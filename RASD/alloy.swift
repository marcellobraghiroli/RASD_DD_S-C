open util / boolean

// User
abstract sig User{}

// Student
sig Student extends User {           
  cv: one CV,                      // associated CV
  selectedInternships: set Internship,  // selected internships
  interestedCompanys: set Internship,
  matches: set Match,        // completed matches
}

// Company
sig Company extends User {           
  internships: set Internship,      // published internships
  selectedCVs: Internship -> set CV,     // selected CVs for each internship
  interestedStudents: Internship -> set CV,
  matches: set Match            // completed matches
}

// Student CV
sig CV {
  owner: one Student                // CV's owner
}

// Internship
sig Internship {
  publisher: one Company        // Internship's publisher
}

// Questionnaire
abstract sig Questionnaire{
    var compiled: one Bool
}

// Questionnaire for the selection process
sig SelectionQuestionnaire extends Questionnaire{
    var grade: one Int,
    interview: one Interview        // related interview
}  {grade >= 0 and grade <= 10}

// Satisfaction questionnaire
abstract sig SatisfactionQuestionnaire extends Questionnaire{
    var evaluation: one Bool
}

// Satisfaction questionnaire for matchmaking process
sig MatchingQuestionnaire extends SatisfactionQuestionnaire{
    match: one Match            // related match
}

// Satisfaction questionnaire for activated internship
sig InternshipQuestionnaire extends SatisfactionQuestionnaire{
    internship: one ActiveInternship        // related active internship
}

// Completed match
sig Match {
  student: one CV,          // matching CV
  internship: one Internship,       // matching internship
  questionnaires: some MatchingQuestionnaire, // associated questionnaires
  activeInternship: lone ActiveInternship  // activated internship
}

// Interview
sig Interview {
    match: one Match,       // related match
    questionnaire: one SelectionQuestionnaire   // questionnaire for selection process
}

// Active internship
sig ActiveInternship {
    match: one Match,       // related match
    questionnaires: some InternshipQuestionnaire,  // associated questionnaires
    messages: set Message      // messaging session
}

// Message 
sig Message {
  sender: one Student + Company,        // company/student who sent the message
  receiver: one Student + Company,      // company/student who received the message
  activeInternship: one ActiveInternship       // active internship associated to the messaging session
}









// Ensures that the student associated to a CV has actually uploaded that CV, and
// that the company associated to an internship has actually published that internship
fact Ownership {
    (all c: CV, s: Student | 
        c = s.cv iff s = c.owner)
    and
    (all i: Internship, c: Company |
        i in c.internships iff c = i.publisher)
}

// Ensures that if an internship is in the "interestedCompanys" list of a student, their
// CV must be in the "selectedCVs" list of the corresponding company for that internship
fact InterestedCompanyImpliesSelectedCV {
    all s: Student, i: Internship | 
        i in s.interestedCompanys iff s.cv in i.publisher.selectedCVs[i]
}

// Ensures that if a student CV is in the "interestedStudents" list of a company for a 
// specific internship, the internship must be in the "selectedInternships" list
// of the corresponding student
fact InterestedStudentImpliesSelectedInternship {
    all co: Company, c: CV, i: Internship |
        c in co.interestedStudents[i] iff i in c.owner.selectedInternships
}

// Ensures that the student and company involved in a match have actually that match
// in their completed matches list
fact CorrespMatchUsers {
    (all m: Match, s: Student | 
        m in s.matches iff s = m.student.owner)
    and
    (all m: Match, c: Company |
        m in c.matches iff c = m.internship.publisher)
}

// Ensures that there cannot be two matches associated to the same pair 
// CV-internship
fact NoDuplicatedMatches {
	all m1, m2: Match | 
		(m1.student = m2.student and m1.internship = m2.internship)
		implies m1 = m2
}

// Ensures that every match is associated to exactly 2 satisfaction questionnaires 
// (one for the student and one for the company) and that these questionnaires are 
// actually related to that match
fact correspMatchQuest {
    all m: Match, q: MatchingQuestionnaire |
        (q in m.questionnaires iff q.match = m)
        and
        (#m.questionnaires = 2)

}

// Ensures that every active internship is associated to exactly 2 satisfaction questionnaires 
// (one for the student and one for the company) and that these questionnaires are 
// actually related to that active internship
fact correspInternshipQuest {
    all a: ActiveInternship, q: InternshipQuestionnaire |
        (q in a.questionnaires iff q.internship = a)
        and
        (#a.questionnaires = 2)
}

// Ensures that an active internships deriving from a match is actually associated
// to that match
fact correspMatchActiveInt {
    all a: ActiveInternship, m: Match |
        a = m.activeInternship iff m = a.match
}

// Ensures that a selecetion process questionaire is associated to the correct 
// interview
fact correspInterviewQuest {
    all q: SelectionQuestionnaire, i: Interview |
        q = i.questionnaire iff i = q.interview
}

// Ensurere that for each match only one interview can be set up
fact NoMultipleInterviews {
    all i1, i2: Interview |
        (i1.match = i2.match) implies (i1 = i2)
}

// Ensures that a message related to an active internship is contaied in the 
// messaging session of that internship
fact correspMexActiveInt { 
    all m: Message, a: ActiveInternship |
        m in a.messages iff m.activeInternship = a
}

// Ensures that a message is sent by a student and received by a company (or viceversa),
// and that the 2 parties are actually involved in the related active internship
fact MexConsistency {
    all m: Message | ((m.sender = m.activeInternship.match.student.owner) and
                    (m.receiver = m.activeInternship.match.internship.publisher))
                    or 
                    ((m.sender = m.activeInternship.match.internship.publisher) and
                    (m.receiver = m.activeInternship.match.student.owner))
}

// Ensures that if a satisfaction questionnaire has not been compiled, then it doesn't contribute to the 
// recommendation process.
// Instead, once the questionnaire has been compiled, the evaluation must never
// change.
fact EvaluationConsistency {
        all q: SatisfactionQuestionnaire |
            always(q.compiled = False implies q.evaluation = False)
	     and
	     always (q.compiled = True implies always q.evaluation = q.evaluation')
}

// Ensures that if a selection process questionnaire has not been compiled, the related match will
// be at the bottom of the suitability rank of the corresponding company, because no grade has been
// established yet.
// Instead, once the questionnaire has been compiled, the grade must
// never change.
fact GradeConsistency {
        all q: SelectionQuestionnaire |
            always (q.compiled = False implies q.grade = 0)
            and
            always (q.compiled = True implies always q.grade = q.grade')
}

// Ensures that once a questionnaire has been compiled, it can never be compilabe again
fact CompilationConsistency {
    all q: Questionnaire |
        always(q.compiled = True implies after always q.compiled = True)
}

