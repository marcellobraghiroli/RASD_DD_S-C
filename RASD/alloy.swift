//
// ENTITIES
//

// User
abstract sig User{}

// Student
sig Student extends User {           
  cv: lone CV,                      // associated CV
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
abstract sig Questionnaire{}

// Questionnaire for the selection process
sig SelectionQuestionnaire extends Questionnaire{
    interview: one Interview        // related interview
}
// Satisfaction questionnaire
abstract sig SatisfactionQuestionnaire extends Questionnaire{}

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
  questionnaires: some MatchingQuestionnaire // associated questionnaires
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
    questionnaires: some InternshipQuestionnaire  // associated questionnaires
    messages: set Message      // messaging session
}

// Message 
sig Message {
  sender: one Student + Company,        // company/student who sent the message
  receiver: one Student + Company,      // company/student who received the message
  activeInternship: one ActiveInternship       // active internship associated to the messaging session
}



//
// VINCOLI
//

// Ensures that the student associated to a CV has actually uploaded that CV, and
// that the company associated to an internship has actually published that internship
fact Ownership {
    (all c: CV | c = c.owner.cv)
    and
    (all i: Internship | i in i.publisher.internships)
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
    all m: Match | 
        (m in m.student.owner.matches)
    and
        (m in m.internship.owner.matches)
}

// Ensures that every match is associated to exactly 2 satisfaction questionnaires 
// (one for the student and one for the company) and that these questionnaires are 
// actually related to that match
fact correspMatchQuest {
    all m: Match | 
        (all q: m.questionnaires | q.match = m)
    and
        (#m.questionnaires = 2)
}

// Ensures that every active internship is associated to exactly 2 satisfaction questionnaires 
// (one for the student and one for the company) and that these questionnaires are 
// actually related to that active internship
fact correspInternshipQuest {
    all a: ActiveInternship | (a = a.questionnaires.internship)
                                and
                                (#a.questionnaires = 2)
}

fact correspMatchActiveInt {
    all a: ActiveInternship | a = a.match.activeInternship
}

// Ensures that an active internships deriving from a match is actually associated
// to that match
fact correspInterviewQuest {
    all q: SelectionQuestionnaire | q = q.interview.questionnaire
}

// Ensures that a message related to an active internship is contaied in the 
// messaging session of that internship
fact correspMexActiveInt {
    all m: Message | m in m.activeInternship.messages
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
