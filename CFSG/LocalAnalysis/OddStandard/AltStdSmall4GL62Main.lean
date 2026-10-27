module

public import Certificates.Certificate36405

public section

namespace CFSG.OddStandard.AltStdSmall4.GL62


theorem gl62OvergroupsEq_holds : GL62OvergroupsEq :=
  Certificates.certificate36405

theorem gl62Overgroups_holds : GL62Overgroups := by
  intro X hB hC
  rcases gl62OvergroupsEq_holds X hB hC with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

end CFSG.OddStandard.AltStdSmall4.GL62
