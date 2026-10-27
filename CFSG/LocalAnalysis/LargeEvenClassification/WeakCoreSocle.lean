module

public import CFSG.Open.LocalVocabulary

public section

open CFSG.Open

namespace CFSG.LargeEvenClassification.Helpers

universe groupUniverse

@[expose] def minimalNormalEligible {Ambient : Type groupUniverse} [Group Ambient]
    (Normal : Subgroup Ambient) : Prop :=
  Minimal (fun Candidate : Subgroup Ambient => Candidate.Normal ∧ Candidate ≠ ⊥) Normal

@[expose] noncomputable def finiteSocle (Ambient : Type groupUniverse) [Group Ambient] : Subgroup Ambient :=
  ⨆ Candidate : {Normal : Subgroup Ambient // minimalNormalEligible Normal}, Candidate.val

instance finiteSocle_normal (Ambient : Type groupUniverse) [Group Ambient] :
    (finiteSocle Ambient).Normal := by
  let _ : ∀ Candidate : {Normal : Subgroup Ambient // minimalNormalEligible Normal},
      Candidate.val.Normal := fun Candidate => Candidate.property.prop.1
  exact Subgroup.iSup_normal _

theorem minimal_normal_le_socle {Ambient : Type groupUniverse} [Group Ambient]
    (Normal : Subgroup Ambient) (hminimal : minimalNormalEligible Normal) :
    Normal ≤ finiteSocle Ambient := le_iSup_of_le ⟨Normal, hminimal⟩ le_rfl

theorem finite_minimal_normal_inside {Ambient : Type groupUniverse} [Group Ambient] [Finite Ambient]
    (Normal : Subgroup Ambient) (hnormal : Normal.Normal) (hnonzero : Normal ≠ ⊥) :
    ∃ MinimalNormal : Subgroup Ambient, MinimalNormal ≤ Normal ∧ minimalNormalEligible MinimalNormal :=
  Finite.exists_le_minimal (p := fun Candidate : Subgroup Ambient => Candidate.Normal ∧ Candidate ≠ ⊥)
    ⟨hnormal, hnonzero⟩

end CFSG.LargeEvenClassification.Helpers
