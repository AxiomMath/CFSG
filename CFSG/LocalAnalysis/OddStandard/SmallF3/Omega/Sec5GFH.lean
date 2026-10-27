module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5GDefs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Classification

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

theorem sec5g_caseII_field {X : Type} [Group X] {A : Subgroup X} (h : Sec5GCaseII A) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), 5 ≤ Nat.card F ∧
      (Nat.card F % 8 = 3 ∨ Nat.card F % 8 = 5) ∧
      Nonempty (Sec5GBar A ≃* CFSG.GorensteinWalter.PSL2 F) ∧
      ∃ P : Sylow 2 (Sec5GBar A), (P : Subgroup (Sec5GBar A)) = Sec5GImg A := by
  obtain ⟨⟨p, f, hp, -, hf, h5, h8, ⟨e⟩⟩, hP⟩ := h
  have hc : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f hf.ne'
  refine ⟨GaloisField p f, inferInstance, inferInstance, ?_, ?_, ⟨e⟩, hP⟩
  · rw [hc]
    exact h5
  · rw [hc]
    exact h8

end CFSG.OddStandard.SmallF3.Omega
