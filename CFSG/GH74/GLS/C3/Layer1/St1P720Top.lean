module

public import CFSG.GH74.GLS.C3.Layer1.St1P720Core
public import CFSG.GH74.GLS.IVK.Proofs2.C3Ivk103Bar

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG.GH74.GLS.C3.Layer1.P720 CFSG.GH74.GLS.C3.Layer1.PumpCalc

theorem bad_of_inU2_not_inC2
    {K : Type} [Group K] (hU : InU2 K) (hN : ¬ InC2 K)
    (hno : ¬ (IsL34Quotient K ∧ CFSG.IsElementaryAbelian 2 ↥(center K) ∧
      Nat.card ↥(center K) ≤ 4)) :
    (HasL2Model K (fun q => Odd q ∧ ¬ IsFM9 q) ∨ Nonempty (K ≃* alternatingGroup (Fin 7))) ∧
      IsSimpleGroup K ∧ ¬ IsL34Quotient K := by
  obtain ⟨hq, hcls⟩ := hU
  have hbad : HasL2Model K (fun q => Odd q ∧ ¬ IsFM9 q) ∨ Nonempty (K ≃* alternatingGroup (Fin 7)) := by
    rcases hcls with hmod | hA7 | hl
    · obtain ⟨p, f, hp, hf, hq', hL⟩ := hmod
      by_cases hfm : IsFM9 (p ^ f)
      · exact absurd (IVK.Proofs2.inC2_of_hasL2Model_fm9 hq ⟨p, f, hp, hf, hfm, hL⟩) hN
      · exact Or.inl ⟨p, f, hp, hf, ⟨hq', hfm⟩, hL⟩
    · exact Or.inr hA7
    · exact absurd hl hno
  have hs : IsSimpleGroup K := by
    rcases hbad with ⟨p, f, hp, hf, hP, hL⟩ | hB
    · exact (CFSG.LieType.Catalog.lieModel_finite_simple _ _ _ _ _ hL).2.2
    · obtain ⟨e⟩ := hB
      have : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
      exact e.isSimpleGroup
  have hcen : center K = ⊥ := center_eq_bot_of_isSimple hs hq
  refine ⟨hbad, hs, fun hl => hno ⟨hl, ?_, ?_⟩⟩
  · rw [hcen]
    exact isElementaryAbelian_bot
  · rw [hcen, Subgroup.card_bot]
    norm_num

end CFSG.GH74.GLS
