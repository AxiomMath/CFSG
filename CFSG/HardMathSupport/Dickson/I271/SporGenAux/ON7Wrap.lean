module

public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.ON7Extra
public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.ThreeKill

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.Tables.Census CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.RankThree.PartTwo.Sec4

theorem sporPlaneKill_of_sevenModel (hOut : SporadicOuterLeTwo) {s : TauCeti.SporadicName}
    (hnot : ¬ SporadicOnePair s 7) {X : Type} [Group X] [Finite X] (bX : X ≃* Spor s)
    (hD : ∃ (Q : Subgroup X) (z : X) (gens : Set X), SevenModel X 7 Q z gens)
    {C : Type} [Group C] (bC : C ≃* Spor s) (hOff : OffPair s C) : SporPlaneKill s 7 := by
  obtain ⟨Q, z, gens, D⟩ := hD
  intro S _ _ hsimple hnab ⟨e⟩
  have hp : Nat.Prime 7 := by norm_num
  haveI : Fact (Nat.Prime 7) := ⟨hp⟩
  have hcenS : Subgroup.center S = ⊥ := center_eq_bot_of_isSimpleGroup hnab
  have hout : Nat.card (Outer S) ≤ 2 := hOut S hsimple hnab s ⟨e⟩
  refine ⟨autRankLe2_of_offPair hp (by norm_num) hnot hOff (e.trans bC.symm) hcenS hout, ?_⟩
  set f : S ≃* X := e.trans bX.symm with hf
  have hcenX : Subgroup.center X = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have h1 : f.symm x ∈ Subgroup.center S := by
      rw [Subgroup.mem_center_iff]
      intro s'
      apply f.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact Subgroup.mem_center_iff.1 hx (f s')
    rw [hcenS] at h1
    have h2 : f.symm x = 1 := h1
    simpa using congrArg f h2
  have houtX : Nat.card (Outer X) ≤ 2 := by
    rw [← Nat.card_congr (equivalence f).toEquiv]
    exact hout
  refine planeKill_of_noSig_model f ?_ hp
  intro R Y hR hRcard hY hRY
  exact D.noSig (by norm_num) hcenX houtX R hR hRcard Y
    ((Nat.Prime.coprime_iff_not_dvd hp).2 hY) hRY

end CFSG.HardMathSupport.Dickson.I271
