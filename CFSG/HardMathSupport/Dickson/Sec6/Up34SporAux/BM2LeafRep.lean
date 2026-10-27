module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34SporAux.BMLeaves
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23Fuse

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.BM

open CFSG.Blueprint CFSG.Monster.GMS CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23

section Rep


theorem b3BLeaf_of_rep
    (h : ¬ 7 ∣ Nat.card (Subgroup.centralizer ({phiB (t3 1)} : Set NativeSporadic.B))) :
    B3BLeaf := by
  intro x hx hunv
  obtain ⟨i, hi⟩ := bThree_classes x hx
  have hnot0 : ¬ IsConj x (phiB (t3 0)) := by
    intro hc
    obtain ⟨d, hd, hdr⟩ := phiB_t3_zero_inverted
    obtain ⟨c, hcx⟩ := isConj_iff.1 hc
    refine hunv (c⁻¹ * d * c) (BabyInv.of_isConj hd (isConj_iff.2 ⟨c⁻¹, by simp⟩)) ?_
    have hx' : x = c⁻¹ * phiB (t3 0) * c := by rw [← hcx]; group
    calc c⁻¹ * d * c * x * (c⁻¹ * d * c)⁻¹
        = c⁻¹ * (d * phiB (t3 0) * d⁻¹) * c := by rw [hx']; group
      _ = x⁻¹ := by rw [hdr, hx']; group
  have hcard : ∀ y : NativeSporadic.B, IsConj x y →
      Nat.card (Subgroup.centralizer ({x} : Set NativeSporadic.B)) =
        Nat.card (Subgroup.centralizer ({y} : Set NativeSporadic.B)) := by
    intro y hxy
    obtain ⟨c, hc⟩ := isConj_iff.1 hxy
    have := natCard_centralizer_mulEquiv (MulAut.conj c) x
    rw [MulAut.conj_apply, hc] at this
    exact this.symm
  fin_cases i
  · exact absurd hi hnot0
  · rw [hcard _ hi]
    exact h
  · exact absurd (hi.trans bThreeRc_holds) hnot0
  · rw [hcard _ (hi.trans bThreeRd_holds)]
    exact h

end Rep

end CFSG.HardMathSupport.Dickson.Sec6.BM
