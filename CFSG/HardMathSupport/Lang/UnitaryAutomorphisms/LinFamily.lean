module

public import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.LinMain
public import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.LinIrredMatrix
public import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.LinIrredThree
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanFixedThreeReduce

public section

namespace CFSG.HardMathSupport.Lang.UnitaryAutomorphisms

open CFSG.HardMathSupport.Lang.Coordinator CFSG.AGLEmbedding.FixedThree
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.Assembly.LowTwoRank

theorem fixedThreeLinear :
    FixedThreeLinear := by
  intro X _ _ L hL hZ hZ1 n p f hm h3 u hu3 huN hin
  have hperf : Group.IsPerfect L := ⟨hL.2.2.1⟩
  have hβ3 := centerQuotientConj_pow_three L huN hu3
  have hβi := centerQuotientConj_not_mem_inner hperf huN hin
  have h3q : 3 ∣ p ^ f - 1 := (Nat.dvd_gcd_iff.mp h3).2
  have h3n : 3 ∣ n := (Nat.dvd_gcd_iff.mp h3).1
  have hm' := hm
  obtain ⟨⟨hℓ, hf, hn3, hne⟩, K, _, _, hK, ⟨e⟩⟩ := hm
  have : Fact p.Prime := ⟨hℓ⟩
  have hfin : Finite K := inferInstance
  have : Fintype K := Fintype.ofFinite K
  have : CharP K p := charP_of_card_eq_prime_pow (f := f) (by rw [Fintype.card_eq_nat_card, hK])
  have h3K : 3 ∣ Nat.card K - 1 := by rw [hK]; exact h3q
  have hn3' : 3 ≤ n := by obtain ⟨c, rfl⟩ := h3n; omega
  let eP : ↥L ⧸ Subgroup.center ↥L ≃* projectiveSL n K :=
    e.trans ((projectiveSpecialLinearGroupEquivStatedProj n K).symm.trans
      (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL n K))
  set β : MulAut (projectiveSL n K) := (eP.symm.trans (centerQuotientConj L huN)).trans eP
    with hβdef
  have hβeq : β = MulAut.congr eP (centerQuotientConj L huN) := rfl
  have hβ3' : β ^ 3 = 1 := by rw [hβeq, ← map_pow, hβ3, map_one]
  have hβi' : β ∉ inner (projectiveSL n K) := by
    intro hmem
    apply hβi
    obtain ⟨c, hc⟩ := hmem
    refine ⟨eP.symm c, ?_⟩
    ext x
    have := DFunLike.congr_fun hc (eP x)
    simp only [MulAut.conj_apply, hβdef, MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at this
    apply eP.injective
    simp only [MulAut.conj_apply, map_mul, map_inv, MulEquiv.apply_symm_apply]
    exact this
  rcases hasFixedThreePair_or_irred_lin hK hf h3K hn3' h3n β hβ3' hβi' with
    ⟨x, y, hx, hy, ox, oy, oxy⟩ | ⟨hn, B, hβB, l, hB3, hl⟩
  · have hrich : ThreePrimeFixedRich β := ThreePrimeFixedRich.of_pair hx hy ox oy oxy
    have hr := hrich.map_equiv eP.symm
    have hback : ((eP.symm.symm.trans β).trans eP.symm) = centerQuotientConj L huN := by
      ext z
      simp [hβdef]
    rw [hback] at hr
    exact fixedThreeConclusion_of_rich hZ huN hr
  · right
    subst hn
    obtain ⟨ω, H, hω3, hω1, hH3, hBH⟩ := exists_lin_irred_element h3K B hB3 hl
    refine exists_lin_irred_alternative hK h3K L hL.2.2.1 hZ hZ1 hm' eP huN B ?_ ω H hω3 hω1 hH3
      hBH
    intro z
    have := DFunLike.congr_fun hβB (eP z)
    simp only [hβdef, MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at this
    exact this

end CFSG.HardMathSupport.Lang.UnitaryAutomorphisms
