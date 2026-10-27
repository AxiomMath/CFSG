module

public import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.UnitaryMain
public import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.IrredMatrix
public import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.IrredThree
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanFixedThreeReduce

public section

namespace CFSG.HardMathSupport.Lang.UnitaryAutomorphisms

open CFSG.HardMathSupport.Lang.Coordinator CFSG.AGLEmbedding.FixedThree
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank

theorem fixedThreeUnitary :
    FixedThreeUnitary := by
  intro X _ _ L hL hZ hZ1 n p f hm h3 u hu3 huN hin
  have hperf : Group.IsPerfect L := ⟨hL.2.2.1⟩
  have hβ3 := centerQuotientConj_pow_three L huN hu3
  have hβi := centerQuotientConj_not_mem_inner hperf huN hin
  have h3q : 3 ∣ p ^ f + 1 := (Nat.dvd_gcd_iff.mp h3).2
  have h3n : 3 ∣ n := (Nat.dvd_gcd_iff.mp h3).1
  obtain ⟨⟨hℓ, hf, hn3, hne⟩, K, _, _, hK, ⟨e⟩⟩ := hm
  have hU : UnitaryFieldData p f K := ⟨hℓ, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have hq : ¬(n = 3 ∧ p ^ f = 2) := fun ⟨h1, h2⟩ => hne (by rw [h1, h2])
  let eU : ↥L ⧸ Subgroup.center ↥L ≃* unitaryPSU hU n :=
    e.trans (unitaryPSUEquiv hU (by omega)).symm
  let eP := eU.trans (CFSG.LocalAnalysis.unitaryPSUEquivPrimeFormOne hU n)
  set β : MulAut (primeFormP hU ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :=
    (eP.symm.trans (centerQuotientConj L huN)).trans eP with hβdef
  have hβeq : β = MulAut.congr eP (centerQuotientConj L huN) := rfl
  have hβ3' : β ^ 3 = 1 := by rw [hβeq, ← map_pow, hβ3, map_one]
  have hβi' : β ∉ inner (primeFormP hU ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
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
  have hfin : Finite K := hU.finite
  have : Finite (primeFormP hU ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := inferInstance
  rcases hasFixedThreePair_or_irred hU h3q hn3 h3n hq β hβ3' hβi' with
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
    obtain ⟨ω, H, hω3, hω1, hωn, hH3, hBH⟩ := exists_irred_element hU h3q B hB3 hl
    have hq2 : 2 < p ^ f := by
      have h2 : 2 ≤ p ^ f := le_trans hℓ.two_le (Nat.le_self_pow (by omega) p)
      rcases h2.lt_or_eq with h | h
      · exact h
      · exact absurd ⟨rfl, h.symm⟩ hq
    refine exists_irred_alternative hU hq2 L hL.2.2.1 hZ1 eU huN B ?_ ω H hω3 hω1 hωn hH3 hBH
    intro z
    have := DFunLike.congr_fun hβB (eP z)
    simp only [hβdef, MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at this
    exact this

end CFSG.HardMathSupport.Lang.UnitaryAutomorphisms
