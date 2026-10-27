module

public import CFSG.HardMathSupport.Dickson.Bal207.LocalBalRows
public import CFSG.HardMathSupport.Dickson.Bal207.ExcU62
import CFSG.HardMathSupport.Dickson.Bal207.LocalBalU62Diag
import CFSG.HardMathSupport.Dickson.Bal207.LocalBalU62Phi
import CFSG.HardMathSupport.Dickson.Bal207.LocalBalU62TorusA
import CFSG.HardMathSupport.Dickson.Bal207.LocalBalU62Zeta
import CFSG.HardMathSupport.Dickson.Bal207.LocalBalU62ZetaPow

public section

namespace CFSG.HardMathSupport.Dickson.Bal207

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
  CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel

section Model

variable {K : Type} [Field K]

theorem u62lb_isLocallyBalancedAbs_primeForm (h : UnitaryFieldData 2 1 K) :
    IsLocallyBalancedAbs 3 1 (primeFormP h (idGram K 6)) := by
  haveI := excU62_finite h
  have hinj : Function.Injective (MulAut.conj : primeFormP h (idGram K 6) →*
      MulAut (primeFormP h (idGram K 6))) :=
    CFSG.RankThree.PartOne.KCUnitaryRegular.conj_injective_primeFormP h
      (isPrimeFormGram_idGram (n := 6)) (by norm_num) (by omega)
  have hA := u62lb_noNormal_of_phi h fun N hN hN1 hc => u62lb_phi h N hN hN1 hc
  have hB := u62lb_torus_rigid h
  refine isLocallyBalancedAbs_one_of_good Nat.prime_three hinj fun x hx3 hx1 => ?_
  obtain ⟨A, rfl, c, hA3⟩ := excU62_realize h x hx3
  by_cases hc : c = 1
  · subst hc
    have hA1 : (A : GL (Fin 6) K) ^ 3 = 1 := by rw [hA3, map_one]
    exact Or.inr (u62lb_coreFree_of_pow_three h hA hB A (Subtype.ext hA1))
  · exact Or.inl (u62lb_fieldCore_zeta_of_pow h A hA3 hc (u62lb_zeta_pow_nine h A hA3 hc))

theorem u62lb_isLocallyBalancedAbs_primeForm_of_data {ℓ f : ℕ} (hℓ : ℓ = 2) (hf : f = 1)
    (h : UnitaryFieldData ℓ f K) : IsLocallyBalancedAbs 3 1 (primeFormP h (idGram K 6)) := by
  subst hℓ hf
  exact u62lb_isLocallyBalancedAbs_primeForm h

end Model

theorem isLocallyBalancedAbs_three_one_u62 {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedA 5 q).Valid) (hq1 : IsTwoPow q 1) :
    IsLocallyBalancedAbs 3 1 (TauCeti.CFSGIndex.lie ⟨.twistedA 5 q, hv⟩).Group := by
  obtain ⟨⟨hℓ, hfe, hn3, hq'⟩, F, _, _, hF, ⟨eT⟩⟩ :=
    CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 5 q hv (MulEquiv.refl _)
  have h : UnitaryFieldData q.p q.exponent F := ⟨hℓ, hfe, by rw [hF, ← pow_mul, mul_comm]⟩
  obtain ⟨eP⟩ := nonempty_primeFormP_mulEquiv h (isPrimeFormGram_idGram (n := 5 + 1) (K := F))
  exact IsLocallyBalancedAbs.of_mulEquiv
    ((eT.trans (unitaryPSUEquiv h (by omega)).symm).trans eP.symm)
    (u62lb_isLocallyBalancedAbs_primeForm_of_data hq1.1 hq1.2 h)

theorem bal207LocalBalRow_u62 : Bal207LocalBalRow fun p d => p = 3 ∧ IsExcU62 d := by
  rintro p d ⟨rfl, hd⟩
  obtain ⟨q, hv, hq, rfl⟩ := excU62_index hd
  exact isLocallyBalancedAbs_three_one_u62 hv hq

end CFSG.HardMathSupport.Dickson.Bal207

end
