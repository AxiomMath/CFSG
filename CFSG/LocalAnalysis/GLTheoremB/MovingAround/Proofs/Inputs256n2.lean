module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs256n
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs256j2

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256n

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256j
open CFSG.StandardType.RecipeExcLang (inndiagGroup)

set_option linter.unusedSectionVars false

section Residuals

theorem qGen3ExcInndiagF3_holds : Inputs256i.QGen3ExcInndiagF3 := by
  intro τ hτ K _ _ hK3 p hp hp2 hp3 α b j hj hα hp1 hh1
  classical
  have hp5 := hp.five_le_of_ne_two_of_ne_three hp2 hp3
  have hKc : ringChar K = 3 :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ringChar_eq_of_card_eq_pow (n := 1) Nat.prime_three le_rfl
      (by rw [hK3, pow_one])
  have hpK' : ¬ p ∣ Nat.card K := by
    rw [hK3]
    intro h
    exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h)
  have hmon : CFSG.HardMathSupport.Timmesfeld.CrossChar.MonomialToralAt τ p :=
    monomialToralAt_exc monomialToralAt_E6_five monomialToralAt_E7_five
      (by rcases hτ with h | h | h | h | h <;> simp [h]) hp hp2
  have hperf : commutator ↥(adjointGroup τ K) = ⊤ := by
    rcases hτ with h | h | h | h | h
    · subst h
      exact (CFSG.LieType.Steinberg.Adjoint.isPerfect_g2_of_three_le_card K (by omega)).commutator_eq_top
    all_goals exact single_edge_perfect τ K (by simp [h])
  have hh : rootDiagUnit τ b * j ∈ inndiagGroup τ K := ⟨b, j, hj, rfl⟩
  obtain ⟨S, a, ι, -, -, hT, hap, h1, hinj, hrange, hconj⟩ :=
    exists_langSetup_of_inner_untw hτ hp hpK' (Or.inl hp5) hmon hperf α (rootDiagUnit τ b * j)
      (baseChange_mem_adjointGroup_of_mem_inndiag hh) hα hp1 hh1
  exact qGenCoprime_three_of_langSetup S hp hp5 (excRationalLieTypesP_charQ hp hp2) hKc ι hinj hrange α hconj hT
    hap h1 (langSetup_hTame S hT hap h1)

theorem qGen3TwE6InndiagF3_holds : Inputs256i.QGen3TwE6InndiagF3 := by
  intro K _ _ hK σ hσ p hp hp2 hp3 h hp1 hh1
  classical
  have hℓ : (3 : ℕ).Prime := Nat.prime_three
  have hp5 := hp.five_le_of_ne_two_of_ne_three hp2 hp3
  have hmon : CFSG.HardMathSupport.Timmesfeld.CrossChar.MonomialToralAt Tag.E6 p :=
    monomialToralAt_exc monomialToralAt_E6_five monomialToralAt_E7_five (by simp) hp hp2
  obtain ⟨S, a, ι, -, -, hT, hap, h1, hinj, hrange, hconj⟩ :=
    exists_langSetup_of_inndiag_twE6_of_prime hℓ le_rfl hK σ hσ hp hp3 hp hp3 (Or.inl hp5) hmon
      (CFSG.HardMathSupport.Timmesfeld.CrossChar.twistedE6InndiagConj K σ h) (h : ModGL TwistTag.E6.tag K) h.2
      (CFSG.HardMathSupport.Timmesfeld.CrossChar.twistedE6InndiagConj_apply h)
      (by rw [← Subgroup.coe_pow, hp1]; rfl) (fun h' => hh1 (Subtype.ext h'))
  have hKℓ : ringChar K = 3 :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ringChar_eq_of_card_eq_pow (n := 1 * 2) hℓ (by omega)
      (by rw [hK, ← pow_mul])
  exact qGenCoprime_three_of_langSetup S hp hp5 (excRationalLieTypesP_charQ hp hp2) hKℓ ι hinj hrange _ hconj hT
    hap h1 (langSetup_hTame S hT hap h1)

theorem qGen3TriD4InnerF3_holds : Inputs256i.QGen3TriD4InnerF3 := by
  intro q hv hq3 hf p hp hp2 hp3 t ht
  classical
  have hℓ : (3 : ℕ).Prime := Nat.prime_three
  have hp5 := hp.five_le_of_ne_two_of_ne_three hp2 hp3
  obtain ⟨K, _, _, σ, hK, hσ, -, ⟨eK⟩⟩ :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_catEquiv_trialityD4 q hv
  rw [hq3, hf] at hK hσ
  refine Inputs256i.qGenCoprime_of_congr eK _ ?_
  rw [CFSG.ComponentClassification.OuterAutomorphisms.congr_conj]
  have hφ : orderOf (MulAut.conj (eK t)) = p := by
    rw [← CFSG.ComponentClassification.OuterAutomorphisms.congr_conj, Inputs256f.orderOf_congr]
    exact ht
  have hZ : Subgroup.center ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = ⊥ :=
    center_graphFixedRootGroup_eq_bot σ.surjective
  have hxp : eK t ^ p = 1 :=
    mulAut_conj_injective_of_center_eq_bot hZ (by rw [map_pow, ← hφ, pow_orderOf_eq_one, map_one])
  have hx1 : eK t ≠ 1 := fun h' => by
    rw [h', map_one, orderOf_one] at hφ
    exact hp.one_lt.ne' hφ.symm
  have hmon : CFSG.HardMathSupport.Timmesfeld.CrossChar.MonomialToralAt Tag.D4 p :=
    monomialToralAt_exc monomialToralAt_E6_five monomialToralAt_E7_five (by simp) hp hp2
  obtain ⟨S, a, ι, -, -, hT, hap, h1, hinj, hrange, hconj⟩ :=
    exists_langSetup_of_inner_triD4_of_prime hℓ le_rfl hK σ hσ hp hp3 hp hp3 (Or.inl hp5) hmon (eK t) hxp hx1
  have hKℓ : ringChar K = 3 :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ringChar_eq_of_card_eq_pow (n := 1 * 3) hℓ (by omega)
      (by rw [hK, ← pow_mul])
  exact qGenCoprime_three_of_langSetup S hp hp5 (excRationalLieTypesP_charQ hp hp2) hKℓ ι hinj hrange _ hconj hT
    hap h1 (langSetup_hTame S hT hap h1)

end Residuals

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256n

end
