module

public import CFSG.LocalAnalysis.ComponentClassification.RestrictedStdEven
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTIUnitarySocle
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrSuzukiSocle
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrLargeReeTitsSocle
public import CFSG.GH74.Exceptional.UnitaryFourTwo
public import CFSG.CharacterTheory.Semidihedral.CoreFreeDihedral

public section

namespace CFSG.ComponentClassification.RestrictedStd

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.GSThmB

variable {A : Type} [Group A] [Finite A] {W : Subgroup A} [W.Normal]
  (hWs : IsSimpleGroup W) (hWnab : ∃ x y : W, x * y ≠ y * x)
  (hCW : centralizer (W : Set A) = ⊥) {a : A} (ha : orderOf a = 2) {L : Subgroup A}
  (hLW : L ≤ W) (hL : Assembly.IsComponentOf L (centralizer ({a} : Set A)))

include hWs hWnab hCW ha hLW hL

theorem gsRestricted_even_psu (hs : SmallSource L) {n e : ℕ} (hm : LieModel W .PSU n 2 e) :
    GSRestricted W := by
  obtain ⟨p, f, hp, hp2, hf, hsrc⟩ := exists_selector_source hs
  obtain ⟨⟨-, he, hn, hne⟩, K, _, _, hK, ⟨φ⟩⟩ := statedClassicalModel_of_lieModel (by decide) hm
  have hUd : LocalAnalysis.ComponentInitial.UnitaryFieldData 2 e K :=
    ⟨Nat.prime_two, he, by rw [hK, ← pow_mul, mul_comm]⟩
  have hq : ¬ (n = 3 ∧ 2 ^ e = 2) := fun ⟨h3, h2⟩ => hne (by rw [h3, h2])
  obtain ⟨ρ₀, -, -, -, -, H₀, C, hC, -, θ₀, -, ρC, -, -, σ, -, -, Cl, hCl, -, -, -, -, -, -, -,
    -, hrows, -⟩ :=
    OutcomeLocal.faithful_even_unitary_socle_small_source_involution_selector hWs hWnab hCW ha
      hLW hL hp hp2 hf hsrc hUd hn hq
      (φ.trans (ClassicalGroups.UnitaryFlag.unitaryPSUEquiv hUd (by omega)).symm)
  rcases hrows with ⟨hn3, he2, -⟩ | ⟨hn4, he1, -⟩ | ⟨hn5, he1, -⟩
  · subst hn3 he2
    exact gsRestricted_psu_three_four hm
  · subst hn4 he1
    exact gsRestricted_odd_family Nat.prime_three (by decide) le_rfl
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        (GH74.Exceptional.lieModel_PSp_two_three_of_lieModel_PSU_four_two hm)))))))
  · subst hn5 he1
    exact gsRestricted_psu_five_two hm

theorem not_lieModel_twistedB2 {n p f : ℕ} (hm : LieModel W .twistedB2 n p f) : False := by
  rcases hm with ⟨ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, -, hsz⟩
  · simp [classicalTags] at ht
  · simp [chevalleyExceptionalTags] at ht
  · simp [reeTitsTags] at ht
  · exact UnbalancedCorr.faithful_suzuki_socle_involution_component_exclusion hWs hWnab hCW ha
      hLW hL p f hsz

theorem not_lieModel_large_ree_tits {t : StatedLieTag} (ht : t = .twistedF4 ∨ t = .Tits)
    {n p f : ℕ} (hm : LieModel W t n p f) : False := by
  have hmod : ReeTitsModel W t p f := by
    rcases hm with ⟨htc, -⟩ | ⟨-, htc, -⟩ | ⟨-, -, h⟩ | ⟨-, htc, -⟩
    · rcases ht with rfl | rfl <;> simp [classicalTags] at htc
    · rcases ht with rfl | rfl <;> simp [chevalleyExceptionalTags] at htc
    · exact h
    · rcases ht with rfl | rfl <;> cases htc
  have : IsSimpleGroup W := hWs
  have hF := Semidihedral.CoreFreeDihedral.generalizedFitting_eq_of_normal_simple_centralizer_eq_bot
    W hWnab hCW
  obtain ⟨-, hno, -⟩ :=
    UnbalancedCorr.simple_generalized_fitting_large_Ree_Tits_involution_centralizers_component_free
      hF hWs hWnab ha ht hmod
  exact hno L hL

end CFSG.ComponentClassification.RestrictedStd
