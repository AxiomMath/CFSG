module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5CenterHyp
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5CenterOdd

public noncomputable section

open CFSG.Open

namespace CFSG.ComponentClassification.AschbacherTheorem5

open CenterQuotient

theorem conclusion_of_center_quotient {G : Type} [Group G] [Finite G] {D : Subgroup G} {r : ℕ}
    {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)} (hyp : Hyp61 G D r Abar)
    (hH : Subgroup.normalizer (D : Set G) ≠ ⊤)
    (hquot : Conclusion (G ⧸ Subgroup.center G) (quotientSubgroup D) r
      (quotientFactors D Abar)) :
    Conclusion G D r Abar := by
  rcases hquot with hone | ⟨htwo, hfactors⟩
  · exact Or.inl hone
  right
  refine ⟨htwo, fun i j hij => ?_⟩
  subst htwo
  obtain ⟨-, hranki, hclause⟩ := hfactors i j hij
  obtain ⟨-, hrankj, -⟩ := hfactors j i hij.symm
  have hoddi := center_inf_factor_odd hyp i hranki.le
  have hoddj := center_inf_factor_odd hyp j hrankj.le
  refine ⟨canonical_two_factor_product D Abar hyp.hcomm hyp.hgen i j hij, ?_, ?_⟩
  · rw [pRank_eq_of_center_inf_odd _ hoddi, ← preimage_center_quotient, ← quotientFactors_apply]
    exact hranki
  intro a₁ ha₁ a₂ ha₂ horder₁ horder₂ hcommute hcentral₁ hcentral₂
  by_contra hfail
  obtain ⟨-, hnoncentral⟩ := not_or.mp hfail
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnotcenter : ∀ (k : Fin 2) (a : G), a ∈ aschbacherThm5Preimage D (Abar k) →
      orderOf a = 2 →
      Odd (Nat.card (Subgroup.center G ⊓ aschbacherThm5Preimage D (Abar k) : Subgroup G)) →
      a ∉ Subgroup.center G := by
    intro k a ha horder hodd hcenter
    have hdvd := Subgroup.orderOf_dvd_natCard _ (Subgroup.mem_inf.mpr ⟨hcenter, ha⟩)
    rw [horder] at hdvd
    exact hodd.not_two_dvd_nat hdvd
  have himage : ∀ a : G, orderOf a = 2 → a ∉ Subgroup.center G →
      orderOf (QuotientGroup.mk' (Subgroup.center G) a) = 2 := by
    intro a horder hcenter
    apply orderOf_eq_prime
    · rw [← map_pow, ← horder, pow_orderOf_eq_one, map_one]
    · intro hone
      exact hcenter ((QuotientGroup.eq_one_iff a).mp hone)
  have hmem : ∀ (k : Fin 2) (a : G), a ∈ aschbacherThm5Preimage D (Abar k) →
      QuotientGroup.mk' (Subgroup.center G) a ∈
        aschbacherThm5Preimage (quotientSubgroup D) (quotientFactors D Abar k) := by
    intro k a ha
    rw [quotientFactors_apply, preimage_center_quotient]
    exact Subgroup.mem_map_of_mem _ ha
  have hcentralizes : ∀ (k : Fin 2) (a : G), aschbacherThm5Centralizes (aschbacherThm5Core D)
      (aschbacherThm5Preimage D (Abar k)) a →
      aschbacherThm5Centralizes (aschbacherThm5Core (quotientSubgroup D))
        (aschbacherThm5Preimage (quotientSubgroup D) (quotientFactors D Abar k))
        (QuotientGroup.mk' (Subgroup.center G) a) := by
    intro k a ha
    rw [quotientFactors_apply, preimage_center_quotient, core_center_quotient]
    exact centralizes_map _ ha
  have hcentral : QuotientGroup.mk' (Subgroup.center G) (a₁ * a₂) ∈
      Subgroup.center (G ⧸ Subgroup.center G) := by
    rcases hclause _ (hmem i a₁ ha₁) _ (hmem j a₂ ha₂)
        (himage a₁ horder₁ (hnotcenter i a₁ ha₁ horder₁ hoddi))
        (himage a₂ horder₂ (hnotcenter j a₂ ha₂ horder₂ hoddj))
        (by rw [← map_mul, ← map_mul, hcommute])
        (hcentralizes i a₁ hcentral₁) (hcentralizes j a₂ hcentral₂) with heq | hcenter
    · have hsquare : QuotientGroup.mk' (Subgroup.center G) a₁ *
          QuotientGroup.mk' (Subgroup.center G) a₂ = 1 := by
        rw [← heq, ← pow_two, ← himage a₁ horder₁ (hnotcenter i a₁ ha₁ horder₁ hoddi),
          pow_orderOf_eq_one]
      rw [map_mul, hsquare]
      exact Subgroup.one_mem _
    · rwa [map_mul]
  have hsquare₁ : a₁ ^ 2 = 1 := by rw [← horder₁]; exact pow_orderOf_eq_one a₁
  have hsquare₂ : a₂ ^ 2 = 1 := by rw [← horder₂]; exact pow_orderOf_eq_one a₂
  have hpower : (a₁ * a₂) ^ (2 ^ 1) = 1 := by
    rw [pow_one, Commute.mul_pow hcommute, hsquare₁, hsquare₂, one_mul]
  have hcentralizesi : aschbacherThm5Centralizes (aschbacherThm5Core D)
      (aschbacherThm5Preimage D (Abar i)) (a₁ * a₂) := by
    have hd₁ : a₁ ∈ D := preimage_le D _ ha₁
    have hd₂ : a₂ ∈ D := preimage_le D _ ha₂
    have h₁ := (centralizes_iff_quotient_commutes D (Abar i) ⟨a₁, hd₁⟩).mp hcentral₁
    have h₂ := (centralizes_iff_quotient_commutes D (Abar i) ⟨a₂, hd₂⟩).mp
      (cross_factor_centralizes D Abar hyp.hcomm i j hij a₂ ha₂)
    apply (centralizes_iff_quotient_commutes D (Abar i) (⟨a₁, hd₁⟩ * ⟨a₂, hd₂⟩)).mpr
    intro x hx
    rw [map_mul, mul_assoc, h₂ x hx, ← mul_assoc, h₁ x hx, mul_assoc]
  apply hH
  rw [eq_top_iff]
  intro g _
  exact hyp.hi i i (a₁ * a₂) g ⟨1, hpower⟩ hnoncentral hcentralizesi
    (conj_centralizes_of_central_image hcentralizesi hcentral g)

theorem reduction_to_trivial_center
    (hfree : ∀ (G : Type) [Group G] [Finite G] (D : Subgroup G) (r : ℕ)
      (Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)), ¬ Counterexample G D r Abar) :
    ∀ (G : Type) [Group G] [Finite G] (D : Subgroup G) (r : ℕ)
      (Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)),
      Hyp61 G D r Abar → Subgroup.normalizer (D : Set G) ≠ ⊤ → Conclusion G D r Abar := by
  suffices h : ∀ (n : ℕ) (G : Type) [Group G] [Finite G], Nat.card G = n →
      ∀ (D : Subgroup G) (r : ℕ) (Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)),
      Hyp61 G D r Abar → Subgroup.normalizer (D : Set G) ≠ ⊤ → Conclusion G D r Abar from
    fun G _ _ D r Abar => h _ G rfl D r Abar
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro G _ _ hcard D r Abar hyp hH
    by_cases hcenter : Subgroup.center G = ⊥
    · by_contra hfail
      exact hfree G D r Abar ⟨hyp, hH, hcenter, hfail⟩
    · have hlt : Nat.card (G ⧸ Subgroup.center G) < n := by
        rw [← hcard, Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center G)]
        exact lt_mul_of_one_lt_right Nat.card_pos
          ((Subgroup.one_lt_card_iff_ne_bot _).mpr hcenter)
      exact conclusion_of_center_quotient hyp hH
        (ih _ hlt (G ⧸ Subgroup.center G) rfl (quotientSubgroup D) r (quotientFactors D Abar)
          (hyp61_center_quotient hyp) (normalizer_center_quotient_ne_top hyp hH))

end CFSG.ComponentClassification.AschbacherTheorem5
