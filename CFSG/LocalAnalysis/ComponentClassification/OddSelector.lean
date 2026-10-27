module

public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorRowO
public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorGraphField

public noncomputable section

namespace CFSG.ComponentClassification.OddSelector

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.OutcomeLocal

theorem center_projectiveSL_two_eq_bot {E : Type} [Field E] [Finite E] (hE : 4 ≤ Nat.card E) :
    center (projectiveSL 2 E) = ⊥ := by
  classical
  have : Fintype E := Fintype.ofFinite E
  have hs : ∃ s : Finset E, s.card = 4 := by
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset E)) (n := 4)
      (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact hE)
    exact ⟨s, hs⟩
  have := (CFSG.LinearGroups.linear_projective_simple (K := E) (n := 2) le_rfl (Or.inr hs)).2.1
  have : IsSimpleGroup (projectiveSL 2 E) :=
    (LinearCover.projectiveSpecialLinearEquivProjectiveSL 2 E).symm.isSimpleGroup
  have : Group.IsPerfect (SpecialLinearGroup (Fin 2) E) :=
    CatalogueBGeneralLinear.specialLinear_perfect 2 E le_rfl (Or.inr (by omega))
      (Or.inr (by omega))
  have : Group.IsPerfect (projectiveSL 2 E) := Group.IsPerfect.ofSurjective (proj_surjective 2 E)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center (projectiveSL 2 E)) with h | h
  · exact h
  · exfalso
    have hcomm : ∀ a b : projectiveSL 2 E, a * b = b * a := fun a b =>
      mem_center_iff.mp (h ▸ mem_top b) a
    exact Group.IsPerfect.not_isSolvable _ (Group.isSolvable_of_comm hcomm)

theorem statedClassicalModel_of_mulEquiv_projectiveSL_two {L : Type} [Group L] {E : Type}
    [Field E] [Finite E] {ℓ e : ℕ} (hℓ : ℓ.Prime) (he : 1 ≤ e) (hE : Nat.card E = ℓ ^ e)
    (h4 : 4 ≤ ℓ ^ e) (φ : L ≃* projectiveSL 2 E) :
    StatedClassicalModel (L ⧸ center L) .PSL 2 ℓ e := by
  have hZ : center L = ⊥ := by
    have h1 := Subgroup.map_center_eq φ
    rw [center_projectiveSL_two_eq_bot (by omega)] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ φ.injective).mp h1
  have eQ : L ⧸ center L ≃* StatedProj (StatedSL 2 E) :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans (QuotientGroup.quotientBot.trans
      (φ.trans ((LinearCover.projectiveSpecialLinearEquivProjectiveSL 2 E).symm.trans
        (projectiveSpecialLinearGroupEquivStatedProj 2 E))))
  exact SectionRank.statedClassicalModel_of_mulEquiv eQ
    (statedClassicalModel_psl_two hℓ he hE (by omega) (by omega))

theorem source_parameters {X : Type} [Group X] {ℓ g p f : ℕ} (hℓ2 : ℓ ≠ 2)
    (hX : StatedClassicalModel X .PSL 2 ℓ g) (hp2 : p ≠ 2)
    (hsrc : StatedClassicalModel X .PSL 2 p f ∨ Nonempty (X ≃* alternatingGroup (Fin 7)) ∨
      StatedClassicalModel X .PSL 3 2 2) :
    p = ℓ ∧ f = g ∧ StatedClassicalModel X .PSL 2 p f := by
  obtain ⟨hpar, h7, h34⟩ :=
    UnbalancingLocal.small_standard_source_projective_linear_two_field_parameters_stated hX
  rcases hsrc with h | h | h
  · rcases hpar p f hp2 h with ⟨⟨-, hlp, hgf⟩, -⟩ | ⟨⟨hl2, -⟩, -⟩
    · exact ⟨hlp.symm, hgf.symm, h⟩
    · exact absurd hl2 hℓ2
  · exact absurd h (not_nonempty_iff.mpr h7)
  · exact absurd h h34

theorem not_selectorRowS_and_selectorRowO {A : Type} [Group A] {m : ℕ} {k : Type} [Field k]
    [Finite k] (hm : 3 ≤ m) {ρ : A →* MulAut (projectiveSL m k)} {W : Subgroup A} {a : A}
    {L : Subgroup A} : ¬ (SelectorRowS m k ρ W a L ∧ SelectorRowO m k ρ W a L) := by
  rintro ⟨⟨ν, -, Ψ, C, -, hS, -⟩, ⟨δ, -, ψ, R, C', -, -, hO, -⟩⟩
  apply ProjectivePlane.dualAut_not_mem_semilinearAutGroup (K := k) hm
  have h2 := hO.symm.trans hS
  have h1 : conjAut m k R⁻¹ * dualAut m k =
      conjAut m k (C'⁻¹ * C * rowSU ν Ψ * C⁻¹ * C') := by
    calc conjAut m k R⁻¹ * dualAut m k =
          (conjAut m k C')⁻¹ * (conjAut m k C' * (conjAut m k R⁻¹ * dualAut m k) *
            (conjAut m k C')⁻¹) * conjAut m k C' := by group
      _ = (conjAut m k C')⁻¹ * (conjAut m k C * conjAut m k (rowSU ν Ψ) *
            (conjAut m k C)⁻¹) * conjAut m k C' := by rw [h2]
      _ = _ := by simp only [map_mul, map_inv]; group
  have hδ : dualAut m k = (conjAut m k R⁻¹)⁻¹ *
      conjAut m k (C'⁻¹ * C * rowSU ν Ψ * C⁻¹ * C') := by
    rw [← h1, inv_mul_cancel_left]
  rw [hδ]
  refine mul_mem (inv_mem (mem_semilinearAutGroup_iff.mpr ⟨R⁻¹, 1, by rw [map_one, mul_one]⟩))
    (mem_semilinearAutGroup_iff.mpr ⟨C'⁻¹ * C * rowSU ν Ψ * C⁻¹ * C', 1,
      by rw [map_one, mul_one]⟩)

theorem faithful_odd_higher_linear_socle_selector_core
    {A : Type} [Group A] [Finite A] {W : Subgroup A} [W.Normal]
    (_hWsimple : IsSimpleGroup W) (_hWnonab : ∃ x y : W, x * y ≠ y * x)
    (hCW : centralizer (W : Set A) = ⊥) {a : A} (ha : orderOf a = 2) {L : Subgroup A}
    (hLW : L ≤ W) (hL : CFSG.Assembly.IsComponentOf L (centralizer ({a} : Set A)))
    (hstd : IsStandardSubgroup L) {p f : ℕ} (hp2 : p ≠ 2)
    (hsrc : StatedClassicalModel (L ⧸ center L) .PSL 2 p f ∨
      Nonempty (L ⧸ center L ≃* alternatingGroup (Fin 7)) ∨
      StatedClassicalModel (L ⧸ center L) .PSL 3 2 2)
    (hrank : StatedClassicalModel (L ⧸ center L) .PSL 2 p f →
      2 ≤ CFSG.pRank 2 L ∨ Odd (Nat.card (center L)))
    {m ℓ e : ℕ} (hm : 4 ≤ m) (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (he : 1 ≤ e) {k : Type} [Field k]
    (hk : Nat.card k = ℓ ^ e) (φ : W ≃* projectiveSL m k) :
    ∃ ρ : A →* MulAut (projectiveSL m k), Function.Injective ρ ∧
      (∀ w : W, ρ w = MulAut.conj (φ w)) ∧
      (∀ ρ' : A →* MulAut (projectiveSL m k), (∀ w : W, ρ' w = MulAut.conj (φ w)) → ρ' = ρ) ∧
      m = 4 ∧ p = ℓ ∧ f = 2 * e ∧
      (∃ (E : Type) (_ : Field E) (_ : Finite E), Nat.card E = (ℓ ^ e) ^ 2 ∧
        Nonempty (L ≃* projectiveSL 2 E)) ∧
      StatedClassicalModel (L ⧸ center L) .PSL 2 p f ∧
      (SelectorRowS m k ρ W a L ∨ SelectorRowO m k ρ W a L) ∧
      ¬ (SelectorRowS m k ρ W a L ∧ SelectorRowO m k ρ W a L) := by
  classical
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; exact pow_ne_zero _ hℓ.ne_zero)
  have : CharP k ℓ := finite_field_prime_power_characteristic hℓ he hk
  have hk2 : ringChar k ≠ 2 := by rw [ringChar.eq k ℓ]; exact hℓ2
  have htwo : (2 : k) ≠ 0 := Ring.two_ne_zero hk2
  have hodd : Odd (Nat.card k) := by rw [hk]; exact (hℓ.odd_of_ne_two hℓ2).pow
  have hm3 : 3 ≤ m := by omega
  have hZ := center_projectiveSL_eq_bot (k := k) hm3
  obtain ⟨ρ, hinj, hρW, huniq, -⟩ := socle_extension hCW φ hZ
  obtain ⟨hW, hCA, hCW', hL₁⟩ := socle_images φ hinj hρW hLW hL
  have hinn : OuterAutomorphisms.inner (projectiveSL m k) ≤ ρ.range :=
    hW ▸ map_le_range ρ W
  have key : (SelectorRowS m k ρ W a L ∨ SelectorRowO m k ρ W a L) ∧ m = 4 ∧
      ∃ (E : Type) (_ : Field E) (_ : Finite E), Nat.card E = Nat.card k ^ 2 ∧
        Nonempty (L ≃* projectiveSL 2 E) := by
    obtain ⟨-, hform⟩ := automorphism_generation (K := k) hm3
    obtain ⟨B, τ, ε, hε, hρa⟩ := hform (ρ a)
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hε with rfl | rfl
    · rw [pow_zero, mul_one] at hρa
      by_cases hτ : τ = 1
      · subst hτ
        rw [map_one, mul_one] at hρa
        obtain ⟨μ, hμ, hsq, hm4⟩ :=
          inner_case_reduction ha hm hℓ hℓ2 he hk hinj hL₁ hρa hp2 hsrc hrank
        subst hm4
        obtain ⟨hS, hE⟩ := selectorRowS_of_inner htwo hinj hCA hCW' hL₁ hρa hμ hsq
        exact ⟨Or.inl hS, rfl, hE⟩
      · exact (field_case_false ha hm3 hℓ hℓ2 he hk hinj hL₁ hτ hρa hp2 hsrc).elim
    · rw [pow_one] at hρa
      by_cases hτ : τ = 1
      · subst hτ
        rw [map_one, mul_one] at hρa
        have hα2 : (conjAut m k B * dualAut m k) ^ 2 = 1 := by
          rw [← hρa, ← map_pow, ← ha, pow_orderOf_eq_one, map_one]
        rcases transpose_eq_or_eq_neg_of_pureGraph hm3 B hα2 with hB | hB
        · by_cases hm5 : 5 ≤ m
          · exact (orthogonal_case_false hm5 hℓ hℓ2 he hk hinj hL₁ hρa hB hp2 hsrc).elim
          · have hm4 : m = 4 := by omega
            subst hm4
            by_cases hsp : ∃ S : Submodule k (Fin 4 → k), Module.finrank k S = 2 ∧
                ∀ x ∈ S, CatalogueBLinearHigherB.matrixQuadraticForm B⁻¹ x = 0
            · exact (split_four_case_false hℓ hℓ2 he hk hinj hinn hL₁ hρa hB hsp hstd).elim
            · obtain ⟨hO, hE⟩ := selectorRowO_of_nonsplit hodd hinj hCA hCW' hL₁ hρa hB hsp
              exact ⟨Or.inr hO, rfl, hE⟩
        · exact (symplectic_case_false hm hℓ hℓ2 he hk hinj hL₁ hρa hB hp2 hsrc).elim
      · exact (graph_field_case_false ha hm hℓ hℓ2 he hk hinj hL₁ hτ hρa hp2 hsrc).elim
  obtain ⟨hrow, hm4, E, _, _, hEc, ⟨eL⟩⟩ := key
  have hE : Nat.card E = ℓ ^ (2 * e) := by rw [hEc, hk, ← pow_mul, mul_comm]
  have h4 : 4 ≤ ℓ ^ (2 * e) := by
    have h3 : 3 ≤ ℓ := by have := hℓ.two_le; omega
    calc 4 ≤ ℓ ^ 2 := by nlinarith
      _ ≤ ℓ ^ (2 * e) := Nat.pow_le_pow_right hℓ.pos (by omega)
  have hX := statedClassicalModel_of_mulEquiv_projectiveSL_two hℓ (by omega) hE h4 eL
  obtain ⟨hpl, hfe, hfirst⟩ := source_parameters hℓ2 hX hp2 hsrc
  exact ⟨ρ, hinj, hρW, huniq, hm4, hpl, hfe, ⟨E, inferInstance, inferInstance,
    by rw [hEc, hk], ⟨eL⟩⟩, hfirst, hrow, not_selectorRowS_and_selectorRowO hm3⟩

theorem faithful_odd_higher_linear_socle_small_source_involution_selector
    {A : Type} [Group A] [Finite A] {W : Subgroup A} [W.Normal]
    (hWsimple : IsSimpleGroup W) (hWnonab : ∃ x y : W, x * y ≠ y * x)
    (hCW : centralizer (W : Set A) = ⊥) {a : A} (ha : orderOf a = 2) {L : Subgroup A}
    (hLW : L ≤ W) (hL : CFSG.Assembly.IsComponentOf L (centralizer ({a} : Set A)))
    (hL2 : 2 ≤ CFSG.pRank 2 L) (hstd : IsStandardSubgroup L)
    {p f : ℕ} (_hp : p.Prime) (hp2 : p ≠ 2) (_hf : 1 ≤ f)
    (hsrc : StatedClassicalModel (L ⧸ center L) .PSL 2 p f ∨
      Nonempty (L ⧸ center L ≃* alternatingGroup (Fin 7)) ∨
      StatedClassicalModel (L ⧸ center L) .PSL 3 2 2)
    {m ℓ e : ℕ} (hm : 4 ≤ m) (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (he : 1 ≤ e) {k : Type} [Field k]
    (hk : Nat.card k = ℓ ^ e) (φ : W ≃* projectiveSL m k) :
    ∃ ρ : A →* MulAut (projectiveSL m k), Function.Injective ρ ∧
      (∀ w : W, ρ w = MulAut.conj (φ w)) ∧
      (∀ ρ' : A →* MulAut (projectiveSL m k), (∀ w : W, ρ' w = MulAut.conj (φ w)) → ρ' = ρ) ∧
      m = 4 ∧ p = ℓ ∧ f = 2 * e ∧
      (∃ (E : Type) (_ : Field E) (_ : Finite E), Nat.card E = (ℓ ^ e) ^ 2 ∧
        Nonempty (L ≃* projectiveSL 2 E)) ∧
      StatedClassicalModel (L ⧸ center L) .PSL 2 p f ∧
      (SelectorRowS m k ρ W a L ∨ SelectorRowO m k ρ W a L) ∧
      ¬ (SelectorRowS m k ρ W a L ∧ SelectorRowO m k ρ W a L) :=
  faithful_odd_higher_linear_socle_selector_core hWsimple hWnonab hCW ha hLW hL hstd hp2 hsrc
    (fun _ => Or.inl hL2) hm hℓ hℓ2 he hk φ

end CFSG.ComponentClassification.OddSelector
