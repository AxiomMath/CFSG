module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotTPGraphFieldCore
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotUniqueGraph

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.Quasithin (perfectCore)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

section Inner

variable {n : ℕ} {F : Type} [Field F] [Finite F]

theorem choose_identity (k m : ℕ) :
    k * (k - 1) + (k * (k - 1) + m * (m - 1) + 2 * (k * k + m * k + k * m)) =
      (2 * k + m) * (2 * k + m - 1) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [show 2 * (j + 1) + 0 - 1 = 2 * j + 1 by omega, Nat.add_sub_cancel]
    ring
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  obtain ⟨i, rfl⟩ : ∃ i, m = i + 1 := ⟨m - 1, by omega⟩
  rw [show 2 * (j + 1) + (i + 1) - 1 = 2 * j + i + 2 by omega, Nat.add_sub_cancel,
    Nat.add_sub_cancel]
  ring

variable [CharP F 2]

theorem le_two_mul_factorization_card_centralizer_GL {e : ℕ} (he : 1 ≤ e)
    (hF : Nat.card F = 2 ^ e) {B : GL (Fin n) F} (hB : B * B = 1) :
    e * (n * (n - 1) - (n / 2) * (n / 2 - 1)) ≤
      2 * (Nat.card (centralizer ({B} : Set (GL (Fin n) F)))).factorization 2 := by
  set V := Fin n → F
  set Ψ : GL (Fin n) F ≃* (V ≃ₗ[F] V) := Matrix.GeneralLinearGroup.toLin.trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv F V) with hΨ
  set g := Ψ B with hg
  have hgg : g * g = 1 := by rw [hg, ← map_mul, hB, map_one]
  have hcardC : Nat.card (centralizer ({B} : Set (GL (Fin n) F))) =
      Nat.card (centralizer ({g} : Set (V ≃ₗ[F] V))) := by
    refine Nat.card_congr (Equiv.subtypeEquiv Ψ.toEquiv fun x => ?_)
    rw [mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
    change x * B = B * x ↔ Ψ x * Ψ B = Ψ B * Ψ x
    rw [← map_mul, ← map_mul, Ψ.injective.eq_iff]
  set k := Module.finrank F (LinearMap.range ((g : V →ₗ[F] V) - LinearMap.id)) with hk
  have hk2 : 2 * k ≤ n := by
    have h := CFSG.LargeExtraspecial.GLR.two_mul_finrank_range_sub_id_le hgg
    rwa [Module.finrank_fin_fun] at h
  set m := n - 2 * k with hm
  have hdim : Module.finrank F V = 2 * k + m := by
    rw [Module.finrank_fin_fun]
    omega
  have hcard := CFSG.LargeExtraspecial.GLR.card_centralizer_of_mul_self_eq_one hgg hk.symm hdim
  rw [hcardC, hcard]
  have hGk := factorization_card_GL_two_pow he hF k
  have hGm := factorization_card_GL_two_pow he hF m
  rw [Nat.factorization_mul (mul_ne_zero Nat.card_pos.ne' Nat.card_pos.ne')
      (pow_ne_zero _ (by rw [hF]; positivity)), Finsupp.add_apply,
    Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply, hGk, hGm,
    hF, ← pow_mul, Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same]
  have hid := choose_identity k m
  rw [show 2 * k + m = n by omega] at hid
  have hkr : k * (k - 1) ≤ (n / 2) * (n / 2 - 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have h2k := two_mul_choose_two_eq k
  have h2m := two_mul_choose_two_eq m
  have hsub : n * (n - 1) - (n / 2) * (n / 2 - 1) ≤
      k * (k - 1) + m * (m - 1) + 2 * (k * k + m * k + k * m) := by omega
  calc e * (n * (n - 1) - (n / 2) * (n / 2 - 1))
      ≤ e * (k * (k - 1) + m * (m - 1) + 2 * (k * k + m * k + k * m)) :=
        Nat.mul_le_mul_left e hsub
    _ = 2 * (e * (k * (k - 1) / 2) + e * (m * (m - 1) / 2) + e * (k * k + m * k + k * m)) := by
        have h3 : 2 * (e * (k * (k - 1) / 2) + e * (m * (m - 1) / 2) +
            e * (k * k + m * k + k * m)) =
            e * (2 * (k * (k - 1) / 2)) + e * (2 * (m * (m - 1) / 2)) +
              e * (2 * (k * k + m * k + k * m)) := by ring
        rw [h3, h2k, h2m]
        ring

theorem le_two_mul_factorization_card_centralizer_projectiveSL {e : ℕ} (he : 1 ≤ e)
    (hF : Nat.card F = 2 ^ e) (hn : 1 ≤ n) {y : projectiveSL n F} (hy : orderOf y = 2) :
    e * (n * (n - 1) - (n / 2) * (n / 2 - 1)) ≤
      2 * (Nat.card (centralizer ({y} : Set (projectiveSL n F)))).factorization 2 := by
  have hyy : y * y = 1 := by rw [← sq, ← hy, pow_orderOf_eq_one]
  obtain ⟨A, hAA, rfl⟩ := exists_proj_eq_of_mul_self hyy
  rw [InvPlacement.centralizer_proj_eq_map hAA]
  set C := centralizer ({A} : Set (Matrix.SpecialLinearGroup (Fin n) F)) with hC
  set φ := (proj n F).comp C.subtype with hφ
  have hrange : φ.range = C.map (proj n F) := by rw [hφ, MonoidHom.range_comp, range_subtype]
  have hfac := card_ker_mul_card_range φ
  rw [hrange] at hfac
  have hkerdvd : Nat.card φ.ker ∣ Nat.card F - 1 := by
    have hle : φ.ker.map C.subtype ≤ scalars n F := by
      rintro _ ⟨x, hx, rfl⟩
      exact proj_eq_one_iff.mp hx
    have h1 := Subgroup.card_dvd_of_le hle
    rw [card_map_of_injective C.subtype_injective] at h1
    exact h1.trans (card_scalars_dvd hn)
  have hodd := odd_card_sub_one_of_two_pow he hF
  have hker2 : (Nat.card φ.ker).factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd fun h2 =>
      (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 (h2.trans hkerdvd))
  have hv : (Nat.card (C.map (proj n F))).factorization 2 = (Nat.card C).factorization 2 := by
    rw [← hfac, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply,
      hker2, zero_add]
  rw [hv, ← factorization_card_centralizer_toGL he hF hn A]
  exact le_two_mul_factorization_card_centralizer_GL he hF (by rw [← map_mul, hAA, map_one])

end Inner

section Types

open CFSG.LocalAnalysis.ComponentInitial.FourGroupEvenCanonical (matrixIsometryGroup)
open CFSG.ClassicalGroups.UnitaryFlag (unitaryPSU)

variable {n : ℕ} {K : Type} [Field K] [Finite K]

theorem conjAut_mul_dualAut_not_mem_range (hn : 3 ≤ n) (A : GL (Fin n) K) :
    conjAut n K A * dualAut n K ∉
      (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range := by
  rintro ⟨y, hy⟩
  apply ProjectivePlane.dualAut_not_mem_semilinearAutGroup (K := K) hn
  have h1 : dualAut n K = (conjAut n K A)⁻¹ * MulAut.conj y := by
    rw [hy]
    group
  rw [h1]
  exact mul_mem (inv_mem (linearAutGroup_le_semilinearAutGroup (conjAut_mem_linearAutGroup A)))
    (conj_mem_semilinearAutGroup y)

theorem exists_card_perfectCore_field (hn : 3 ≤ n) {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (A : GL (Fin n) K) {ρ : K ≃+* K} (hρ : ρ ≠ 1)
    (hθ : (conjAut n K A * fieldAut n K ρ) * (conjAut n K A * fieldAut n K ρ) = 1) :
    Even f ∧ ∃ (K₀ : Type) (_ : Field K₀) (_ : Finite K₀), Nat.card K₀ = 2 ^ (f / 2) ∧
      Nat.card (perfectCore (fixedSubgroup (conjAut n K A * fieldAut n K ρ))) =
        Nat.card (projectiveSL n K₀) := by
  obtain ⟨hfe, hρx, H, hH⟩ :=
    even_linear_field_involution_descent hf hK hn A ρ hρ (by rw [sq]; exact hθ)
  have := Fintype.ofFinite K
  have hρ2 : ρ ^ 2 = 1 := by
    ext x
    rw [sq, RingAut.mul_apply, hρx, hρx, ← pow_mul, ← pow_add,
      show f / 2 + f / 2 = f by obtain ⟨a, ha⟩ := hfe; omega, ← hK, Nat.card_eq_fintype_card,
      FiniteField.pow_card, RingAut.one_apply]
  set K₀ := CFSG.ComponentClassification.CatalogueBHigherLinearField.fixedField K ρ with hK₀
  have hsq := CFSG.ComponentClassification.CatalogueBHigherLinearField.fixedField_card_square K ρ
    hρ2 hρ
  have hcard : Nat.card K₀ = 2 ^ (f / 2) := by
    obtain ⟨a, ha⟩ := hfe
    rw [hK, show f = 2 * (f / 2) by omega, pow_mul', ← hK₀] at hsq
    exact (Nat.pow_left_injective (by norm_num : 2 ≠ 0) hsq).symm
  refine ⟨hfe, K₀, inferInstance, inferInstance, hcard, ?_⟩
  have hfix : ∀ x : K, ρ x = x ↔ x ∈ Set.range (K₀.subtype : K₀ →+* K) := by
    intro x
    rw [← CFSG.ComponentClassification.CatalogueBHigherLinearField.mem_fixedField K ρ x]
    exact ⟨fun h => ⟨⟨x, h⟩, rfl⟩, fun ⟨y, hy⟩ => hy ▸ y.2⟩
  rw [hH]
  exact card_perfectCore_fixedSubgroup_conj_fieldAut hn _ hfix H

theorem exists_card_perfectCore_graphField (hn : 4 ≤ n) {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) (A : GL (Fin n) K) {ρ : K ≃+* K} (hρ : ρ ≠ 1)
    (hθ : (conjAut n K A * fieldAut n K ρ * dualAut n K) *
        (conjAut n K A * fieldAut n K ρ * dualAut n K) = 1) :
    Even f ∧ ∃ h : UnitaryFieldData 2 (f / 2) K,
      Nat.card (perfectCore (fixedSubgroup (conjAut n K A * fieldAut n K ρ * dualAut n K))) =
        Nat.card (unitaryPSU h n) := by
  obtain ⟨hfe, hρx, H, hH⟩ := UnitaryHigher.linear_graph_field_involution_descent Nat.prime_two hf
    hK (by omega) A ρ hρ (by rw [sq]; exact hθ)
  obtain ⟨a, ha⟩ := hfe
  have hud : UnitaryFieldData 2 (f / 2) K := ⟨Nat.prime_two, by omega, by
    rw [hK]; congr 1; omega⟩
  refine ⟨⟨a, ha⟩, hud, ?_⟩
  have hσ : ∀ x, ρ x = hud.bar x := fun x => by rw [hρx, UnitaryFieldData.bar_apply]
  have hfix : autFixSubgroup (fieldAut n K ρ * dualAut n K) =
      fixedSubgroup (fieldAut n K ρ * dualAut n K) := by
    ext x
    rfl
  rw [hH, card_perfectCore_fixedSubgroup_conjAut_mul, ← hfix]
  exact card_perfectCore_graphField hud (by omega) (by
    intro h
    have := congrArg Prod.fst h
    simp at this
    omega) ρ hσ

end Types

section TwoParts

open CFSG.LocalAnalysis.ComponentInitial.FourGroupEvenCanonical (matrixIsometryGroup)
open CFSG.ClassicalGroups.UnitaryFlag (unitarySU unitaryPSU)

variable {n : ℕ}

theorem not_two_dvd_prod_two_pow_sub_one {a : ℕ} (ha : 1 ≤ a) (n : ℕ) :
    ¬ 2 ∣ ∏ j ∈ Finset.Icc 2 n, ((2 ^ a) ^ j - 1) := by
  rw [Prime.dvd_finsetProd_iff Nat.prime_two.prime]
  rintro ⟨j, hj, hdvd⟩
  rw [Finset.mem_Icc] at hj
  have h2 : 2 ∣ (2 ^ a) ^ j := by
    rw [← pow_mul]
    exact dvd_pow_self 2 (Nat.mul_ne_zero (by omega) (by omega))
  have h1 : 1 ≤ (2 ^ a) ^ j := Nat.one_le_pow _ _ (by positivity)
  generalize (2 ^ a) ^ j = s at h1 h2 hdvd
  omega

theorem factorization_card_projectiveSL_two_pow {a : ℕ} (ha : 1 ≤ a) {K₀ : Type} [Field K₀]
    [Finite K₀] (hK₀ : Nat.card K₀ = 2 ^ a) (hn : 1 ≤ n) :
    (Nat.card (projectiveSL n K₀)).factorization 2 = a * (n * (n - 1) / 2) := by
  have h1 : Nat.card (Matrix.SpecialLinearGroup (Fin n) K₀) =
      Nat.card (projectiveSL n K₀) * Nat.card (scalars n K₀) :=
    (scalars n K₀).card_eq_card_quotient_mul_card_subgroup
  have hsc : (Nat.card (scalars n K₀)).factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd fun h2 =>
      (Nat.not_even_iff_odd.2 (odd_card_sub_one_of_two_pow ha hK₀))
        (even_iff_two_dvd.2 (h2.trans (card_scalars_dvd hn)))
  have hodd := not_two_dvd_prod_two_pow_sub_one ha n
  have hne : ∏ j ∈ Finset.Icc 2 n, ((2 ^ a) ^ j - 1) ≠ 0 := fun h => hodd (h ▸ dvd_zero 2)
  have hSL : (Nat.card (Matrix.SpecialLinearGroup (Fin n) K₀)).factorization 2 =
      a * (n * (n - 1) / 2) := by
    rw [card_SL_eq hn, hK₀, Nat.factorization_mul (pow_ne_zero _ (pow_ne_zero _ two_ne_zero)) hne,
      Finsupp.add_apply, ← pow_mul, Nat.Prime.factorization_pow Nat.prime_two,
      Finsupp.single_eq_same, Nat.factorization_eq_zero_of_not_dvd hodd, add_zero]
  rw [h1, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply, hsc,
    add_zero] at hSL
  exact hSL

theorem factorization_card_unitaryPSU_two_pow {a : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 a K) (hn : 1 ≤ n) :
    (Nat.card (unitaryPSU h n)).factorization 2 = a * (n * (n - 1) / 2) := by
  have hmul := card_unitaryPSU_mul h hn
  have hfac := (card_unitarySU_and_factorization h hn).2
  rw [← pow_mul] at hfac
  have hSU := Nat.pow_right_injective (le_refl 2) hfac
  have hgcd : ¬ 2 ∣ Nat.gcd n (2 ^ a + 1) := by
    intro h2
    have h3 : 2 ∣ 2 ^ a + 1 := h2.trans (Nat.gcd_dvd_right _ _)
    have h4 : 2 ∣ 2 ^ a := dvd_pow_self 2 (by have := h.one_le; omega)
    exact absurd ((Nat.dvd_add_right h4).1 h3) (by norm_num)
  have hg0 : Nat.gcd n (2 ^ a + 1) ≠ 0 := Nat.gcd_ne_zero_right (Nat.succ_ne_zero _)
  have hP0 : Nat.card (unitaryPSU h n) ≠ 0 := by
    have := h.finite
    exact Nat.card_pos.ne'
  rw [← hmul, Nat.factorization_mul hP0 hg0, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hgcd, add_zero] at hSU
  exact hSU

end TwoParts

section Classification

open CFSG.LocalAnalysis.ComponentInitial.FourGroupEvenCanonical (matrixIsometryGroup)
open CFSG.ClassicalGroups.UnitaryFlag (unitaryPSU)

variable {n : ℕ} {K : Type} [Field K]

@[expose] def FieldTypeCore (n f : ℕ) (K : Type) [Field K] (θ : MulAut (projectiveSL n K)) :
    Prop :=
  Even f ∧ ((∃ (K₀ : Type) (_ : Field K₀) (_ : Finite K₀), Nat.card K₀ = 2 ^ (f / 2) ∧
      Nat.card (perfectCore (fixedSubgroup θ)) = Nat.card (projectiveSL n K₀)) ∨
    ∃ h : UnitaryFieldData 2 (f / 2) K,
      Nat.card (perfectCore (fixedSubgroup θ)) = Nat.card (unitaryPSU h n))

variable [Finite K]

theorem involution_types [CharP K 2] (hn : 4 ≤ n) {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    {θ : MulAut (projectiveSL n K)} (hθ : θ * θ = 1) (hθ1 : θ ≠ 1) :
    (∃ y : projectiveSL n K, orderOf y = 2 ∧ θ = MulAut.conj y) ∨
      (∃ A : GL (Fin n) K, θ = conjAut n K A * dualAut n K) ∨ FieldTypeCore n f K θ := by
  obtain ⟨A, ρ, ε, hε, rfl⟩ := (automorphism_generation (K := K) (by omega : 3 ≤ n)).2 θ
  rcases (by omega : ε = 0 ∨ ε = 1) with rfl | rfl
  · rw [pow_zero, mul_one] at hθ hθ1 ⊢
    by_cases hρ : ρ = 1
    · subst hρ
      rw [map_one, mul_one] at hθ hθ1 ⊢
      obtain ⟨y, hy, hyA⟩ := CFSG.ComponentClassification.OutcomeLocal.exists_involution_eq_conjAut
        (by omega) A (by rw [sq, hθ]) hθ1
      exact Or.inl ⟨y, hy, hyA⟩
    · obtain ⟨hfe, hex⟩ := exists_card_perfectCore_field (by omega) hf hK A hρ hθ
      exact Or.inr (Or.inr ⟨hfe, Or.inl hex⟩)
  · rw [pow_one] at hθ hθ1 ⊢
    by_cases hρ : ρ = 1
    · subst hρ
      rw [map_one, mul_one]
      exact Or.inr (Or.inl ⟨A, rfl⟩)
    · obtain ⟨hfe, hex⟩ := exists_card_perfectCore_graphField hn hf hK A hρ hθ
      exact Or.inr (Or.inr ⟨hfe, Or.inr hex⟩)

theorem le_factorization_card_fixedSubgroup_graph (hn : 3 ≤ n) {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) (A : GL (Fin n) K)
    (hθ : (conjAut n K A * dualAut n K) * (conjAut n K A * dualAut n K) = 1) :
    f * (n / 2) ^ 2 ≤ (Nat.card (fixedSubgroup (conjAut n K A * dualAut n K))).factorization 2 := by
  have : CharP K 2 := charP_two_of_card_eq_two_pow hK
  obtain ⟨C, hC, hcard, -⟩ := card_fixedSubgroup_graph_eq hf hK hn A hθ
  rw [hcard]
  have hdvd : Nat.card K ^ ((n / 2) ^ 2) ∣
      Nat.card (matrixIsometryGroup (C : Matrix (Fin n) (Fin n) K)) := by
    rcases hC with hC1 | ⟨r, hr, hJ⟩
    · rw [hC1]
      obtain ⟨r, hr | hr⟩ := Nat.even_or_odd' n
      · rw [show n / 2 = r by omega]
        exact pow_dvd_card_matrixIsometryGroup_one hr (by omega)
      · rw [card_matrixIsometryGroup_one_of_odd hr, show n / 2 = r by omega]
        exact pow_dvd_card_statedSp r
    · rw [hJ, card_matrixIsometryGroup_blockSwapJ hr, show n / 2 = r by omega]
      exact pow_dvd_card_statedSp r
  rw [hK, ← pow_mul] at hdvd
  exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').1 hdvd

theorem le_four_mul_factorization_of_fieldTypeCore (hn : 1 ≤ n) {f : ℕ} (hf : 2 ≤ f)
    {θ : MulAut (projectiveSL n K)} (hθ : FieldTypeCore n f K θ) :
    f * (n * (n - 1)) ≤ 4 * (Nat.card (fixedSubgroup θ)).factorization 2 := by
  obtain ⟨⟨a, ha⟩, hdata⟩ := hθ
  have hfa : f / 2 = a := by omega
  have hcore : a * (n * (n - 1) / 2) ≤
      (Nat.card (perfectCore (fixedSubgroup θ))).factorization 2 := by
    rcases hdata with ⟨K₀, _, _, hK₀, hcard⟩ | ⟨h, hcard⟩
    · rw [hcard, factorization_card_projectiveSL_two_pow (by omega) hK₀ hn, hfa]
    · rw [hcard, factorization_card_unitaryPSU_two_pow h hn, hfa]
  have hle : (Nat.card (perfectCore (fixedSubgroup θ))).factorization 2 ≤
      (Nat.card (fixedSubgroup θ)).factorization 2 :=
    factorization_two_le_of_dvd (Subgroup.card_dvd_of_le (CFSG.Quasithin.perfectCore_le _))
      Nat.card_pos.ne'
  have h2 := two_mul_choose_two_eq n
  have h3 : f * (n * (n - 1)) = 4 * (a * (n * (n - 1) / 2)) := by
    calc f * (n * (n - 1)) = (a + a) * (2 * (n * (n - 1) / 2)) := by rw [h2, ha]
      _ = 4 * (a * (n * (n - 1) / 2)) := by ring
  omega

end Classification

end CFSG.SeitzReduction.LinearPilot
