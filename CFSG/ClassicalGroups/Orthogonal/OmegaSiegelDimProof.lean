module

public import CFSG.ClassicalGroups.Orthogonal.OmegaSiegelDim
public import CFSG.ClassicalGroups.Orthogonal.OmegaSiegelMinusFour
public import CFSG.ClassicalGroups.Orthogonal.OmegaSiegelMinusThreeI
public import CFSG.ClassicalGroups.Orthogonal.OmegaSiegelMinusThreeII
import CFSG.Timmesfeld.Orders.ClassicalOmega
public import CFSG.ClassicalGroups.Orthogonal.OmegaSiegelMain

public section

namespace CFSG.ClassicalGroups.Orthogonal.OmegaSiegel

open CFSG.HardMathSupport.Kantor79 CFSG.ClassicalGroups.Orthogonal.SiegelRT1
open CFSG.RankThree.GF2n.Smith81 QuadraticMap Module

private theorem nd_polarBilin_of_forall {K : Type*} [Field K] {V : Type*} [AddCommGroup V]
    [Module K V] {Qf : QuadraticForm K V} (hnd : ∀ x : V, (∀ y, polar Qf x y = 0) → x = 0) :
    (polarBilin Qf).Nondegenerate :=
  ⟨fun x hx => hnd x fun y => hx y, fun y hy => hnd y fun x => by rw [polar_comm]; exact hy x⟩

private noncomputable def plusIsometryOf {K : Type*} [Field K] {W : Type*} [AddCommGroup W]
    [Module K W] {n : ℕ} {Q₀ : QuadraticForm K W} (b : Module.Basis (Fin n ⊕ Fin n) K W)
    (hb : ∀ x y : Fin n → K, Q₀ (∑ i, x i • b (.inl i) + ∑ i, y i • b (.inr i)) =
      ∑ i, x i * y i) :
    Q₀.IsometryEquiv (CFSG.LieType.Universal.Spin.quadPlus n K) where
  toLinearEquiv := b.equivFun
  map_app' w := by
    have hw : w = ∑ i, b.repr w (.inl i) • b (.inl i) +
        ∑ i, b.repr w (.inr i) • b (.inr i) := by
      conv_lhs => rw [← b.sum_repr w]
      rw [Fintype.sum_sum_type]
    change CFSG.LieType.Universal.Spin.quadPlus n K (b.equivFun w) = Q₀ w
    conv_rhs => rw [hw]
    rw [hb, CFSG.LieType.Universal.Spin.quadPlus_apply]
    rfl

private noncomputable def minusIsometryOf {K : Type*} [Field K] {W : Type*} [AddCommGroup W]
    [Module K W] {n : ℕ} {Q₀ : QuadraticForm K W} {β γ : K}
    (b : Module.Basis (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) K W)
    (hb : ∀ (x y : Fin (n - 1) → K) (s t : K),
      Q₀ (∑ i, x i • b (.inl i) + ∑ i, y i • b (.inr (.inl i)) + s • b (.inr (.inr 0)) +
        t • b (.inr (.inr 1))) = ∑ i, x i * y i + s ^ 2 + β * s * t + γ * t ^ 2) :
    Q₀.IsometryEquiv (CFSG.LieType.Universal.Spin.quadMinus n K β γ) where
  toLinearEquiv := b.equivFun
  map_app' w := by
    have hw : w = ∑ i, b.repr w (.inl i) • b (.inl i) +
        ∑ i, b.repr w (.inr (.inl i)) • b (.inr (.inl i)) +
          b.repr w (.inr (.inr 0)) • b (.inr (.inr 0)) +
            b.repr w (.inr (.inr 1)) • b (.inr (.inr 1)) := by
      conv_lhs => rw [← b.sum_repr w]
      rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fin.sum_univ_two]
      abel
    change CFSG.LieType.Universal.Spin.quadMinus n K β γ (b.equivFun w) = Q₀ w
    conv_rhs => rw [hw]
    rw [hb, CFSG.LieType.Universal.Spin.quadMinus_apply]
    rfl

private theorem exists_model_isometry {K : Type*} [Field K] [Finite K] [CharP K 2] {V : Type*}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Qf : QuadraticForm K V}
    (hnd : (polarBilin Qf).Nondegenerate) {n : ℕ} (hn : 1 ≤ n) (hdim : finrank K V = 2 * n) :
    Nonempty (Qf.IsometryEquiv (CFSG.LieType.Universal.Spin.quadPlus n K)) ∨
      ∃ b c : K, (∀ s : K, s ^ 2 + b * s + c ≠ 0) ∧
        Nonempty (Qf.IsometryEquiv (CFSG.LieType.Universal.Spin.quadMinus n K b c)) := by
  rcases (CFSG.ComponentClassification.UnbalancedCatalog.finite_even_regular_quadratic_normal_forms
    Qf hnd).2.2.1 n hn hdim with ⟨b, hb⟩ | ⟨β, γ, -, hroot, b, hb⟩
  · exact Or.inl ⟨plusIsometryOf b hb⟩
  · exact Or.inr ⟨β, γ, hroot, ⟨minusIsometryOf b hb⟩⟩

private theorem not_pow_four_dvd_of_lt {q F : ℤ} (hF : 0 < F) (hlt : F < q ^ 4)
    (h : q ^ 4 ∣ F) : False :=
  absurd (Int.le_of_dvd hF h) (not_le.2 hlt)

private theorem not_pow_four_dvd_of_coprime {q B F : ℤ} (hq : 2 ≤ q) (hcop : IsCoprime q B)
    (hF : F = 2 * q ^ 2 * B) (h : q ^ 4 ∣ F) : False := by
  have hq0 : 0 < q := by linarith
  have h1 : q ^ 4 ∣ 2 * q ^ 2 := (hcop.pow_left).dvd_of_dvd_mul_right (hF ▸ h)
  have h3 := Int.le_of_dvd (mul_pos two_pos (pow_pos hq0 2)) h1
  have h4 : 2 * 2 ≤ q * q := mul_le_mul hq hq (by norm_num) hq0.le
  have h5 : 4 * (q * q) ≤ (q * q) * (q * q) :=
    mul_le_mul_of_nonneg_right (by linarith) (mul_self_nonneg q)
  nlinarith

private theorem two_mul_add_two_lt_pow_four {q : ℤ} (hq : 2 ≤ q) : 2 * q + 2 < q ^ 4 := by
  have h1 : 4 ≤ q * q := by nlinarith
  have h2 : 4 * (q * q) ≤ q * q * (q * q) := mul_le_mul_of_nonneg_right h1 (mul_self_nonneg q)
  have h3 : 2 * q ≤ q * q := by nlinarith
  nlinarith

private theorem not_pow_four_dvd_plus_two {q F : ℤ} (hq : 2 ≤ q)
    (hF : F = 2 * q ^ 2 * (q ^ 2 - 1) * (q ^ 2 - 1)) (h : q ^ 4 ∣ F) : False :=
  not_pow_four_dvd_of_coprime (B := (q ^ 2 - 1) * (q ^ 2 - 1)) hq ⟨-(q ^ 3 - 2 * q), 1, by ring⟩
    (by rw [hF]; ring) h

private theorem not_pow_four_dvd_minus_two {q F : ℤ} (hq : 2 ≤ q)
    (hF : F = 2 * q ^ 2 * (q ^ 2 + 1) * (q ^ 2 - 1)) (h : q ^ 4 ∣ F) : False :=
  not_pow_four_dvd_of_coprime (B := (q ^ 2 + 1) * (q ^ 2 - 1)) hq ⟨q ^ 3, -1, by ring⟩
    (by rw [hF]; ring) h

theorem six_le_finrank_of_pow_four_dvd_card {K : Type*} [Field K] [Finite K] [CharP K 2]
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Qf : QuadraticForm K V}
    (hnd : ∀ x : V, (∀ y, polar Qf x y = 0) → x = 0) {X : Type*} [Group X]
    (ρ : X →* (V ≃ₗ[K] V)) (hρ : Function.Injective ρ) (hρQ : ∀ g v, Qf (ρ g v) = Qf v)
    (hX : Nat.card K ^ 4 ∣ Nat.card X) : 6 ≤ finrank K V := by
  have hnd' := nd_polarBilin_of_forall hnd
  have hdvd : Nat.card X ∣ Nat.card (TauCeti.QuadraticMap.orthogonalGroup Qf) := by
    have hle : ρ.range ≤ TauCeti.QuadraticMap.orthogonalGroup Qf := by
      rintro _ ⟨g, rfl⟩
      exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr (hρQ g)
    rw [Nat.card_congr (MonoidHom.ofInjective hρ).toEquiv]
    exact Subgroup.card_dvd_of_le hle
  have hX0 := hX.trans hdvd
  have hq : 2 ≤ Nat.card K := Finite.one_lt_card
  have hq' : (2 : ℤ) ≤ (Nat.card K : ℤ) := by exact_mod_cast hq
  obtain ⟨n, hn⟩ := CFSG.ComponentClassification.UnbalancedCatalog.even_finrank_of_charTwo Qf hnd'
  by_contra hlt
  rcases Nat.eq_zero_or_pos n with rfl | hn1
  ·
    have hsub : Subsingleton V := Module.finrank_zero_iff.1 (by omega)
    rw [(CFSG.Timmesfeld.ClassicalOrders.card_singular_and_orthogonalGroup_of_subsingleton Qf).2]
      at hX0
    have h1 := Nat.dvd_one.1 hX0
    have := Nat.one_lt_pow (by norm_num : (4 : ℕ) ≠ 0) hq
    omega
  obtain ⟨⟨e⟩⟩ | ⟨b, c, hirr, ⟨e⟩⟩ :=
    exists_model_isometry hnd' hn1 (show finrank K V = 2 * n by omega)
  ·
    rw [CFSG.Timmesfeld.ClassicalOrders.card_orthogonalGroup_congr e] at hX0
    have hZ := Int.natCast_dvd_natCast.mpr hX0
    push_cast at hZ
    rcases (show n = 1 ∨ n = 2 by omega) with rfl | rfl
    · have h := (CFSG.Timmesfeld.ClassicalOrders.card_quadPlus (K := K) 0).2
      rw [show (0 : ℕ) + 1 = 1 from rfl, Finset.Icc_eq_empty_of_lt (by norm_num)] at h
      simp only [pow_zero, pow_one, Finset.prod_empty, mul_one] at h
      exact not_pow_four_dvd_of_lt (by rw [h]; linarith)
        (by rw [h]; linarith [two_mul_add_two_lt_pow_four hq']) hZ
    · have h := (CFSG.Timmesfeld.ClassicalOrders.card_quadPlus (K := K) 1).2
      rw [show (1 : ℕ) + 1 = 2 from rfl] at h
      simp only [one_mul, mul_one, Finset.Icc_self, Finset.prod_singleton] at h
      exact not_pow_four_dvd_plus_two hq' h hZ
  ·
    rw [CFSG.Timmesfeld.ClassicalOrders.card_orthogonalGroup_congr e] at hX0
    have hZ := Int.natCast_dvd_natCast.mpr hX0
    push_cast at hZ
    rcases (show n = 1 ∨ n = 2 by omega) with rfl | rfl
    · have h := (CFSG.Timmesfeld.ClassicalOrders.card_quadMinus (K := K) 0 hirr).2
      rw [show (0 : ℕ) + 1 = 1 from rfl, Finset.Icc_eq_empty_of_lt (by norm_num)] at h
      simp only [pow_zero, pow_one, Finset.prod_empty, mul_one] at h
      exact not_pow_four_dvd_of_lt (by rw [h]; linarith)
        (by rw [h]; linarith [two_mul_add_two_lt_pow_four hq']) hZ
    · have h := (CFSG.Timmesfeld.ClassicalOrders.card_quadMinus (K := K) 1 hirr).2
      rw [show (1 : ℕ) + 1 = 2 from rfl] at h
      simp only [one_mul, mul_one, Finset.Icc_self, Finset.prod_singleton] at h
      exact not_pow_four_dvd_minus_two hq' h hZ

theorem natCard_rootGroup_hypPair {K : Type*} [Field K] [Finite K] [CharP K 2] {N : Type*}
    [AddCommGroup N] [Module K N] [FiniteDimensional K N] {Q : QuadraticForm K N}
    (hnd : (polarBilin Q).Nondegenerate) (P : HypPair Q) :
    Nat.card (rootGroup Q P.e) = Nat.card K ^ (finrank K N - 2) :=
  card_rootGroup hnd P.Q_e P.e_ne_zero

theorem pow_dvd_natCard_elementaryGroup {K : Type} [Field K] [Finite K] [CharP K 2] {N : Type}
    [AddCommGroup N] [Module K N] [FiniteDimensional K N] {Q : QuadraticForm K N}
    (hnd : (polarBilin Q).Nondegenerate) {m : ℕ} (hdim : finrank K N = 2 * m) (hm : 4 ≤ m) :
    Nat.card K ^ (m * (m - 1)) ∣ Nat.card ↥(elementaryGroup Q) := by
  open CFSG.ComponentClassification.CatalogueBOrthogonalPointIsometry in
  have hz : (Nat.card K : ℤ) ^ (m * (m - 1)) ∣ (Nat.card ↥(elementaryGroup Q) : ℤ) := by
    rcases CFSG.GroupTheory.WeirSylow.exists_isometry_quadPlus_or_quadMinus Q hnd (by omega) hdim
      with ⟨⟨e⟩⟩ | ⟨b, c, hirr, ⟨e⟩⟩
    · rw [Nat.card_congr (elementaryIsometryEquiv e).toEquiv,
        CFSG.Timmesfeld.ClassicalOrders.card_elementaryGroup_quadPlus hm]
      exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
    · rw [Nat.card_congr (elementaryIsometryEquiv e).toEquiv,
        CFSG.Timmesfeld.ClassicalOrders.card_elementaryGroup_quadMinus hm hirr]
      exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
  exact_mod_cast hz

private theorem pow_four_dvd_natCard_of_pair {K : Type} [Field K] [Finite K] [CharP K 2]
    {N : Type} [AddCommGroup N] [Module K N] [FiniteDimensional K N] {Q : QuadraticForm K N}
    (hnd : (polarBilin Q).Nondegenerate) (P : HypPair Q) (hdim : finrank K N = 2 * 3) :
    Nat.card K ^ 4 ∣ Nat.card ↥(elementaryGroup Q) := by
  have h := Subgroup.card_dvd_of_le (rootGroup_le_elementaryGroup Q P.e)
  rw [natCard_rootGroup_hypPair hnd P, hdim] at h
  exact h

theorem omegaSiegelDimStatement_holds : OmegaSiegelDimStatement := by
  intro K' _ _ _ K _ _ _ hcard hq4 N _ _ _ QN hndN m hdimN hm3 V _ _ _ Qf hnd ρ hinj hiso h₀
    hfix htop
  have hs : OmegaSetting QN Qf ρ := omegaSetting_of_exists hdimN hm3 hcard hndN hnd hinj hiso h₀
  have hnorm := CFSG.ComponentClassification.UnbalancedCatalog.exists_hypPairs_normal m ⊤
    (polarNondegOn_top hndN) (by rw [finrank_top, hdimN])
  obtain ⟨r, hr⟩ := CFSG.ComponentClassification.UnbalancedCatalog.even_finrank_of_charTwo Qf
    (nd_polarBilin_of_forall hnd)
  rcases Nat.lt_or_ge m 4 with hm4 | hm4
  ·
    obtain rfl : m = 3 := by omega
    have hK2 : 2 < Nat.card K' := by omega
    have hne : Nonempty (HypPair QN) := by
      rcases hnorm with ⟨P, -, -⟩ | ⟨m', hm', P, -⟩
      · exact ⟨P ⟨0, by norm_num⟩⟩
      · exact ⟨P ⟨0, by omega⟩⟩
    obtain ⟨P0⟩ := hne
    have hX4 : Nat.card K ^ 4 ∣ Nat.card ↥(elementaryGroup QN) := by
      rw [← hcard]
      exact pow_four_dvd_natCard_of_pair hndN P0 hdimN
    have h6 : 6 ≤ finrank K V := six_le_finrank_of_pow_four_dvd_card hnd ρ hinj hiso hX4
    rcases hnorm with ⟨P, -, hP⟩ | ⟨m', hm', P, u, v, -, hP, -, -, huv, hQu, hpuv, hroot⟩
    · obtain ⟨e, f, p, p', w, j₁, hF⟩ := exists_listFrame_three hdimN P hP
      have h8 := hs.finrank_le_eight_of_listFrame htop hF
      omega
    · obtain rfl : m' = 2 := by omega
      have hF := exists_minusThreeFrame (by omega) P (hP 0 1 (by decide)) huv hQu hpuv hroot
      rcases hs.flag_dichotomy hF with hI | hII
      · have h6' := hs.finrank_le_six_of_caseI htop hF hI
        omega
      · have h8 := hs.finrank_le_eight_of_caseII htop hfix hK2 hF hII
        omega
  · have hX : Nat.card K ^ (m * (m - 1)) ∣ Nat.card ↥(elementaryGroup QN) := by
      rw [← hcard]
      exact pow_dvd_natCard_elementaryGroup hndN hdimN hm4
    have hlow : 2 * m ≤ finrank K V :=
      two_mul_le_finrank_of_pow_dvd_card hnd ρ hinj hiso (m := m) (by omega) hX
    rcases hnorm with ⟨P, -, hP⟩ | ⟨m', hm', P, u, v, -, hP, -, -, huv, hQu, hpuv, hroot⟩
    · obtain ⟨e, f, p, p', w, j₁, hF, hC⟩ := exists_listFrame_plus hdimN hm4 P hP
      have h := hs.finrank_le_of_listFrame htop hF hC
      omega
    · rcases Nat.lt_or_ge m 5 with hm5 | hm5
      · obtain rfl : m = 4 := by omega
        obtain rfl : m' = 3 := by omega
        have h := hs.finrank_le_nine_of_minusFour htop (by omega) P hP huv hQu hpuv hroot
        omega
      · obtain rfl : m' = m - 1 := by omega
        obtain ⟨e, f, p, p', w, j₁, hF, hC⟩ :=
          exists_listFrame_minus hdimN hm5 P hP huv hQu hpuv
        have h := hs.finrank_le_of_listFrame htop hF hC
        omega

end CFSG.ClassicalGroups.Orthogonal.OmegaSiegel
