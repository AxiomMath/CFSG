module

public import CFSG.LocalAnalysis.LyonsUnitaryFour.FiveColumns.GlobalFiveColumns

public section

open scoped BigOperators Classical

namespace CFSG.LyonsUnitaryFour

open CFSG.TwoRankLowerBound.Helpers CFSG.Wreathed CFSG.RankTwoShapes

theorem irreducible_character_central_mul {L : Type*} [Group L] [Fintype L]
    (data : FiniteComplexRepresentation L) (hirr : data.IsIrreducible) {x : L}
    (hx : x ∈ Subgroup.center L) (y : L) :
    data.character (x * y) * data.character 1 = data.character x * data.character y := by
  let : data.representation.IsIrreducible := hirr
  have hdeg := irreducible_character_degree_ne_zero data hirr
  have hscalar := irreducible_conjugacy_class_sum data.representation x {x}
    (fun conjugator element => by
      simp only [Finset.mem_singleton]
      constructor
      · rintro rfl
        rw [Subgroup.mem_center_iff.mp hx conjugator, mul_inv_cancel_right]
      · intro h
        have h' : conjugator * element * conjugator⁻¹ = conjugator * x * conjugator⁻¹ := by
          rw [h, Subgroup.mem_center_iff.mp hx conjugator, mul_inv_cancel_right]
        simpa using h')
    (fun element helement => by rw [Finset.mem_singleton] at helement; rw [helement])
    hdeg
  simp only [Finset.sum_singleton, Finset.card_singleton, Nat.cast_one, one_mul] at hscalar
  have hxy : data.character (x * y) = data.character x / data.character 1 * data.character y := by
    change LinearMap.trace ℂ _ (data.representation (x * y)) = _
    rw [map_mul, hscalar, smul_mul_assoc, one_mul, map_smul, smul_eq_mul]
    rfl
  rw [hxy]
  field_simp

theorem sum_central_weight_sq {L : Type*} [Group L] [Fintype L]
    (basis : FiniteIrreducibleCharacterBasis L) (N : L → ℂ)
    (hN : ∀ g, N g ≠ 0 → g ∈ Subgroup.center L) (v : L) :
    ∑ θ, (∑ g, N g * (basis.representation θ).character g) ^ 2 *
        (basis.representation θ).character v / (basis.representation θ).character 1 =
      (Nat.card L : ℂ) * ∑ g, ∑ g', N g * N g' * (if g * g' * v = 1 then 1 else 0) := by
  have hterm : ∀ θ g g', N g * N g' * ((basis.representation θ).character g *
      (basis.representation θ).character g' * (basis.representation θ).character v /
        (basis.representation θ).character 1) =
      N g * N g' * ((basis.representation θ).character 1 *
        (basis.representation θ).character (g * g' * v)) := by
    intro θ g g'
    by_cases hg : N g = 0
    · simp [hg]
    by_cases hg' : N g' = 0
    · simp [hg']
    congr 1
    have hdeg := irreducible_character_degree_ne_zero (basis.representation θ)
      (basis.irreducible θ)
    have h1 := irreducible_character_central_mul (basis.representation θ) (basis.irreducible θ)
      (hN g hg) (g' * v)
    have h2 := irreducible_character_central_mul (basis.representation θ) (basis.irreducible θ)
      (hN g' hg') v
    rw [mul_assoc g g' v]
    set c := (basis.representation θ).character with hc
    calc c g * c g' * c v / c 1 = c g * (c g' * c v) / c 1 := by ring
      _ = c g * (c (g' * v) * c 1) / c 1 := by rw [h2]
      _ = c g * c (g' * v) := by field_simp
      _ = c (g * (g' * v)) * c 1 := h1.symm
      _ = c 1 * c (g * (g' * v)) := mul_comm _ _
  have hexp : ∀ θ, (∑ g, N g * (basis.representation θ).character g) ^ 2 *
      (basis.representation θ).character v / (basis.representation θ).character 1 =
      ∑ g, ∑ g', N g * N g' * ((basis.representation θ).character 1 *
        (basis.representation θ).character (g * g' * v)) := by
    intro θ
    rw [sq, Finset.sum_mul_sum, Finset.sum_mul, Finset.sum_div]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [Finset.sum_mul, Finset.sum_div]
    refine Finset.sum_congr rfl fun g' _ => ?_
    rw [← hterm θ g g']
    ring
  rw [Finset.sum_congr rfl fun θ _ => hexp θ, Finset.sum_comm]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun g' _ => ?_
  rw [← Finset.mul_sum]
  have hcol := complete_complex_character_column_sum basis 1 (g * g' * v)
  have hreal : ∀ θ, (basis.representation θ).character 1 *
      (basis.representation θ).character (g * g' * v) =
      (basis.representation θ).character (g * g' * v) *
        starRingEnd ℂ ((basis.representation θ).character 1) := by
    intro θ
    rw [mul_comm]
    congr 1
    rw [FiniteComplexRepresentation.character, Representation.char_one, Complex.conj_natCast]
  rw [Finset.sum_congr rfl fun θ _ => hreal θ, hcol]
  unfold conjugatorCount
  simp only [mul_one, mul_inv_cancel]
  by_cases h1 : g * g' * v = 1
  · rw [ite_eq_left h1]
    simp only [h1, ite_true, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
      ← Nat.card_eq_fintype_card]
    ring
  · rw [ite_eq_right h1]
    simp only [Ne.symm h1, ite_false, Finset.sum_const_zero, mul_zero]

namespace UnitaryFourByFive

variable {L : Type} [Group L] [Fintype L] {S₀ : Subgroup L} {h : L}
  (hL : UnitaryFourByFive S₀ h)
include hL

theorem pair_count {z₀ w₀ : L} (hz₀ : z₀ ∈ (Subgroup.center S₀).map S₀.subtype)
    (hw₀ : w₀ ∈ (Subgroup.center S₀).map S₀.subtype) (hz₀2 : z₀ * z₀ = 1)
    (hw₀2 : w₀ * w₀ = 1) (hz₀1 : z₀ ≠ 1) (hw₀1 : w₀ ≠ 1) (hzw : w₀ ≠ z₀)
    (N : L → ℂ) (n : ℂ) (hN : ∀ g, N g ≠ 0 → g = z₀ ∨ g = w₀ ∨ g = z₀ * w₀)
    (hNz : N z₀ = 1) (hNw : N w₀ = n) (hNzw : N (z₀ * w₀) = n) {j : ℕ} (hj : j < 5) :
    ∑ g, ∑ g', N g * N g' * (if g * g' * (z₀ * h ^ j) = 1 then 1 else 0) =
      if j = 0 then 2 * n ^ 2 else 0 := by
  have hcz := Subgroup.mem_center_iff.mp (hL.center_le_center hz₀)
  have hzS : z₀ ∈ S₀ := (mem_map_center_iff.mp hz₀).1
  have hwS : w₀ ∈ S₀ := (mem_map_center_iff.mp hw₀).1
  have hzwsq : z₀ * w₀ * (z₀ * w₀) = 1 := by
    calc z₀ * w₀ * (z₀ * w₀) = z₀ * (w₀ * z₀) * w₀ := by simp only [mul_assoc]
      _ = z₀ * (z₀ * w₀) * w₀ := by rw [hcz w₀]
      _ = (z₀ * z₀) * (w₀ * w₀) := by simp only [mul_assoc]
      _ = 1 := by rw [hz₀2, hw₀2, one_mul]
  have hsq : ∀ g, N g ≠ 0 → g * g = 1 := by
    intro g hg
    rcases hN g hg with rfl | rfl | rfl
    · exact hz₀2
    · exact hw₀2
    · exact hzwsq
  have hsupp : ∀ g, N g ≠ 0 → g ∈ S₀ := by
    intro g hg
    rcases hN g hg with rfl | rfl | rfl
    · exact hzS
    · exact hwS
    · exact S₀.mul_mem hzS hwS
  have hzw1 : z₀ * w₀ ≠ 1 := fun h1 => hzw (by
    rw [eq_inv_of_mul_eq_one_right h1, inv_eq_of_mul_eq_one_right hz₀2])
  have hzw2 : z₀ * w₀ ≠ z₀ := fun h1 => hw₀1 (by
    have := congrArg (z₀⁻¹ * ·) h1
    simpa using this)
  have hzw3 : z₀ * w₀ ≠ w₀ := fun h1 => hz₀1 (by
    have := congrArg (· * w₀⁻¹) h1
    simpa using this)
  have hN1 : N 1 = 0 := by
    by_contra hne
    rcases hN 1 hne with h1 | h1 | h1
    · exact hz₀1 h1.symm
    · exact hw₀1 h1.symm
    · exact hzw1 h1.symm
  have hsum : ∀ g, ∑ g', N g * N g' * (if g * g' * (z₀ * h ^ j) = 1 then (1 : ℂ) else 0) =
      if j = 0 then N g * N (g * z₀) else 0 := by
    intro g
    by_cases hg : N g = 0
    · simp [hg]
    have hginv : g⁻¹ = g := inv_eq_of_mul_eq_one_right (hsq g hg)
    rw [Finset.sum_eq_single (g * z₀)]
    · by_cases hj0 : j = 0
      · subst hj0
        rw [ite_eq_left rfl, ite_eq_left]
        · ring
        · rw [pow_zero, mul_one, ← mul_assoc g g z₀, hsq g hg, one_mul, hz₀2]
      · rw [ite_eq_right hj0, ite_eq_right]
        · ring
        intro h1
        have hgg : g * (g * z₀) * z₀ ∈ S₀ :=
          S₀.mul_mem (S₀.mul_mem (hsupp g hg) (S₀.mul_mem (hsupp g hg) hzS)) hzS
        have hmem : h ^ j ∈ S₀ := by
          have : h ^ j = (g * (g * z₀) * z₀)⁻¹ := by
            apply eq_inv_of_mul_eq_one_right
            rw [← h1]; group
          rw [this]; exact S₀.inv_mem hgg
        exact hj0 (Nat.eq_zero_of_dvd_of_lt ((hL.pow_mem_iff j).mp hmem) hj)
    · intro g' _ hne
      by_cases hg' : N g' = 0
      · simp [hg']
      rw [ite_eq_right]
      · ring
      intro h1
      apply hne
      have hj0 : j = 0 := by
        have hgg : g * g' * z₀ ∈ S₀ :=
          S₀.mul_mem (S₀.mul_mem (hsupp g hg) (hsupp g' hg')) hzS
        have hmem : h ^ j ∈ S₀ := by
          have : h ^ j = (g * g' * z₀)⁻¹ := by
            apply eq_inv_of_mul_eq_one_right
            rw [← h1]; group
          rw [this]; exact S₀.inv_mem hgg
        exact Nat.eq_zero_of_dvd_of_lt ((hL.pow_mem_iff j).mp hmem) hj
      subst hj0
      rw [pow_zero, mul_one] at h1
      calc g' = g⁻¹ * ((g * g' * z₀) * z₀) := by rw [mul_assoc (g * g'), hz₀2, mul_one]; group
        _ = g * z₀ := by rw [h1, one_mul, hginv]
    · intro h1; exact absurd (Finset.mem_univ _) h1
  rw [Finset.sum_congr rfl fun g _ => hsum g]
  by_cases hj0 : j = 0
  · simp only [hj0, ite_true]
    have hsub : ∑ g, N g * N (g * z₀) = ∑ g ∈ ({z₀, w₀, z₀ * w₀} : Finset L), N g * N (g * z₀) := by
      refine (Finset.sum_subset (Finset.subset_univ _) fun g _ hg => ?_).symm
      have : N g = 0 := by
        by_contra hne
        apply hg
        rcases hN g hne with rfl | rfl | rfl <;> simp
      rw [this, zero_mul]
    have hwz : w₀ * z₀ = z₀ * w₀ := hcz w₀
    have hzwz : z₀ * w₀ * z₀ = w₀ := by
      rw [mul_assoc, hwz, ← mul_assoc, hz₀2, one_mul]
    rw [hsub, Finset.sum_insert (by simp [Ne.symm hzw, Ne.symm hzw2]),
      Finset.sum_insert (by simp [Ne.symm hzw3]), Finset.sum_singleton, hz₀2, hN1, hwz, hNzw,
      hzwz, hNw]
    ring
  · simp only [hj0, ite_false, Finset.sum_const_zero]

end UnitaryFourByFive

variable {G : Type} [Group G] [Fintype G]

theorem sum_comp_eq_sum_fiber_card {X L : Type*} [Fintype L] [DecidableEq L] (s : Finset X)
    (π : X → L) (f : L → ℂ) :
    ∑ x ∈ s, f (π x) = ∑ g, ((s.filter fun x => π x = g).card : ℂ) * f g := by
  have : ∀ x ∈ s, f (π x) = ∑ g, if π x = g then f g else 0 := by
    intro x _
    rw [Finset.sum_ite_eq, ite_eq_left (Finset.mem_univ _)]
  rw [Finset.sum_congr rfl this, Finset.sum_comm]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_mul, Finset.sum_filter]
  refine Finset.sum_congr rfl fun x _ => ?_
  split_ifs <;> simp

theorem local_order_sum {z : G}
    (localBasis :
      FiniteIrreducibleCharacterBasis (Subgroup.centralizer (Subgroup.zpowers z : Set G)))
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (localPrincipal : localBasis.index)
    (hlocalPrincipal : (localBasis.representation localPrincipal).character = 1)
    {L : Type} [Group L] [Fintype L] {S₀ : Subgroup L} {h : L} (hL : UnitaryFourByFive S₀ h)
    (quotientBasis : FiniteIrreducibleCharacterBasis L)
    (π : Subgroup.centralizer (Subgroup.zpowers z : Set G) →* L) (hπ : Function.Surjective π)
    [Fintype π.ker] (hker : ¬ 2 ∣ Nat.card π.ker)
    (y : Subgroup.centralizer (Subgroup.zpowers z : Set G)) (hy : π y = h) {w₀ : L}
    (hz₀ : π (centralizerSelf z) ∈ (Subgroup.center S₀).map S₀.subtype)
    (hw₀ : w₀ ∈ (Subgroup.center S₀).map S₀.subtype)
    (hz₀2 : π (centralizerSelf z) * π (centralizerSelf z) = 1) (hw₀2 : w₀ * w₀ = 1)
    (hz₀1 : π (centralizerSelf z) ≠ 1) (hw₀1 : w₀ ≠ 1) (hzw : w₀ ≠ π (centralizerSelf z))
    (n : ℂ)
    (hN : ∀ g, ((Finset.univ.filter fun x : Subgroup.centralizer (Subgroup.zpowers z : Set G) =>
        IsConj (x : G) z ∧ π x = g).card : ℂ) ≠ 0 →
      g = π (centralizerSelf z) ∨ g = w₀ ∨ g = π (centralizerSelf z) * w₀)
    (hNz : ((Finset.univ.filter fun x : Subgroup.centralizer (Subgroup.zpowers z : Set G) =>
        IsConj (x : G) z ∧ π x = π (centralizerSelf z)).card : ℂ) = 1)
    (hNw : ((Finset.univ.filter fun x : Subgroup.centralizer (Subgroup.zpowers z : Set G) =>
        IsConj (x : G) z ∧ π x = w₀).card : ℂ) = n)
    (hNzw : ((Finset.univ.filter fun x : Subgroup.centralizer (Subgroup.zpowers z : Set G) =>
        IsConj (x : G) z ∧ π x = π (centralizerSelf z) * w₀).card : ℂ) = n)
    {j : ℕ} (hj : j < 5) :
    ∑ ψ ∈ coefficientBlock localBasis (localizedComplexIntegerRing ideal) localPrincipal,
      ((Nat.card (Subgroup.centralizer (Subgroup.zpowers z : Set G)) : ℂ)⁻¹ *
        ∑ x ∈ Finset.univ.filter (fun x : Subgroup.centralizer (Subgroup.zpowers z : Set G) =>
          IsConj (x : G) z), (localBasis.representation ψ).character x) ^ 2 *
        (localBasis.representation ψ).character (centralizerSelf z * y ^ j) /
          (localBasis.representation ψ).character 1 =
      if j = 0 then 2 * Nat.card L * n ^ 2 /
        (Nat.card (Subgroup.centralizer (Subgroup.zpowers z : Set G)) : ℂ) ^ 2 else 0 := by
  set X := Finset.univ.filter (fun x : Subgroup.centralizer (Subgroup.zpowers z : Set G) =>
    IsConj (x : G) z) with hX
  set c := (Nat.card (Subgroup.centralizer (Subgroup.zpowers z : Set G)) : ℂ) with hc
  set N : L → ℂ := fun g => ((Finset.univ.filter
    fun x : Subgroup.centralizer (Subgroup.zpowers z : Set G) =>
      IsConj (x : G) z ∧ π x = g).card : ℂ) with hNdef
  have hfiber : ∀ g, ((X.filter fun x => π x = g).card : ℂ) = N g := by
    intro g
    rw [hNdef, hX, Finset.filter_filter]
  rw [local_principal_block_eq localBasis ideal localPrincipal hlocalPrincipal hL quotientBasis
    π hπ hker, sum_normalSubgroupCharacterSupport_eq localBasis quotientBasis π hπ
    (fun ψ => (c⁻¹ * ∑ x ∈ X, ψ x) ^ 2 * ψ (centralizerSelf z * y ^ j) / ψ 1)]
  have hterm : ∀ θ : quotientBasis.index,
      (c⁻¹ * ∑ x ∈ X, ((quotientBasis.representation θ).character ∘ π) x) ^ 2 *
        ((quotientBasis.representation θ).character ∘ π) (centralizerSelf z * y ^ j) /
          ((quotientBasis.representation θ).character ∘ π) 1 =
      c⁻¹ ^ 2 * ((∑ g, N g * (quotientBasis.representation θ).character g) ^ 2 *
        (quotientBasis.representation θ).character (π (centralizerSelf z) * h ^ j) /
          (quotientBasis.representation θ).character 1) := by
    intro θ
    simp only [Function.comp_apply, map_mul, map_pow, hy, map_one]
    rw [sum_comp_eq_sum_fiber_card X π, Finset.sum_congr rfl fun g _ => by rw [hfiber g]]
    ring
  rw [Finset.sum_congr rfl fun θ _ => hterm θ, ← Finset.mul_sum,
    sum_central_weight_sq quotientBasis N (fun g hg => by
      rcases hN g hg with rfl | rfl | rfl
      · exact hL.center_le_center hz₀
      · exact hL.center_le_center hw₀
      · exact Subgroup.mul_mem _ (hL.center_le_center hz₀) (hL.center_le_center hw₀)),
    hL.pair_count hz₀ hw₀ hz₀2 hw₀2 hz₀1 hw₀1 hzw N n hN hNz hNw hNzw hj]
  have hcne : c ≠ 0 := by rw [hc]; exact Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  split_ifs
  · field_simp
  · simp

end CFSG.LyonsUnitaryFour
