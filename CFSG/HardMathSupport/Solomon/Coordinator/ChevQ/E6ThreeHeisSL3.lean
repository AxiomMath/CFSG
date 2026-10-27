module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeHeisOuter
public import CFSG.LieType.SeitzGeneration.Basic
public import Mathlib.Algebra.Order.Ring.Star

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open Matrix CFSG.LieType.SeitzGeneration
open scoped commutatorElement

section Plane

variable {K : Type*} [Field K]

@[expose] def conjSL : GL (Fin 3) K →* MulAut (SpecialLinearGroup (Fin 3) K) where
  toFun g :=
    { toFun := conjUnit g
      invFun := conjUnit g⁻¹
      left_inv := fun h => by simpa using conjUnit_conjUnit_inv g⁻¹ h
      right_inv := fun h => conjUnit_conjUnit_inv g h
      map_mul' := map_mul _ }
  map_one' := by
    refine MulEquiv.ext fun h => ?_
    apply Subtype.ext
    simp [conjUnit_coe]
  map_mul' g g' := by
    refine MulEquiv.ext fun h => ?_
    apply Subtype.ext
    simp [conjUnit_coe, Matrix.mul_assoc]

theorem conjSL_apply (g : GL (Fin 3) K) (h : SpecialLinearGroup (Fin 3) K) :
    conjSL g h = conjUnit g h := rfl

theorem conjSL_toGL (g : SpecialLinearGroup (Fin 3) K) :
    conjSL (SpecialLinearGroup.toGL g) = MulAut.conj g := by
  refine MulEquiv.ext fun h => ?_
  apply Subtype.ext
  rw [conjSL_apply, conjUnit_coe, MulAut.conj_apply, ← map_inv]
  rfl

end Plane

section Generation

variable {K : Type*} [Field K]

theorem exists_isPrimitiveRoot_three [Finite K] (h3 : 3 ∣ Nat.card K - 1) :
    ∃ ω : K, IsPrimitiveRoot ω 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdvd : 3 ∣ Nat.card Kˣ := by rwa [Nat.card_units]
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 hdvd
  exact ⟨(x : K), IsPrimitiveRoot.coe_units_iff.mpr (hx ▸ IsPrimitiveRoot.orderOf x)⟩

theorem four_lt_card_of_three_dvd [Finite K] (h3 : 3 ∣ Nat.card K - 1) (h4 : Nat.card K ≠ 4) :
    4 < Nat.card K := by
  have h1 : 1 < Nat.card K := Finite.one_lt_card
  obtain ⟨k, hk⟩ := h3
  omega

end Generation

section GLPair

variable {K : Type*} [Field K]

theorem conjSL_apply_eq_self_iff {g : GL (Fin 3) K} {k : SpecialLinearGroup (Fin 3) K} :
    conjSL g k = k ↔ (g : Matrix (Fin 3) (Fin 3) K) * k = k * g := by
  have hgg : ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * g = 1 := Units.inv_mul g
  have hgg' : (g : Matrix (Fin 3) (Fin 3) K) * ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
    1 := Units.mul_inv g
  rw [conjSL_apply]
  constructor
  · intro h
    have h' : (g : Matrix (Fin 3) (Fin 3) K) * k *
        ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = k := by
      have := congrArg (fun a : SpecialLinearGroup (Fin 3) K => (a : Matrix (Fin 3) (Fin 3) K)) h
      simpa [conjUnit_coe] using this
    calc (g : Matrix (Fin 3) (Fin 3) K) * k
        = (g : Matrix (Fin 3) (Fin 3) K) * k * (((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
            g) := by rw [hgg, Matrix.mul_one]
      _ = ((g : Matrix (Fin 3) (Fin 3) K) * k * ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))
            * g := by simp only [Matrix.mul_assoc]
      _ = k * g := by rw [h']
  · intro h
    apply Subtype.ext
    rw [conjUnit_coe]
    calc (g : Matrix (Fin 3) (Fin 3) K) * k * ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
        = (k * g) * ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by rw [h]
      _ = k := by rw [Matrix.mul_assoc, hgg', Matrix.mul_one]

theorem conjSL_scalar (u : Kˣ) : conjSL (Matrix.GeneralLinearGroup.scalar (Fin 3) u) = 1 :=
  MulEquiv.ext fun h => conjSL_apply_eq_self_iff.2 (by
    rw [Matrix.GeneralLinearGroup.coe_scalar]
    exact Matrix.scalar_commute _ (fun r => Commute.all _ r) _)

theorem mul_ne_mul_comm_of_smul {x y : GL (Fin 3) K} {ω : K} (hω1 : ω ≠ 1)
    (hyx : (y : Matrix (Fin 3) (Fin 3) K) * x = ω • ((x : Matrix (Fin 3) (Fin 3) K) * y)) :
    (y : Matrix (Fin 3) (Fin 3) K) * x ≠ x * y := by
  intro h
  rw [h] at hyx
  have h1 : (1 - ω) • ((x : Matrix (Fin 3) (Fin 3) K) * y) = 0 := by
    rw [sub_smul, one_smul, ← hyx, sub_self]
  have hxy : ((x : Matrix (Fin 3) (Fin 3) K) * y) *
      (((x * y)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
    have := Units.mul_inv (x * y)
    rwa [Units.val_mul] at this
  have h2 : (1 - ω) • (1 : Matrix (Fin 3) (Fin 3) K) = 0 := by
    have h3 := congrArg
      (fun M => M * (((x * y)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) h1
    simp only [Matrix.smul_mul, hxy, Matrix.zero_mul] at h3
    exact h3
  have h4 := congrFun (congrFun h2 (0 : Fin 3)) (0 : Fin 3)
  simp at h4
  exact hω1 (sub_eq_zero.1 h4).symm

theorem conjSL_ne_one_of_not_commute {g h : GL (Fin 3) K}
    (hgh : (g : Matrix (Fin 3) (Fin 3) K) * h ≠ h * g) : conjSL g ≠ 1 := by
  intro h1
  apply hgh
  have hcomm : ∀ t : Matrix.TransvectionStruct (Fin 3) K,
      Commute t.toMatrix (g : Matrix (Fin 3) (Fin 3) K) := by
    intro t
    have h2 : conjSL g t.toSpecialLinearGroup = t.toSpecialLinearGroup := by rw [h1]; rfl
    exact (conjSL_apply_eq_self_iff.1 h2).symm
  obtain ⟨c, hc⟩ := Matrix.mem_range_scalar_of_commute_transvectionStruct hcomm
  rw [← hc]
  exact Matrix.scalar_commute (n := Fin 3) c (fun r => Commute.all _ r) _

theorem mem_planeClosure_of_commute_gl {g : GL (Fin 3) K}
    {A : Subgroup (MulAut (SpecialLinearGroup (Fin 3) K))} (hg : conjSL g ∈ A)
    (hg1 : conjSL g ≠ 1) {k : SpecialLinearGroup (Fin 3) K}
    (hk : (g : Matrix (Fin 3) (Fin 3) K) * k = k * g) : k ∈ planeClosure A :=
  mem_planeClosure_of_fixed hg hg1 (conjSL_apply_eq_self_iff.2 hk)

theorem ne_zero_of_pow_three_eq_smul {x : GL (Fin 3) K} {α : K}
    (hx3 : (x : Matrix (Fin 3) (Fin 3) K) ^ 3 = α • 1) : α ≠ 0 := by
  rintro rfl
  rw [zero_smul] at hx3
  apply Units.ne_zero (x ^ 3)
  rw [Units.val_pow_eq_pow_val]
  exact hx3

theorem three_dvd_card_sub_one [Finite K] {ω : K} (hω : IsPrimitiveRoot ω 3) :
    3 ∣ Nat.card K - 1 := by
  have hω0 : ω ≠ 0 := hω.ne_zero (by norm_num)
  have hu : IsPrimitiveRoot (Units.mk0 ω hω0) 3 :=
    IsPrimitiveRoot.coe_units_iff.1 (by simpa using hω)
  have h1 : orderOf (Units.mk0 ω hω0) ∣ Nat.card Kˣ := orderOf_dvd_natCard _
  rw [← hu.eq_orderOf, Nat.card_units] at h1
  exact h1

theorem exists_cube_line [Finite K] (h3 : 3 ∣ Nat.card K - 1) {α β : K} (hα : α ≠ 0)
    (hβ : β ≠ 0) :
    (∃ s : K, s ≠ 0 ∧ s ^ 3 = β) ∨ (∃ s : K, s ≠ 0 ∧ s ^ 3 = α) ∨
      (∃ s : K, s ≠ 0 ∧ s ^ 3 = α * β) ∨ (∃ s : K, s ≠ 0 ∧ s ^ 3 = α * β ^ 2) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set d := (Nat.card K - 1) / 3 with hd
  have hκ : ∀ t : K, t ≠ 0 → (t ^ d) ^ 3 = 1 := fun t ht => by
    rw [← pow_mul, mul_comm, hd, Nat.mul_div_cancel' h3]
    have := Fintype.ofFinite K
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.pow_card_sub_one_eq_one t ht
  by_cases hβ1 : β ^ d = 1
  · exact Or.inl (exists_pow_eq_of_pow_div_eq_one h3 hβ hβ1)
  · have hω : IsPrimitiveRoot (β ^ d) 3 := by
      have := orderOf_eq_prime (hκ β hβ) hβ1
      rw [← this]
      exact IsPrimitiveRoot.orderOf _
    obtain ⟨i, hi, hiα⟩ := hω.eq_pow_of_pow_eq_one (hκ α hα)
    interval_cases i
    · exact Or.inr (Or.inl (exists_pow_eq_of_pow_div_eq_one h3 hα (by rw [← hiα]; simp)))
    · refine Or.inr (Or.inr (Or.inr (exists_pow_eq_of_pow_div_eq_one h3
        (mul_ne_zero hα (pow_ne_zero 2 hβ)) ?_)))
      have h1 : (α * β ^ 2) ^ d = α ^ d * (β ^ d) ^ 2 := by ring
      rw [h1, ← hiα]
      linear_combination hκ β hβ
    · refine Or.inr (Or.inr (Or.inl (exists_pow_eq_of_pow_div_eq_one h3
        (mul_ne_zero hα hβ) ?_)))
      have h1 : (α * β) ^ d = α ^ d * β ^ d := by ring
      rw [h1, ← hiα]
      linear_combination hκ β hβ

theorem conjUnit_diagSL_mem_planeClosure {y P : GL (Fin 3) K} {ξ ω : K}
    (hyP : (y : Matrix (Fin 3) (Fin 3) K) * P = P * diagonal ![ξ, ξ * ω, ξ * ω ^ 2])
    {A : Subgroup (MulAut (SpecialLinearGroup (Fin 3) K))} (hy : conjSL y ∈ A)
    (hy1 : conjSL y ≠ 1) (a b d : K) (h : a * b * d = 1) :
    conjUnit P (diagSL a b d h) ∈ planeClosure A := by
  refine mem_planeClosure_of_commute_gl hy hy1 (commute_conjUnit_of_intertwine hyP ?_).symm
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagSL, mul_comm]

theorem planeGen_of_heisPair_normal [Finite K] {ω α : K} (hω : IsPrimitiveRoot ω 3)
    (hq : 4 < Nat.card K) {x y : GL (Fin 3) K}
    (hyx : (y : Matrix (Fin 3) (Fin 3) K) * x = ω • ((x : Matrix (Fin 3) (Fin 3) K) * y))
    (hy3 : (y : Matrix (Fin 3) (Fin 3) K) ^ 3 = 1)
    (hx3 : (x : Matrix (Fin 3) (Fin 3) K) ^ 3 = α • 1)
    {A : Subgroup (MulAut (SpecialLinearGroup (Fin 3) K))} (hx : conjSL x ∈ A)
    (hy : conjSL y ∈ A) : PlaneGen A := by
  have hω3 : ω ^ 3 = 1 := hω.pow_eq_one
  have hω1 : ω ≠ 1 := hω.ne_one (by norm_num)
  have hωq : ω ^ 2 + ω + 1 = 0 := by
    have h1 : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by linear_combination hω3
    exact (mul_eq_zero.1 h1).resolve_left (sub_ne_zero.2 hω1)
  have hx1 : conjSL x ≠ 1 :=
    conjSL_ne_one_of_not_commute (mul_ne_mul_comm_of_smul hω1 hyx).symm
  have hy1 : conjSL y ≠ 1 := conjSL_ne_one_of_not_commute (mul_ne_mul_comm_of_smul hω1 hyx)
  by_cases hcube : ∃ μ : K, μ ^ 3 = α
  · obtain ⟨μ, hμ⟩ := hcube
    have hμ0 : μ ≠ 0 := by
      rintro rfl
      apply ne_zero_of_pow_three_eq_smul hx3
      rw [← hμ]
      norm_num
    obtain ⟨u, hu⟩ : ∃ u : Kˣ, (u : K) = μ⁻¹ := ⟨Units.mk0 _ (inv_ne_zero hμ0), rfl⟩
    set x₁ : GL (Fin 3) K := Matrix.GeneralLinearGroup.scalar (Fin 3) u * x with hx₁
    have hx₁c : (x₁ : Matrix (Fin 3) (Fin 3) K) = (u : K) • (x : Matrix (Fin 3) (Fin 3) K) := by
      rw [hx₁, coe_scalarGL_mul]
    have hyx₁ : (y : Matrix (Fin 3) (Fin 3) K) * x₁ =
        ω • ((x₁ : Matrix (Fin 3) (Fin 3) K) * y) := by
      rw [hx₁c, Matrix.mul_smul, hyx, Matrix.smul_mul, smul_comm]
    have hx₁3 : (x₁ : Matrix (Fin 3) (Fin 3) K) ^ 3 = (1 : K) • 1 := by
      rw [hx₁c, smul_pow, hx3, smul_smul, hu, ← hμ, ← mul_pow, inv_mul_cancel₀ hμ0, one_pow]
    have hx₁A : conjSL x₁ ∈ A := by
      rw [hx₁, map_mul, conjSL_scalar, one_mul]
      exact hx
    have hx₁1 : conjSL x₁ ≠ 1 := by
      rw [hx₁, map_mul, conjSL_scalar, one_mul]
      exact hx1
    obtain ⟨P, ξ, -, hyP, hx₁P⟩ := exists_heisenberg_basis_gl hω hyx₁ hy3 hx₁3
    refine eq_top_of_comap_conjUnit' P (eq_top_of_torus_circ (K := (planeClosure A).comap
      (conjUnit P)) (fun a b d h => ?_) (fun a b d h => ?_) hωq hω1 hq)
    · exact conjUnit_diagSL_mem_planeClosure hyP hy hy1 a b d h
    · refine mem_planeClosure_of_commute_gl hx₁A hx₁1
        (commute_conjUnit_of_intertwine hx₁P ?_).symm
      have := congrArg Subtype.val (circSL_mul_shiftSL a b d h)
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul] at this
      exact this
  · obtain ⟨P, ξ, -, hyP, hxP⟩ := exists_heisenberg_basis_gl hω hyx hy3 hx3
    refine eq_top_of_comap_conjUnit' P (eq_top_of_torus_centralizer_noncube
      (K := (planeClosure A).comap (conjUnit P)) hωq hω1 hcube hq (fun a b d h => ?_)
      (fun k hk => ?_))
    · exact conjUnit_diagSL_mem_planeClosure hyP hy hy1 a b d h
    · exact mem_planeClosure_of_commute_gl hx hx1 (commute_conjUnit_of_intertwine hxP hk).symm

theorem planeGen_of_heisPair_line [Finite K] {ω α s : K} (hω : IsPrimitiveRoot ω 3)
    (hq : 4 < Nat.card K) (hs : s ≠ 0) {g₁ g₂ : GL (Fin 3) K}
    (h21 : (g₂ : Matrix (Fin 3) (Fin 3) K) * g₁ = ω • ((g₁ : Matrix (Fin 3) (Fin 3) K) * g₂))
    (hg₂ : (g₂ : Matrix (Fin 3) (Fin 3) K) ^ 3 = (s ^ 3) • 1)
    (hg₁ : (g₁ : Matrix (Fin 3) (Fin 3) K) ^ 3 = α • 1)
    {A : Subgroup (MulAut (SpecialLinearGroup (Fin 3) K))} (h₁ : conjSL g₁ ∈ A)
    (h₂ : conjSL g₂ ∈ A) : PlaneGen A := by
  obtain ⟨u, hu⟩ : ∃ u : Kˣ, (u : K) = s⁻¹ := ⟨Units.mk0 _ (inv_ne_zero hs), rfl⟩
  set y : GL (Fin 3) K := Matrix.GeneralLinearGroup.scalar (Fin 3) u * g₂ with hy
  have hyc : (y : Matrix (Fin 3) (Fin 3) K) = (u : K) • (g₂ : Matrix (Fin 3) (Fin 3) K) := by
    rw [hy, coe_scalarGL_mul]
  refine planeGen_of_heisPair_normal hω hq (x := g₁) (y := y) ?_ ?_ hg₁ h₁ ?_
  · rw [hyc, Matrix.smul_mul, Matrix.mul_smul, h21]
    exact smul_comm _ _ _
  · rw [hyc, smul_pow, hg₂, smul_smul, hu, ← mul_pow, inv_mul_cancel₀ hs, one_pow, one_smul]
  · rw [hy, map_mul, conjSL_scalar, one_mul]
    exact h₂

theorem heis_step {x y : GL (Fin 3) K} {c : K}
    (h : (y : Matrix (Fin 3) (Fin 3) K) * x = c • ((x : Matrix (Fin 3) (Fin 3) K) * y)) :
    (y : Matrix (Fin 3) (Fin 3) K) * ((x * y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      c • (((x * y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * y) := by
  rw [Units.val_mul, ← Matrix.mul_assoc, h, Matrix.smul_mul]

theorem heis_line {x y : GL (Fin 3) K} {c : K}
    (h : (y : Matrix (Fin 3) (Fin 3) K) * x = c • ((x : Matrix (Fin 3) (Fin 3) K) * y)) :
    ((x * y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * x =
      c • ((x : Matrix (Fin 3) (Fin 3) K) *
        ((x * y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) := by
  rw [Units.val_mul, Matrix.mul_assoc, h, Matrix.mul_smul]

theorem mul_pow_three_gl {x y : GL (Fin 3) K} {c : K} (hc : c ^ 3 = 1)
    (h : (y : Matrix (Fin 3) (Fin 3) K) * x = c • ((x : Matrix (Fin 3) (Fin 3) K) * y)) :
    ((x * y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ^ 3 =
      (x : Matrix (Fin 3) (Fin 3) K) ^ 3 * (y : Matrix (Fin 3) (Fin 3) K) ^ 3 := by
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at hc
  have hcu : (Units.mk0 c hc0) ^ 3 = 1 := Units.ext (by simpa using hc)
  have hGL : y * x = Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.mk0 c hc0) * (x * y) := by
    apply Units.ext
    rw [coe_scalarGL_mul, Units.val_mul, Units.val_mul]
    exact h
  have hw3 : (Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.mk0 c hc0)) ^ 3 = 1 := by
    rw [← map_pow, hcu, map_one]
  have h3 := mul_pow_prime_eq Nat.prime_three (by norm_num) (fun g => commute_scalarGL _ g) hGL hw3
  have h4 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) h3
  simpa [Units.val_mul, Units.val_pow_eq_pow_val] using h4

theorem planeGen_of_heisPair [Finite K] {ω : K} (hω : IsPrimitiveRoot ω 3) (hq : 4 < Nat.card K)
    {x y : GL (Fin 3) K}
    (hxy : (x : Matrix (Fin 3) (Fin 3) K) * y = ω • ((y : Matrix (Fin 3) (Fin 3) K) * x))
    (hx3 : ∃ α : K, (x : Matrix (Fin 3) (Fin 3) K) ^ 3 = α • 1)
    (hy3 : ∃ β : K, (y : Matrix (Fin 3) (Fin 3) K) ^ 3 = β • 1)
    {A : Subgroup (MulAut (SpecialLinearGroup (Fin 3) K))} (hx : conjSL x ∈ A)
    (hy : conjSL y ∈ A) : PlaneGen A := by
  obtain ⟨α, hα⟩ := hx3
  obtain ⟨β, hβ⟩ := hy3
  have hα0 := ne_zero_of_pow_three_eq_smul hα
  have hβ0 := ne_zero_of_pow_three_eq_smul hβ
  have hω3 : ω ^ 3 = 1 := hω.pow_eq_one
  have hωc : IsPrimitiveRoot (ω ^ 2) 3 := hω.pow_of_coprime 2 (by norm_num)
  have hc3 : (ω ^ 2) ^ 3 = 1 := hωc.pow_eq_one
  have hyx : (y : Matrix (Fin 3) (Fin 3) K) * x =
      (ω ^ 2) • ((x : Matrix (Fin 3) (Fin 3) K) * y) := by
    have h1 : ω ^ 2 * ω = 1 := by linear_combination hω3
    rw [hxy, smul_smul, h1, one_smul]
  have hxyA : conjSL (x * y) ∈ A := by
    rw [map_mul]
    exact A.mul_mem hx hy
  rcases exists_cube_line (three_dvd_card_sub_one hω) hα0 hβ0 with
    ⟨s, hs0, hs⟩ | ⟨s, hs0, hs⟩ | ⟨s, hs0, hs⟩ | ⟨s, hs0, hs⟩
  · exact planeGen_of_heisPair_line hωc hq hs0 hyx (by rw [hs]; exact hβ) hα hx hy
  · exact planeGen_of_heisPair_line hω hq hs0 hxy (by rw [hs]; exact hα) hβ hy hx
  · refine planeGen_of_heisPair_line hωc hq hs0 (g₁ := x) (g₂ := x * y) (heis_line hyx) ?_ hα hx
      hxyA
    rw [mul_pow_three_gl hc3 hyx, hα, hβ, smul_mul_smul_comm, Matrix.one_mul, hs]
  · have hxy3 : ((x * y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ^ 3 = (α * β) • 1 := by
      rw [mul_pow_three_gl hc3 hyx, hα, hβ, smul_mul_smul_comm, Matrix.one_mul]
    refine planeGen_of_heisPair_line hωc hq hs0 (g₁ := x * y) (g₂ := x * y * y)
      (heis_line (heis_step hyx)) ?_ hxy3 hxyA ?_
    · rw [mul_pow_three_gl hc3 (heis_step hyx), hxy3, hβ, smul_mul_smul_comm, Matrix.one_mul, hs]
      congr 1
      ring
    · rw [map_mul]
      exact A.mul_mem hxyA hy

end GLPair

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

end
