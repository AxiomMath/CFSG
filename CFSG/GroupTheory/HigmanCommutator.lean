module

public import CFSG.Timmesfeld.Bridge.RootStructR2Higman

public section

namespace CFSG

open scoped commutatorElement MatrixGroups
open Matrix

variable {Q : Type*} [Group Q] {N : Subgroup Q} [N.Normal]
variable {K : Type*} [Field K] [Finite K] [CharP K 2]
variable {Γ : Type*} [Group Γ]

theorem commute_of_natural_central_extension
    (hNc : N ≤ Subgroup.center Q) (hK : 2 < Nat.card K)
    (act : Γ →* MulAut Q) (hactN : ∀ γ, ∀ n ∈ N, act γ n ∈ N)
    (π : Γ →* SL(2, K)) (hπ : Function.Surjective π)
    (φA : Additive (Q ⧸ N) ≃+ (Fin 2 → K))
    (hφA : ∀ γ x, φA (Additive.ofMul (QuotientGroup.mk (act γ x) : Q ⧸ N)) =
      ((π γ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) *ᵥ
        φA (Additive.ofMul (QuotientGroup.mk x)))
    (φB : Additive N ≃+ (Fin 2 → K))
    (hφB : ∀ γ (n : N), φB (Additive.ofMul ⟨act γ n, hactN γ n n.2⟩) =
      ((π γ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) *ᵥ φB (Additive.ofMul n)) :
    ∀ x y : Q, x * y = y * x := by
  classical
  have hcomm : ∀ a b : Q ⧸ N, a * b = b * a := by
    intro a b
    apply φA.injective
    change φA (Additive.ofMul (a * b)) = φA (Additive.ofMul (b * a))
    rw [ofMul_mul, ofMul_mul, map_add, map_add, add_comm]
  have hcommN : ∀ x y : Q, ⁅x, y⁆ ∈ N := by
    intro x y
    refine (QuotientGroup.eq_one_iff (N := N) (x := ⁅x, y⁆)).mp ?_
    rw [← QuotientGroup.coe_mk']
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (hcomm _ _)
  have hcl : ∀ a b : Q, ⁅a, b⁆ ∈ Subgroup.center Q := fun a b => hNc (hcommN a b)
  have hcancel_left : ∀ x y z : Q, z ∈ N → ⁅x * z, y⁆ = ⁅x, y⁆ := by
    intro x y z hz
    have hzy : z * y = y * z := (Subgroup.mem_center_iff.mp (hNc hz) y).symm
    rw [commutatorElement_def, commutatorElement_def, _root_.mul_inv_rev]
    calc x * z * y * (z⁻¹ * x⁻¹) * y⁻¹
        = x * (z * y) * z⁻¹ * x⁻¹ * y⁻¹ := by group
      _ = x * (y * z) * z⁻¹ * x⁻¹ * y⁻¹ := by rw [hzy]
      _ = x * y * x⁻¹ * y⁻¹ := by group
  have hcancel_right : ∀ x y z : Q, z ∈ N → ⁅x, y * z⁆ = ⁅x, y⁆ := by
    intro x y z hz
    have hzx : z * x⁻¹ = x⁻¹ * z := (Subgroup.mem_center_iff.mp (hNc hz) x⁻¹).symm
    rw [commutatorElement_def, commutatorElement_def, _root_.mul_inv_rev]
    calc x * (y * z) * x⁻¹ * (z⁻¹ * y⁻¹)
        = x * y * (z * x⁻¹) * z⁻¹ * y⁻¹ := by group
      _ = x * y * (x⁻¹ * z) * z⁻¹ * y⁻¹ := by rw [hzx]
      _ = x * y * x⁻¹ * y⁻¹ := by group
  have hmul_left : ∀ x x' y : Q, ⁅x * x', y⁆ = ⁅x, y⁆ * ⁅x', y⁆ := by
    intro x x' y
    rw [commutatorElement_mul_left_eq_conj_mul]
    have hconj : x * ⁅x', y⁆ * x⁻¹ = ⁅x', y⁆ := by
      have h : x * ⁅x', y⁆ = ⁅x', y⁆ * x :=
        Subgroup.mem_center_iff.mp (hcl x' y) x
      rw [h, mul_assoc, mul_inv_cancel, mul_one]
    rw [hconj]
    exact Subgroup.mem_center_iff.mp (hcl x y) ⁅x', y⁆
  have hmul_right : ∀ x y y' : Q, ⁅x, y * y'⁆ = ⁅x, y⁆ * ⁅x, y'⁆ := by
    intro x y y'
    rw [commutatorElement_mul_right_eq_mul_conj]
    have hconj : y * ⁅x, y'⁆ = ⁅x, y'⁆ * y :=
      Subgroup.mem_center_iff.mp (hcl x y') y
    calc ⁅x, y⁆ * y * ⁅x, y'⁆ * y⁻¹
        = ⁅x, y⁆ * (y * ⁅x, y'⁆) * y⁻¹ := by simp only [mul_assoc]
      _ = ⁅x, y⁆ * (⁅x, y'⁆ * y) * y⁻¹ := by rw [hconj]
      _ = ⁅x, y⁆ * ⁅x, y'⁆ := by simp only [mul_assoc, mul_inv_cancel, mul_one]
  let B : Q ⧸ N → Q ⧸ N → N := fun u v =>
    Quotient.liftOn₂' u v (fun x y => (⟨⁅x, y⁆, hcommN x y⟩ : N)) (by
      intro a b a' b' ha hb
      have ha' : a⁻¹ * a' ∈ N := QuotientGroup.leftRel_apply.mp ha
      have hb' : b⁻¹ * b' ∈ N := QuotientGroup.leftRel_apply.mp hb
      have e1 : a' = a * (a⁻¹ * a') := by rw [mul_inv_cancel_left]
      have e2 : b' = b * (b⁻¹ * b') := by rw [mul_inv_cancel_left]
      apply Subtype.ext
      show ⁅a, b⁆ = ⁅a', b'⁆
      rw [e1, e2, hcancel_right (a * (a⁻¹ * a')) b (b⁻¹ * b') hb',
        hcancel_left a b (a⁻¹ * a') ha'])
  have hB_mk : ∀ x y : Q, B (QuotientGroup.mk x) (QuotientGroup.mk y) =
      (⟨⁅x, y⁆, hcommN x y⟩ : N) := fun x y => rfl
  have hB_left : ∀ x x' y : Q,
      B (QuotientGroup.mk (x * x')) (QuotientGroup.mk y) =
        B (QuotientGroup.mk x) (QuotientGroup.mk y) *
          B (QuotientGroup.mk x') (QuotientGroup.mk y) := by
    intro x x' y
    rw [hB_mk, hB_mk, hB_mk]
    exact Subtype.ext (hmul_left x x' y)
  have hB_right : ∀ x y y' : Q,
      B (QuotientGroup.mk x) (QuotientGroup.mk (y * y')) =
        B (QuotientGroup.mk x) (QuotientGroup.mk y) *
          B (QuotientGroup.mk x) (QuotientGroup.mk y') := by
    intro x y y'
    rw [hB_mk, hB_mk, hB_mk]
    exact Subtype.ext (hmul_right x y y')
  let cAdd : Additive (Q ⧸ N) → Additive (Q ⧸ N) → Additive N := fun u v =>
    Additive.ofMul (B (Additive.toMul u) (Additive.toMul v))
  have hsurj : ∀ m : Additive (Q ⧸ N), ∃ x : Q,
      m = Additive.ofMul (QuotientGroup.mk x) := by
    intro m
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (Additive.toMul m)
    exact ⟨x, by rw [← ofMul_toMul m, hx]⟩
  have hAdd_left : ∀ u u' v : Additive (Q ⧸ N),
      cAdd (u + u') v = cAdd u v + cAdd u' v := by
    intro u u' v
    obtain ⟨x, rfl⟩ := hsurj u
    obtain ⟨x', rfl⟩ := hsurj u'
    obtain ⟨y, rfl⟩ := hsurj v
    change Additive.ofMul (B (Additive.toMul (Additive.ofMul (QuotientGroup.mk x) +
      Additive.ofMul (QuotientGroup.mk x')))
      (Additive.toMul (Additive.ofMul (QuotientGroup.mk y)))) =
      Additive.ofMul (B (QuotientGroup.mk x) (QuotientGroup.mk y)) +
        Additive.ofMul (B (QuotientGroup.mk x') (QuotientGroup.mk y))
    rw [← ofMul_mul, toMul_ofMul, ← QuotientGroup.mk_mul, toMul_ofMul, hB_left, ofMul_mul]
  have hAdd_right : ∀ u v v' : Additive (Q ⧸ N),
      cAdd u (v + v') = cAdd u v + cAdd u v' := by
    intro u v v'
    obtain ⟨x, rfl⟩ := hsurj u
    obtain ⟨y, rfl⟩ := hsurj v
    obtain ⟨y', rfl⟩ := hsurj v'
    change Additive.ofMul (B (Additive.toMul (Additive.ofMul (QuotientGroup.mk x)))
      (Additive.toMul (Additive.ofMul (QuotientGroup.mk y) +
        Additive.ofMul (QuotientGroup.mk y')))) =
      Additive.ofMul (B (QuotientGroup.mk x) (QuotientGroup.mk y)) +
        Additive.ofMul (B (QuotientGroup.mk x) (QuotientGroup.mk y'))
    rw [← ofMul_mul, toMul_ofMul, ← QuotientGroup.mk_mul, toMul_ofMul, hB_right, ofMul_mul]
  have hB_act : ∀ (γ : Γ) (x y : Q),
      B (QuotientGroup.mk (act γ x)) (QuotientGroup.mk (act γ y)) =
        ⟨act γ (B (QuotientGroup.mk x) (QuotientGroup.mk y) : Q),
          hactN γ _ (B (QuotientGroup.mk x) (QuotientGroup.mk y)).2⟩ := by
    intro γ x y
    rw [hB_mk, hB_mk]
    apply Subtype.ext
    show ⁅act γ x, act γ y⁆ = act γ ⁅x, y⁆
    exact (map_commutatorElement (act γ) x y).symm
  let β : (Fin 2 → K) → (Fin 2 → K) → (Fin 2 → K) := fun v w =>
    φB (cAdd (φA.symm v) (φA.symm w))
  have hcAdd_mk : ∀ x y : Q,
      cAdd (Additive.ofMul (QuotientGroup.mk x))
        (Additive.ofMul (QuotientGroup.mk y)) =
      Additive.ofMul (B (QuotientGroup.mk x) (QuotientGroup.mk y)) := by
    intro x y
    rfl
  have hβ_mk : ∀ x y : Q, β (φA (Additive.ofMul (QuotientGroup.mk x)))
      (φA (Additive.ofMul (QuotientGroup.mk y))) =
      φB (Additive.ofMul (B (QuotientGroup.mk x) (QuotientGroup.mk y))) := by
    intro x y
    change φB (cAdd (φA.symm (φA (Additive.ofMul (QuotientGroup.mk x))))
      (φA.symm (φA (Additive.ofMul (QuotientGroup.mk y))))) = _
    rw [AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply]
    rfl
  have hβ_left : ∀ v v' w, β (v + v') w = β v w + β v' w := by
    intro v v' w
    change φB (cAdd (φA.symm (v + v')) (φA.symm w)) = _
    rw [map_add φA.symm, hAdd_left, map_add]
  have hβ_right : ∀ v w w', β v (w + w') = β v w + β v w' := by
    intro v w w'
    change φB (cAdd (φA.symm v) (φA.symm (w + w'))) = _
    rw [map_add φA.symm, hAdd_right, map_add]
  have hφA_symm : ∀ (γ : Γ) (x : Q),
      φA.symm (((π γ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) *ᵥ
          φA (Additive.ofMul (QuotientGroup.mk x))) =
        Additive.ofMul (QuotientGroup.mk (act γ x)) := by
    intro γ x
    apply φA.injective
    rw [AddEquiv.apply_symm_apply, hφA]
  have hβ_eq : ∀ (g : SL(2, K)) v w,
      β (((g : Matrix (Fin 2) (Fin 2) K) *ᵥ v))
        (((g : Matrix (Fin 2) (Fin 2) K) *ᵥ w)) =
      ((g : Matrix (Fin 2) (Fin 2) K) *ᵥ β v w) := by
    intro g v w
    obtain ⟨γ, rfl⟩ := hπ g
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (Additive.toMul (φA.symm v))
    obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (Additive.toMul (φA.symm w))
    have hv : φA (Additive.ofMul (QuotientGroup.mk x)) = v := by
      rw [hx, ofMul_toMul, AddEquiv.apply_symm_apply]
    have hw : φA (Additive.ofMul (QuotientGroup.mk y)) = w := by
      rw [hy, ofMul_toMul, AddEquiv.apply_symm_apply]
    rw [← hv, ← hw]
    dsimp only [β, cAdd]
    rw [hφA_symm γ x, hφA_symm γ y]
    simp only [toMul_ofMul, AddEquiv.symm_apply_apply]
    rw [hB_act]
    exact hφB γ (B (QuotientGroup.mk x) (QuotientGroup.mk y))
  obtain ⟨t₀, ht₀, ht₁⟩ := CFSG.Timmesfeld.Bridge.Higman.exists_ne_zero_ne_one hK
  have hβ_zero := CFSG.Timmesfeld.Bridge.Higman.bilinear_eq_zero ht₀ ht₁ β
    hβ_left hβ_right hβ_eq
  intro x y
  have hBxy : B (QuotientGroup.mk x) (QuotientGroup.mk y) = 1 := by
    have hβxy : β (φA (Additive.ofMul (QuotientGroup.mk x)))
        (φA (Additive.ofMul (QuotientGroup.mk y))) =
        φB (Additive.ofMul (B (QuotientGroup.mk x) (QuotientGroup.mk y))) := hβ_mk x y
    have h1 : φB (Additive.ofMul (B (QuotientGroup.mk x) (QuotientGroup.mk y))) = 0 := by
      rw [← hβxy]
      exact hβ_zero _ _
    have h2 : Additive.ofMul (B (QuotientGroup.mk x) (QuotientGroup.mk y)) = 0 :=
      φB.injective (by simpa using h1)
    simpa using congrArg Additive.toMul h2
  have hcomm1 : ⁅x, y⁆ = 1 := by
    have h := congrArg Subtype.val (hB_mk x y)
    rw [hBxy] at h
    simpa using h.symm
  exact commutatorElement_eq_one_iff_mul_comm.mp hcomm1

end CFSG

end
