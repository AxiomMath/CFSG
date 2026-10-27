module

public import CFSG.CGT.Stroth77.WeakType
public import CFSG.CGT.Stroth77.Arch76Lemma2Coord

public section

namespace CFSG.CGT.Stroth77

namespace StrothWeakTypeData

variable {S : Type*} [Group S] {B : Subgroup S} {τ : StrothTypeIndex}
  (D : StrothWeakTypeData B τ)

@[expose] def ofTorus (y : Torus τ.k) : S := ((Additive.toMul (D.e.symm y) : B) : S)

theorem ofTorus_mem (y : Torus τ.k) : D.ofTorus y ∈ B := (Additive.toMul (D.e.symm y)).2

theorem ofTorus_add (y y' : Torus τ.k) : D.ofTorus (y + y') = D.ofTorus y * D.ofTorus y' := by
  simp [ofTorus]

theorem ofTorus_zero : D.ofTorus 0 = 1 := by simp [ofTorus]

theorem ofTorus_neg (y : Torus τ.k) : D.ofTorus (-y) = (D.ofTorus y)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← ofTorus_add, neg_add_cancel, ofTorus_zero]

theorem ofTorus_nsmul (n : ℕ) (y : Torus τ.k) : D.ofTorus (n • y) = D.ofTorus y ^ n := by
  induction n with
  | zero => simp [ofTorus_zero]
  | succ n ih => rw [succ_nsmul, ofTorus_add, ih, pow_succ]

theorem ofTorus_e (x : B) : D.ofTorus (D.e (Additive.ofMul x)) = x := by simp [ofTorus]

theorem c_eq : (D.c : S) = D.ofTorus Torus.c := rfl
theorem a_eq : (D.a : S) = D.ofTorus Torus.a := rfl
theorem b_eq : (D.b : S) = D.ofTorus Torus.b := rfl

theorem conj_ofTorus {g : S} (hg : g ∈ Subgroup.normalizer B) {φ : Torus τ.k →+ Torus τ.k}
    (hconj : ∀ x : B, D.e (Additive.ofMul (conjBy hg x)) = φ (D.e (Additive.ofMul x)))
    (y : Torus τ.k) : g⁻¹ * D.ofTorus y * g = D.ofTorus (φ y) := by
  have h := D.conj_apply hg hconj y
  have h2 : conjBy hg (Additive.toMul (D.e.symm y)) = Additive.toMul (D.e.symm (φ y)) := by
    rw [← h]; simp
  have h3 := congrArg Subtype.val h2
  simpa [conjBy, ofTorus] using h3

end StrothWeakTypeData

theorem torus100_decomp : ∀ y : Torus (StrothTypeIndex.t100 1).k,
    y = (y 0).val • Torus.c + (y 1).val • Torus.a + (y 2).val • Torus.b := by
  decide +kernel

namespace StrothWeakTypeData

variable {S : Type*} [Group S] {B : Subgroup S} (D : StrothWeakTypeData B (.t100 1))

theorem closure_eq : B = Subgroup.closure {(D.c : S), (D.a : S)⁻¹, (D.b : S)⁻¹} := by
  apply le_antisymm
  · intro x hx
    have h := D.ofTorus_e ⟨x, hx⟩
    rw [torus100_decomp (D.e (Additive.ofMul ⟨x, hx⟩)), ofTorus_add, ofTorus_add, ofTorus_nsmul,
      ofTorus_nsmul, ofTorus_nsmul, ← c_eq, ← a_eq, ← b_eq] at h
    rw [← show ((⟨x, hx⟩ : B) : S) = x from rfl, ← h]
    have hc : (D.c : S) ∈ Subgroup.closure {(D.c : S), (D.a : S)⁻¹, (D.b : S)⁻¹} :=
      Subgroup.subset_closure (by simp)
    have ha : (D.a : S) ∈ Subgroup.closure {(D.c : S), (D.a : S)⁻¹, (D.b : S)⁻¹} := by
      rw [← inv_inv (D.a : S)]; exact inv_mem (Subgroup.subset_closure (by simp))
    have hb : (D.b : S) ∈ Subgroup.closure {(D.c : S), (D.a : S)⁻¹, (D.b : S)⁻¹} := by
      rw [← inv_inv (D.b : S)]; exact inv_mem (Subgroup.subset_closure (by simp))
    exact mul_mem (mul_mem (pow_mem hc _) (pow_mem ha _)) (pow_mem hb _)
  · rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    exacts [D.c.2, inv_mem D.a.2, inv_mem D.b.2]

include D in
theorem card_eq_32 : Nat.card B = 32 := by rw [D.card]; rfl

theorem pow_two_c : (D.c : S) ^ 2 = 1 := by
  rw [c_eq, ← ofTorus_nsmul, show (2 • Torus.c : Torus (StrothTypeIndex.t100 1).k) = 0 by decide,
    ofTorus_zero]

theorem pow_four_a_inv : ((D.a : S)⁻¹) ^ 4 = 1 := by
  rw [a_eq, ← ofTorus_neg, ← ofTorus_nsmul,
    show (4 • -Torus.a : Torus (StrothTypeIndex.t100 1).k) = 0 by decide, ofTorus_zero]

theorem pow_four_b_inv : ((D.b : S)⁻¹) ^ 4 = 1 := by
  rw [b_eq, ← ofTorus_neg, ← ofTorus_nsmul,
    show (4 • -Torus.b : Torus (StrothTypeIndex.t100 1).k) = 0 by decide, ofTorus_zero]

theorem uv_conj_c : D.uv⁻¹ * (D.c : S) * D.uv = (D.c : S) * ((D.a : S)⁻¹ * (D.b : S)⁻¹) ^ 2 := by
  rw [c_eq, a_eq, b_eq, D.conj_ofTorus D.uv_mem D.uv_conj, ← ofTorus_neg, ← ofTorus_neg,
    ← ofTorus_add, ← ofTorus_nsmul, ← ofTorus_add]
  congr 1; decide

theorem uv_conj_a_inv : D.uv⁻¹ * (D.a : S)⁻¹ * D.uv = (D.a : S)⁻¹ * ((D.b : S)⁻¹) ^ 2 := by
  rw [a_eq, b_eq, ← ofTorus_neg, ← ofTorus_neg, D.conj_ofTorus D.uv_mem D.uv_conj,
    ← ofTorus_nsmul, ← ofTorus_add]
  congr 1; decide

theorem uv_conj_b_inv : D.uv⁻¹ * (D.b : S)⁻¹ * D.uv = (D.b : S)⁻¹ * ((D.a : S)⁻¹) ^ 2 := by
  rw [a_eq, b_eq, ← ofTorus_neg, ← ofTorus_neg, D.conj_ofTorus D.uv_mem D.uv_conj,
    ← ofTorus_nsmul, ← ofTorus_add]
  congr 1; decide

theorem t_conj_c : D.t⁻¹ * (D.c : S) * D.t = (D.c : S) * ((D.a : S)⁻¹) ^ 2 := by
  rw [c_eq, a_eq, D.conj_ofTorus D.t_mem D.t_conj, ← ofTorus_neg, ← ofTorus_nsmul, ← ofTorus_add]
  congr 1; decide

theorem t_conj_a_inv : D.t⁻¹ * (D.a : S)⁻¹ * D.t = ((D.a : S)⁻¹)⁻¹ := by
  rw [a_eq, ← ofTorus_neg, ← ofTorus_neg, D.conj_ofTorus D.t_mem D.t_conj]
  congr 1; decide

theorem t_conj_b_inv : D.t⁻¹ * (D.b : S)⁻¹ * D.t = ((D.a : S)⁻¹) ^ 2 * ((D.b : S)⁻¹)⁻¹ := by
  rw [a_eq, b_eq, ← ofTorus_neg, ← ofTorus_neg, ← ofTorus_neg, D.conj_ofTorus D.t_mem D.t_conj,
    ← ofTorus_nsmul, ← ofTorus_add]
  congr 1; decide

theorem u_conj_c : D.u⁻¹ * (D.c : S) * D.u = (D.c : S) := by
  rw [c_eq, D.conj_ofTorus D.u_mem D.u_conj]
  congr 1; decide

theorem u_conj_a_inv : D.u⁻¹ * (D.a : S)⁻¹ * D.u = (D.b : S)⁻¹ := by
  rw [a_eq, b_eq, ← ofTorus_neg, ← ofTorus_neg, D.conj_ofTorus D.u_mem D.u_conj]
  congr 1; decide

theorem ρ_conj_c : D.ρ⁻¹ * (D.c : S) * D.ρ = (D.c : S) := by
  rw [c_eq, D.conj_ofTorus D.ρ_mem D.ρ_conj]
  congr 1; decide

theorem ρ_conj_a_inv : D.ρ⁻¹ * (D.a : S)⁻¹ * D.ρ = (D.b : S)⁻¹ := by
  rw [a_eq, b_eq, ← ofTorus_neg, ← ofTorus_neg, D.conj_ofTorus D.ρ_mem D.ρ_conj]
  congr 1; decide

theorem ρ_conj_b_inv : D.ρ⁻¹ * (D.b : S)⁻¹ * D.ρ = ((D.a : S)⁻¹)⁻¹ * ((D.b : S)⁻¹)⁻¹ := by
  rw [a_eq, b_eq, ← ofTorus_neg, ← ofTorus_neg, ← ofTorus_neg, ← ofTorus_neg,
    D.conj_ofTorus D.ρ_mem D.ρ_conj, ← ofTorus_add]
  congr 1; decide

theorem u_inv_t_u : D.u⁻¹ * D.t * D.u = D.uv * D.t := by
  calc D.u⁻¹ * D.t * D.u = D.u⁻¹ * (D.t * D.u) := by group
    _ = D.u⁻¹ * (D.u * D.uv * D.t) := by rw [D.t_u]
    _ = D.uv * D.t := by group

theorem ρ_inv_uv_ρ : D.ρ⁻¹ * D.uv * D.ρ = D.t := by
  rw [mul_assoc, D.uv_rho]; group

theorem ρ_inv_t_ρ : D.ρ⁻¹ * D.t * D.ρ = D.uv * D.t := by
  rw [mul_assoc, D.t_rho]; group

theorem u_inv_ρ_u : D.u⁻¹ * D.ρ * D.u = D.ρ⁻¹ := by
  have hu : D.u⁻¹ = D.u := inv_eq_of_mul_eq_one_right D.u_sq
  rw [hu, eq_inv_iff_mul_eq_one]
  exact D.u_rho

@[expose] def toConfig : Arch76.Config S where
  A := B
  w := D.c
  x := (D.a : S)⁻¹
  y := (D.b : S)⁻¹
  uv := D.uv
  t := D.t
  u := D.u
  ρ := D.ρ
  hA := D.closure_eq
  hAc := D.isMulCommutative
  hAcard := D.card_eq_32
  hw := D.pow_two_c
  hx := D.pow_four_a_inv
  hy := D.pow_four_b_inv
  huv_w := D.uv_conj_c
  huv_x := D.uv_conj_a_inv
  huv_y := D.uv_conj_b_inv
  ht_w := D.t_conj_c
  ht_x := D.t_conj_a_inv
  ht_y := D.t_conj_b_inv
  hu_w := D.u_conj_c
  hu_x := D.u_conj_a_inv
  hρ_w := D.ρ_conj_c
  hρ_x := D.ρ_conj_a_inv
  hρ_y := D.ρ_conj_b_inv
  huv2 := by rw [pow_two]; exact D.uv_sq
  ht2 := by rw [pow_two]; exact D.t_sq
  hu2 := by rw [pow_two]; exact D.u_sq
  huvt := D.uv_comm_t
  huvu := D.uv_comm_u
  htu := D.u_inv_t_u
  hρuv := D.ρ_inv_uv_ρ
  hρt := D.ρ_inv_t_ρ
  hρu := D.u_inv_ρ_u

@[simp] theorem toConfig_A : D.toConfig.A = B := rfl
@[simp] theorem toConfig_w : D.toConfig.w = (D.c : S) := rfl
@[simp] theorem toConfig_x : D.toConfig.x = (D.a : S)⁻¹ := rfl
@[simp] theorem toConfig_y : D.toConfig.y = (D.b : S)⁻¹ := rfl
@[simp] theorem toConfig_uv : D.toConfig.uv = D.uv := rfl
@[simp] theorem toConfig_t : D.toConfig.t = D.t := rfl
@[simp] theorem toConfig_u : D.toConfig.u = D.u := rfl
@[simp] theorem toConfig_ρ : D.toConfig.ρ = D.ρ := rfl

end StrothWeakTypeData

end CFSG.CGT.Stroth77
