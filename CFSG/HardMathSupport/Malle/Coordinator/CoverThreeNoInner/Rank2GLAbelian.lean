module

public import CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner.Rank2GLEigen
public import CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner.Rank2GLDefs

public section

namespace CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner

open scoped MatrixGroups

section Abelian

variable {F : Type} [Field F]

theorem noncube_field {a : Fˣ} (ha : ∀ c : Fˣ, a ≠ c ^ 3) (b : F) : b ^ 3 ≠ (a : F) := by
  intro h
  by_cases hb : b = 0
  · rw [hb] at h
    simp at h
    exact a.ne_zero h.symm
  · apply ha (Units.mk0 b hb)
    apply Units.ext
    simp [h]

theorem coe_pow_eq_scalar {x : GL (Fin 3) F} {a : Fˣ} (h : x ^ 3 = scal a) :
    (x : Matrix (Fin 3) (Fin 3) F) ^ 3 = Matrix.scalar (Fin 3) (a : F) := by
  rw [← Units.val_pow_eq_pow_val, h, coe_scal]

theorem abelian_cubes [Finite F] (h3 : 3 ∣ Nat.card F - 1) (A : Subgroup (GL (Fin 3) F))
    (hS : sc F ≤ A) (hcube : ∀ x ∈ A, x ^ 3 ∈ sc F)
    (hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hidx : ((sc F).subgroupOf A).index = 9) :
    ∀ x ∈ A, ∃ c : Fˣ, x ^ 3 = scal (c ^ 3) := by
  intro x hx
  by_contra hno
  push Not at hno
  obtain ⟨a, ha⟩ := mem_sc_iff.mp (hcube x hx)
  have hanc : ∀ c : Fˣ, a ≠ c ^ 3 := fun c hc => hno c (by rw [ha, hc])
  have hz : ∃ z ∈ A, ∀ k : Fin 3, z * x ^ (k : ℕ) ∉ sc F := by
    by_contra hcon
    push Not at hcon
    have hle := index_le_of_cover A ((sc F).subgroupOf A) (ι := Fin 3)
      (fun k => ⟨(x ^ (k : ℕ))⁻¹, A.inv_mem (A.pow_mem hx _)⟩) (by
        intro z
        obtain ⟨k, hk⟩ := hcon z.1 z.2
        refine ⟨k, ?_⟩
        rw [Subgroup.mem_subgroupOf]
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
        rw [hcomm _ (A.pow_mem hx _) _ z.2]
        exact hk)
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at hle
    omega
  obtain ⟨z, hzA, hzk⟩ := hz
  obtain ⟨b, hb⟩ := mem_sc_iff.mp (hcube z hzA)
  obtain ⟨k, d, hkd⟩ := exists_cube_mul_pow h3 hanc b
  set y : GL (Fin 3) F := z * x ^ (k : ℕ) * scal d⁻¹ with hy
  have hyA : y ∈ A := A.mul_mem (A.mul_mem hzA (A.pow_mem hx _)) (hS (scal_mem_sc _))
  have hy3 : y ^ 3 = 1 := by
    have c1 : Commute z (x ^ (k : ℕ)) := hcomm z hzA _ (A.pow_mem hx _)
    have c2 : Commute (z * x ^ (k : ℕ)) (scal d⁻¹) :=
      Subgroup.mem_center_iff.mp (sc_mem_center (scal_mem_sc _)) _
    rw [hy, c2.mul_pow, c1.mul_pow, hb, ← pow_mul, mul_comm, pow_mul, ha, ← map_pow, ← map_pow,
      ← map_mul, ← map_mul]
    rw [hkd, inv_pow, mul_inv_cancel, map_one]
  have hyn : y ∉ sc F := by
    intro hysc
    apply hzk k
    have : z * x ^ (k : ℕ) = y * scal d := by
      rw [hy, mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one]
    rw [this]
    exact (sc F).mul_mem hysc (scal_mem_sc d)
  obtain ⟨v, hv, ε, hyv⟩ := exists_eigenvector_of_pow_three h3 y hy3
  have hxy : (x : Matrix (Fin 3) (Fin 3) F) * (y : Matrix (Fin 3) (Fin 3) F) =
      (y : Matrix (Fin 3) (Fin 3) F) * (x : Matrix (Fin 3) (Fin 3) F) := by
    rw [← Units.val_mul, ← Units.val_mul, hcomm x hx y hyA]
  have hyscal := eq_scalar_of_commute_of_eigen (noncube_field hanc) _ _ (coe_pow_eq_scalar ha) hxy hv
    hyv
  have hε : ε ≠ 0 := by
    rintro rfl
    have := y.val_inv
    rw [hyscal] at this
    simp at this
  apply hyn
  rw [mem_sc_iff]
  refine ⟨Units.mk0 ε hε, Units.ext ?_⟩
  rw [coe_scal, hyscal]
  rfl

theorem mul_apply_diag_of_isDiag' {A B : Matrix (Fin 3) (Fin 3) F} (hA : A.IsDiag) (i : Fin 3) :
    (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro j _ hj
    rw [hA hj.symm, zero_mul]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

theorem mem_torusThree_of_diag_cube {h : GL (Fin 3) F}
    (hh : ∀ i j : Fin 3, i ≠ j → (h : Matrix (Fin 3) (Fin 3) F) i j = 0) {c : Fˣ}
    (h3 : h ^ 3 = scal (c ^ 3)) : h ∈ torusThree F := by
  have hdiag : (h : Matrix (Fin 3) (Fin 3) F).IsDiag := hh
  have hnz : ∀ i : Fin 3, (h : Matrix (Fin 3) (Fin 3) F) i i ≠ 0 := by
    intro i
    have h1 : (((h : Matrix (Fin 3) (Fin 3) F)) * ((h⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))
        i i = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_apply_eq]
    rw [mul_apply_diag_of_isDiag' hdiag] at h1
    exact left_ne_zero_of_mul_eq_one h1
  have hmat : (h : Matrix (Fin 3) (Fin 3) F) =
      Matrix.diagonal ![(h : Matrix (Fin 3) (Fin 3) F) 0 0, (h : Matrix (Fin 3) (Fin 3) F) 1 1,
        (h : Matrix (Fin 3) (Fin 3) F) 2 2] := by
    rw [← hdiag.diagonal_diag]
    congr 1
    ext k
    fin_cases k <;> simp [Matrix.diag]
  have hpow : (h : Matrix (Fin 3) (Fin 3) F) ^ 3 = Matrix.scalar (Fin 3) ((c : F) ^ 3) := by
    rw [← Units.val_pow_eq_pow_val, h3, coe_scal]
    simp
  rw [hmat, Matrix.diagonal_pow] at hpow
  have e0 := congrFun (congrFun hpow 0) 0
  have e1 := congrFun (congrFun hpow 1) 1
  have e2 := congrFun (congrFun hpow 2) 2
  simp [Matrix.scalar_apply] at e0 e1 e2
  change ∃ a b c : Fˣ, a ^ 3 = b ^ 3 ∧ b ^ 3 = c ^ 3 ∧ h = diagGL F a b c
  refine ⟨Units.mk0 _ (hnz 0), Units.mk0 _ (hnz 1), Units.mk0 _ (hnz 2), ?_, ?_, ?_⟩
  · apply Units.ext
    simp [e0, e1]
  · apply Units.ext
    simp [e1, e2]
  · apply Units.ext
    simp only [diagGL, Units.val_mk0]
    exact hmat

theorem abelian_torus [Finite F] (h3 : 3 ∣ Nat.card F - 1) (A : Subgroup (GL (Fin 3) F))
    (hS : sc F ≤ A) (hcube : ∀ x ∈ A, x ^ 3 ∈ sc F)
    (hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hidx : ((sc F).subgroupOf A).index = 9) :
    ∃ g : GL (Fin 3) F, A.map (MulAut.conj g).toMonoidHom ≤ torusThree F := by
  have hcubes := abelian_cubes h3 A hS hcube hcomm hidx
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_dvd (F := F) (m := 3) h3
  let E : Subgroup (GL (Fin 3) F) :=
    { carrier := {x | x ∈ A ∧ x ^ 3 = 1}
      mul_mem' := fun {u v} hu hv => ⟨A.mul_mem hu.1 hv.1, by
        have : Commute u v := hcomm u hu.1 v hv.1
        rw [this.mul_pow, hu.2, hv.2, mul_one]⟩
      one_mem' := ⟨A.one_mem, one_pow _⟩
      inv_mem' := fun {u} hu => ⟨A.inv_mem hu.1, by rw [inv_pow, hu.2, inv_one]⟩ }
  have hcommE : ∀ u ∈ E, ∀ v ∈ E, u * v = v * u := fun u hu v hv => hcomm u hu.1 v hv.1
  have hexpE : ∀ u ∈ E, u ^ 3 = 1 := fun u hu => hu.2
  obtain ⟨g, hg⟩ := CFSG.HardMathSupport.Malle.Coordinator.CoverThree.exists_conj_diagonal_of_pow_eq_one
    hζ E hcommE hexpE
  refine ⟨g, ?_⟩
  rintro _ ⟨x, hxA, rfl⟩
  obtain ⟨c, hc⟩ := hcubes x hxA
  have hxE : x * scal c⁻¹ ∈ E := by
    refine ⟨A.mul_mem hxA (hS (scal_mem_sc _)), ?_⟩
    have : Commute x (scal c⁻¹) := Subgroup.mem_center_iff.mp (sc_mem_center (scal_mem_sc _)) x
    rw [this.mul_pow, hc, ← map_pow, ← map_mul, inv_pow, mul_inv_cancel, map_one]
  have hdiag := hg _ hxE
  have hconj : (MulAut.conj g).toMonoidHom x = (g * (x * scal c⁻¹) * g⁻¹) * scal c := by
    have e : g * (x * scal c⁻¹) * g⁻¹ = (g * x * g⁻¹) * scal c⁻¹ := by
      calc g * (x * scal c⁻¹) * g⁻¹ = g * x * (scal c⁻¹ * g⁻¹) := by simp only [mul_assoc]
        _ = g * x * (g⁻¹ * scal c⁻¹) := by rw [Matrix.GeneralLinearGroup.scalar_commute]
        _ = (g * x * g⁻¹) * scal c⁻¹ := by simp only [mul_assoc]
    rw [e, mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one]
    rfl
  refine mem_torusThree_of_diag_cube (c := c) ?_ ?_
  · intro i j hij
    rw [hconj]
    rw [Units.val_mul, coe_scal, Matrix.scalar_apply, Matrix.mul_diagonal, hdiag i j hij, zero_mul]
  · rw [← map_pow, hc]
    show g * scal (c ^ 3) * g⁻¹ = scal (c ^ 3)
    rw [mul_assoc, Matrix.GeneralLinearGroup.scalar_commute (c ^ 3) g⁻¹, mul_inv_cancel_left]

end Abelian

end CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner
