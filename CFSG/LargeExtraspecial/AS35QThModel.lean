module

public import CFSG.Fischer.Classification.Unitary.Basic

public section

namespace CFSG.LargeExtraspecial.AS35QTh

open Matrix CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary
  CFSG.Fischer.Classification.Unitary
open CFSG.Blueprint.Fischer (K)

theorem conjTr_mul_self_comm {A : Matrix (Fin 3) (Fin 3) K} (hA : conjTr frob A * A = 1) :
    A * conjTr frob A = 1 :=
  mul_eq_one_comm.mp hA

@[expose] noncomputable def GU3 : Subgroup (GL (Fin 3) K) where
  carrier := {A | conjTr frob (A : Matrix (Fin 3) (Fin 3) K) * A = 1}
  mul_mem' {A B} hA hB := by
    change conjTr frob ((A : Matrix (Fin 3) (Fin 3) K) * (B : Matrix (Fin 3) (Fin 3) K)) *
      ((A : Matrix (Fin 3) (Fin 3) K) * (B : Matrix (Fin 3) (Fin 3) K)) = 1
    change conjTr frob (A : Matrix (Fin 3) (Fin 3) K) * A = 1 at hA
    change conjTr frob (B : Matrix (Fin 3) (Fin 3) K) * B = 1 at hB
    calc conjTr frob ((A : Matrix (Fin 3) (Fin 3) K) * (B : Matrix (Fin 3) (Fin 3) K)) *
          ((A : Matrix (Fin 3) (Fin 3) K) * (B : Matrix (Fin 3) (Fin 3) K)) =
        conjTr frob (B : Matrix (Fin 3) (Fin 3) K) *
          (conjTr frob (A : Matrix (Fin 3) (Fin 3) K) * A) * B := by
          rw [conjTr_mul]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hA, Matrix.mul_one, hB]
  one_mem' := by
    change conjTr frob ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * _ = 1
    rw [Units.val_one, conjTr_one, Matrix.one_mul]
  inv_mem' {A} hA := by
    change conjTr frob (A : Matrix (Fin 3) (Fin 3) K) * A = 1 at hA
    change conjTr frob ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * _ = 1
    have h1 : ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        conjTr frob (A : Matrix (Fin 3) (Fin 3) K) := by
      rw [← Matrix.mul_one ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K),
        ← conjTr_mul_self_comm hA, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel,
        Units.val_one, Matrix.one_mul]
    rw [h1]
    have h2 : conjTr frob (conjTr frob (A : Matrix (Fin 3) (Fin 3) K)) = A := by
      ext i j
      simp only [conjTr, Matrix.transpose_apply, Matrix.map_apply]
      exact frob_frob _
    rw [h2, conjTr_mul_self_comm hA]

theorem mem_GU3 {A : GL (Fin 3) K} :
    A ∈ GU3 ↔ conjTr frob (A : Matrix (Fin 3) (Fin 3) K) * A = 1 := Iff.rfl

noncomputable abbrev gm (A : GU3) : Matrix (Fin 3) (Fin 3) K :=
  ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)

noncomputable abbrev gv (A : GU3) (v : Fin 3 → K) : Fin 3 → K := gm A *ᵥ v

theorem gv_mul (A B : GU3) (v : Fin 3 → K) : gv (A * B) v = gv A (gv B v) := by
  simp only [gv, gm, Subgroup.coe_mul, Units.val_mul, Matrix.mulVec_mulVec]

theorem gv_one (v : Fin 3 → K) : gv 1 v = v := by
  simp only [gv, gm, OneMemClass.coe_one, Units.val_one, Matrix.one_mulVec]

theorem gv_zero (A : GU3) : gv A 0 = 0 := Matrix.mulVec_zero _

theorem herm_gv (A : GU3) (v w : Fin 3 → K) : herm frob (gv A v) (gv A w) = herm frob v w := by
  rw [gv, herm_mulVec, mem_GU3.1 A.2, Matrix.one_mulVec]

theorem gv_gv_inv (A : GU3) (v : Fin 3 → K) : gv A (gv A⁻¹ v) = v := by
  rw [← gv_mul, mul_inv_cancel, gv_one]

noncomputable abbrev toK : ZMod 2 →+* K := ZMod.castHom (dvd_refl 2) K

@[expose] noncomputable def tr2 (c : K) : ZMod 2 := by
  classical
  exact if c + frob c = 0 then 0 else 1

theorem toK_tr2 (c : K) : toK (tr2 c) = c + frob c := by
  classical
  unfold tr2
  split_ifs with h0
  · rw [map_zero, h0]
  · rw [map_one]
    exact ((add_frob_eq_zero_or_one c).resolve_left h0).symm

theorem toK_injective : Function.Injective toK := (toK).injective

theorem tr2_add (c d : K) : tr2 (c + d) = tr2 c + tr2 d := by
  apply toK_injective
  rw [map_add, toK_tr2, toK_tr2, toK_tr2, map_add]
  ring

theorem frob_toK (ε : ZMod 2) : frob (toK ε) = toK ε := by
  fin_cases ε
  · change frob (toK 0) = toK 0
    rw [map_zero, map_zero]
  · change frob (toK 1) = toK 1
    rw [map_one, map_one]

@[expose] noncomputable def beta (a b : Fin 3 → K) : ZMod 2 := tr2 (ω * herm frob a b)

abbrev Model : Type := ZMod 2 × (Fin 3 → K) × GU3

@[expose] noncomputable def mulM (x y : Model) : Model :=
  (x.1 + y.1 + beta x.2.1 (gv x.2.2 y.2.1), x.2.1 + gv x.2.2 y.2.1, x.2.2 * y.2.2)

theorem nonempty_mulEquiv_of_model {H₁ H₂ : Type*} [Group H₁] [Group H₂] (f₁ : Model → H₁)
    (f₂ : Model → H₂) (hb₁ : Function.Bijective f₁) (hb₂ : Function.Bijective f₂)
    (hm₁ : ∀ x y, f₁ (mulM x y) = f₁ x * f₁ y) (hm₂ : ∀ x y, f₂ (mulM x y) = f₂ x * f₂ y) :
    Nonempty (H₁ ≃* H₂) := by
  set e₁ := Equiv.ofBijective f₁ hb₁
  set e₂ := Equiv.ofBijective f₂ hb₂
  refine ⟨{ toEquiv := e₁.symm.trans e₂, map_mul' := fun h h' => ?_ }⟩
  obtain ⟨x, rfl⟩ := hb₁.2 h
  obtain ⟨y, rfl⟩ := hb₁.2 h'
  have hx : e₁.symm (f₁ x) = x := e₁.symm_apply_apply x
  have hy : e₁.symm (f₁ y) = y := e₁.symm_apply_apply y
  have hxy : e₁.symm (f₁ x * f₁ y) = mulM x y := by
    rw [← hm₁]
    exact e₁.symm_apply_apply _
  change e₂ (e₁.symm (f₁ x * f₁ y)) = e₂ (e₁.symm (f₁ x)) * e₂ (e₁.symm (f₁ y))
  rw [hx, hy, hxy]
  exact hm₂ x y

end CFSG.LargeExtraspecial.AS35QTh
