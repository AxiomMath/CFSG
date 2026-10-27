module

public import CFSG.CharacterTheory.Semidihedral.Model
public import CFSG.Open.Catalog

public section

namespace CFSG.Semidihedral

open CFSG.Open

instance modulus_neZero (n : ℕ) : NeZero (modulus n) :=
  ⟨pow_ne_zero _ (by decide)⟩

abbrev r (n : ℕ) : SemidihedralGroup n := PresentedGroup.of 0

abbrev s (n : ℕ) : SemidihedralGroup n := PresentedGroup.of 1

theorem r_modulus (n : ℕ) : r n ^ modulus n = 1 := by
  have h := PresentedGroup.one_of_mem
    (rels := semidihedralRels n) (x := FreeGroup.of 0 ^ modulus n)
    (by simp [semidihedralRels, modulus])
  simpa only [map_pow, PresentedGroup.of, r] using h

theorem s_sq (n : ℕ) : s n ^ 2 = 1 := by
  have h := PresentedGroup.one_of_mem
    (rels := semidihedralRels n) (x := FreeGroup.of 1 ^ 2)
    (by simp [semidihedralRels])
  simpa only [map_pow, PresentedGroup.of, s] using h

theorem s_conj_r (n : ℕ) :
    s n * r n * (s n)⁻¹ = r n ^ (2 ^ (n - 2) - 1) := by
  have h := PresentedGroup.mk_eq_mk_of_mul_inv_mem
    (rels := semidihedralRels n)
    (x := FreeGroup.of 1 * FreeGroup.of 0 * (FreeGroup.of 1)⁻¹)
    (y := FreeGroup.of 0 ^ (2 ^ (n - 2) - 1))
    (by simp [semidihedralRels])
  simpa only [map_mul, map_inv, map_pow, PresentedGroup.of, r, s] using h

@[expose] def toModel (n : ℕ) (hn : 3 ≤ n) : SemidihedralGroup n →* Model n hn :=
  PresentedGroup.toGroup (f := ![modelR n hn, modelS n hn]) (by
    intro w hw
    simp only [semidihedralRels, Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl
    · simpa only [map_pow, FreeGroup.lift_apply_of, Matrix.cons_val_zero, modulus] using
        modelR_modulus n hn
    · simpa only [map_pow, FreeGroup.lift_apply_of, Matrix.cons_val_one,
        Matrix.cons_val_zero] using modelS_sq n hn
    · simp only [map_mul, map_inv, map_pow, FreeGroup.lift_apply_of,
        Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [modelS_conj_modelR, mul_inv_cancel])

@[simp] theorem toModel_r (n : ℕ) (hn : 3 ≤ n) :
    toModel n hn (r n) = modelR n hn := by
  simp [toModel, r]

@[simp] theorem toModel_s (n : ℕ) (hn : 3 ≤ n) :
    toModel n hn (s n) = modelS n hn := by
  simp [toModel, s]

@[expose] def cyclicPowHom {G : Type*} [Group G]
    (d : ℕ) [NeZero d] (g : G) (hg : g ^ d = 1) : Cyclic d →* G where
  toFun x := g ^ x.toAdd.val
  map_one' := by simp
  map_mul' x y := by
    simp only [toAdd_mul, ZMod.val_add]
    rw [← pow_eq_pow_mod _ hg, pow_add]

@[simp] theorem cyclicPowHom_one {G : Type*} [Group G]
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) (g : G) (hg : g ^ d = 1) :
    cyclicPowHom d g hg (Multiplicative.ofAdd 1) = g := by
  simp [cyclicPowHom, ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt hd]

theorem modulus_two_le {n : ℕ} (hn : 2 ≤ n) : 2 ≤ modulus n := by
  have hhalf : 1 ≤ half n := Nat.succ_le_of_lt (pow_pos (by decide) _)
  rw [modulus_eq_two_mul_half hn]
  omega

@[expose] def rotationHom (n : ℕ) : Cyclic (modulus n) →* SemidihedralGroup n :=
  cyclicPowHom (modulus n) (r n) (r_modulus n)

@[expose] def reflectionHom (n : ℕ) : Cyclic 2 →* SemidihedralGroup n :=
  cyclicPowHom 2 (s n) (s_sq n)

@[simp] theorem rotationHom_one (n : ℕ) (hn : 2 ≤ n) :
    rotationHom n (Multiplicative.ofAdd 1) = r n :=
  cyclicPowHom_one _ (modulus_two_le hn) _ _

@[simp] theorem reflectionHom_one (n : ℕ) :
    reflectionHom n (Multiplicative.ofAdd 1) = s n :=
  cyclicPowHom_one 2 (by decide) _ _

theorem rotationHom_twistAut (n : ℕ) (hn : 3 ≤ n)
    (x : Cyclic (modulus n)) :
    rotationHom n (twistAut n hn x) =
      s n * rotationHom n x * (s n)⁻¹ := by
  have hcast : Multiplicative.ofAdd
      (twist n * x.toAdd) = x ^ (2 ^ (n - 2) - 1) := by
    apply Multiplicative.toAdd.injective
    change twist n * x.toAdd = (2 ^ (n - 2) - 1) • x.toAdd
    rw [twist_eq_natCast, nsmul_eq_mul]
  change rotationHom n (Multiplicative.ofAdd (twist n * x.toAdd)) = _
  rw [hcast, map_pow]
  change (r n ^ x.toAdd.val) ^ (2 ^ (n - 2) - 1) =
    s n * r n ^ x.toAdd.val * (s n)⁻¹
  calc
    (r n ^ x.toAdd.val) ^ (2 ^ (n - 2) - 1) =
        (r n ^ (2 ^ (n - 2) - 1)) ^ x.toAdd.val := by
      rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    _ = (s n * r n * (s n)⁻¹) ^ x.toAdd.val := by rw [s_conj_r]
    _ = s n * r n ^ x.toAdd.val * (s n)⁻¹ := by
      simpa only [MulAut.conj_apply] using (map_pow (MulAut.conj (s n)) (r n) x.toAdd.val).symm

theorem toModel_rotationHom (n : ℕ) (hn : 3 ≤ n)
    (x : Cyclic (modulus n)) :
    toModel n hn (rotationHom n x) = SemidirectProduct.inl x := by
  change toModel n hn (r n ^ x.toAdd.val) = SemidirectProduct.inl x
  rw [map_pow, toModel_r, modelR, ← map_pow]
  apply SemidirectProduct.inl_injective.eq_iff.mpr
  apply Multiplicative.toAdd.injective
  change x.toAdd.val • (1 : ZMod (modulus n)) = x.toAdd
  simpa only [nsmul_eq_mul, mul_one] using ZMod.natCast_zmod_val x.toAdd

theorem toModel_reflectionHom (n : ℕ) (hn : 3 ≤ n)
    (x : Cyclic 2) :
    toModel n hn (reflectionHom n x) = SemidirectProduct.inr x := by
  change toModel n hn (s n ^ x.toAdd.val) = SemidirectProduct.inr x
  rw [map_pow, toModel_s, modelS, ← map_pow]
  apply SemidirectProduct.inr_injective.eq_iff.mpr
  apply Multiplicative.toAdd.injective
  change x.toAdd.val • (1 : ZMod 2) = x.toAdd
  simpa only [nsmul_eq_mul, mul_one] using ZMod.natCast_zmod_val x.toAdd

theorem rotation_reflection_compatible (n : ℕ) (hn : 3 ≤ n)
    (e : Cyclic 2) :
    (rotationHom n).comp (action n hn e).toMonoidHom =
      (MulAut.conj (reflectionHom n e)).toMonoidHom.comp (rotationHom n) := by
  have hcases : e = Multiplicative.ofAdd 0 ∨ e = Multiplicative.ofAdd 1 := by
    exact (show ∀ e : Cyclic 2,
      e = Multiplicative.ofAdd 0 ∨ e = Multiplicative.ofAdd 1 by decide) e
  rcases hcases with rfl | rfl
  · apply MonoidHom.ext
    intro x
    simp
  · apply MonoidHom.ext
    intro x
    simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, action_one,
      reflectionHom_one, MulAut.conj_apply] using rotationHom_twistAut n hn x

@[expose] def fromModel (n : ℕ) (hn : 3 ≤ n) : Model n hn →* SemidihedralGroup n :=
  SemidirectProduct.lift (rotationHom n) (reflectionHom n)
    (rotation_reflection_compatible n hn)

@[simp] theorem fromModel_modelR (n : ℕ) (hn : 3 ≤ n) :
    fromModel n hn (modelR n hn) = r n := by
  simp [fromModel, modelR, rotationHom_one n (by omega)]

@[simp] theorem fromModel_modelS (n : ℕ) (hn : 3 ≤ n) :
    fromModel n hn (modelS n hn) = s n := by simp [fromModel, modelS]

theorem fromModel_comp_toModel (n : ℕ) (hn : 3 ≤ n) :
    (fromModel n hn).comp (toModel n hn) = MonoidHom.id _ := by
  apply PresentedGroup.ext
  intro i
  fin_cases i <;> simp

theorem toModel_comp_fromModel (n : ℕ) (hn : 3 ≤ n) :
    (toModel n hn).comp (fromModel n hn) = MonoidHom.id _ := by
  apply MonoidHom.ext
  intro x
  change toModel n hn (rotationHom n x.left * reflectionHom n x.right) = x
  rw [map_mul, toModel_rotationHom, toModel_reflectionHom,
    SemidirectProduct.inl_left_mul_inr_right]

@[expose] def presentationEquivModel (n : ℕ) (hn : 3 ≤ n) :
    SemidihedralGroup n ≃* Model n hn :=
  MonoidHom.toMulEquiv (toModel n hn) (fromModel n hn)
    (fromModel_comp_toModel n hn) (toModel_comp_fromModel n hn)

@[simp] theorem presentationEquivModel_r (n : ℕ) (hn : 3 ≤ n) :
    presentationEquivModel n hn (r n) = modelR n hn := toModel_r n hn

@[simp] theorem presentationEquivModel_s (n : ℕ) (hn : 3 ≤ n) :
    presentationEquivModel n hn (s n) = modelS n hn := toModel_s n hn

@[simp] theorem presentationEquivModel_symm_modelR (n : ℕ) (hn : 3 ≤ n) :
    (presentationEquivModel n hn).symm (modelR n hn) = r n := fromModel_modelR n hn

@[simp] theorem presentationEquivModel_symm_modelS (n : ℕ) (hn : 3 ≤ n) :
    (presentationEquivModel n hn).symm (modelS n hn) = s n := fromModel_modelS n hn

end CFSG.Semidihedral
