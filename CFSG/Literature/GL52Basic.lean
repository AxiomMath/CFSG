module

public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Combinatorics.Matroid.Init

public section

namespace CFSG.Literature.GL52

open Matrix

abbrev G := GL (Fin 5) (ZMod 2)

abbrev V := Fin 5 → ZMod 2

@[expose] def vecEquiv : V ≃ Fin 32 :=
  (Equiv.refl (Fin 5 → Fin 2)).trans finFunctionFinEquiv

theorem vecEquiv_zero : vecEquiv 0 = 0 := by
  apply Fin.ext
  change ((finFunctionFinEquiv (fun _ : Fin 5 => (0 : Fin 2)) : Fin (2 ^ 5)) : ℕ) = 0
  rw [finFunctionFinEquiv_apply]
  simp

theorem vecEquiv_eq_zero_iff (v : V) : vecEquiv v = 0 ↔ v = 0 := by
  rw [← vecEquiv_zero, vecEquiv.apply_eq_iff_eq]

@[expose] def ptVec (i : Fin 31) : V := vecEquiv.symm i.succ

theorem ptVec_ne_zero (i : Fin 31) : ptVec i ≠ 0 := by
  intro h
  have : vecEquiv (ptVec i) = 0 := (vecEquiv_eq_zero_iff _).2 h
  rw [ptVec, Equiv.apply_symm_apply] at this
  exact Fin.succ_ne_zero i this

@[expose] def vecPt (v : V) (hv : v ≠ 0) : Fin 31 :=
  (vecEquiv v).pred (by rwa [Ne, vecEquiv_eq_zero_iff])

theorem ptVec_vecPt (v : V) (hv : v ≠ 0) : ptVec (vecPt v hv) = v := by
  rw [ptVec, vecPt, Fin.succ_pred, Equiv.symm_apply_apply]

theorem vecPt_ptVec (i : Fin 31) (h : ptVec i ≠ 0) : vecPt (ptVec i) h = i := by
  apply Fin.succ_injective
  rw [vecPt, Fin.succ_pred, ptVec, Equiv.apply_symm_apply]

@[expose] def ptEquiv : Fin 31 ≃ {v : V // v ≠ 0} where
  toFun i := ⟨ptVec i, ptVec_ne_zero i⟩
  invFun v := vecPt v.1 v.2
  left_inv i := vecPt_ptVec i _
  right_inv v := Subtype.ext (ptVec_vecPt v.1 v.2)

theorem mulVec_ne_zero (g : G) {v : V} (hv : v ≠ 0) :
    (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ v ≠ 0 := by
  intro h
  apply hv
  have : ((g⁻¹ : G) : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ ((g : Matrix _ _ _) *ᵥ v) = v := by
    rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
  rw [← this, h, mulVec_zero]

@[expose] def glPermFun (g : G) : Equiv.Perm (Fin 31) where
  toFun i := vecPt ((g : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ ptVec i)
    (mulVec_ne_zero g (ptVec_ne_zero i))
  invFun i := vecPt (((g⁻¹ : G) : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ ptVec i)
    (mulVec_ne_zero g⁻¹ (ptVec_ne_zero i))
  left_inv i := by
    simp only [ptVec_vecPt, mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      one_mulVec, vecPt_ptVec]
  right_inv i := by
    simp only [ptVec_vecPt, mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      one_mulVec, vecPt_ptVec]

theorem ptVec_glPermFun (g : G) (i : Fin 31) :
    ptVec (glPermFun g i) = (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ ptVec i :=
  ptVec_vecPt _ (mulVec_ne_zero g (ptVec_ne_zero i))

@[expose] def glPerm : G →* Equiv.Perm (Fin 31) where
  toFun := glPermFun
  map_one' := by
    ext i
    simp only [glPermFun, Units.val_one, one_mulVec, vecPt_ptVec, Equiv.coe_fn_mk,
      Equiv.Perm.one_apply]
  map_mul' g h := by
    ext i
    simp only [glPermFun, Units.val_mul, Equiv.coe_fn_mk, Equiv.Perm.mul_apply, ptVec_vecPt,
      mulVec_mulVec]

theorem glPerm_apply (g : G) (i : Fin 31) :
    ptVec (glPerm g i) = (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ ptVec i :=
  ptVec_glPermFun g i

theorem ptVec_injective : Function.Injective ptVec := by
  intro i j h
  rw [← vecPt_ptVec i (ptVec_ne_zero i), ← vecPt_ptVec j (ptVec_ne_zero j)]
  simp only [h]

theorem glPerm_apply_eq_iff (g : G) (i j : Fin 31) :
    glPerm g i = j ↔ (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ ptVec i = ptVec j := by
  rw [← glPerm_apply]
  exact ⟨fun h => h ▸ rfl, fun h => ptVec_injective h⟩

theorem glPerm_injective : Function.Injective glPerm := by
  rw [injective_iff_map_eq_one]
  intro g hg
  apply Units.ext
  rw [Units.val_one]
  ext r c
  have hv : (Pi.single c 1 : V) ≠ 0 := Pi.single_ne_zero_iff.mpr one_ne_zero
  set i := vecPt (Pi.single c 1) hv
  have h1 := glPerm_apply g i
  rw [hg, Equiv.Perm.one_apply, ptVec_vecPt] at h1
  have h2 := congrFun h1 r
  rw [mulVec_single_one] at h2
  simp only [Matrix.col_apply] at h2
  rw [← h2]
  simp [Matrix.one_apply, Pi.single_apply]

@[expose] noncomputable def commDim (x : G) : ℕ :=
  ((x : Matrix (Fin 5) (Fin 5) (ZMod 2)) - 1).rank

@[expose] def fixCount (x : G) : ℕ :=
  (Finset.univ.filter fun i : Fin 31 => glPerm x i = i).card

theorem card_fixed_vectors (x : G) :
    Fintype.card {v : V // (x : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ v = v} = 1 + fixCount x := by
  classical
  set A := (x : Matrix (Fin 5) (Fin 5) (ZMod 2))
  have e : {v : V // A *ᵥ v = v} ≃ Option {i : Fin 31 // glPerm x i = i} :=
    { toFun := fun v => if h : v.1 = 0 then none else some ⟨vecPt v.1 h, by
          rw [glPerm_apply_eq_iff, ptVec_vecPt]; exact v.2⟩
      invFun := fun o => match o with
        | none => ⟨0, mulVec_zero _⟩
        | some i => ⟨ptVec i.1, (glPerm_apply_eq_iff x i.1 i.1).1 i.2⟩
      left_inv := by
        rintro ⟨v, hv⟩
        by_cases h : v = 0
        · subst h; simp
        · simp [h, ptVec_vecPt]
      right_inv := by
        rintro (_ | ⟨i, hi⟩)
        · simp
        · simp [ptVec_ne_zero, vecPt_ptVec] }
  rw [Fintype.card_congr e, Fintype.card_option, fixCount, Fintype.card_subtype, add_comm]

theorem card_ker_eq {k : Type*} [Field k] [Fintype k] [DecidableEq k] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) k) :
    Fintype.card {v : Fin n → k // A *ᵥ v = 0} = Fintype.card k ^ (n - A.rank) := by
  classical
  have h := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  rw [Module.finrank_fin_fun] at h
  change A.rank + _ = n at h
  have hc := Module.card_eq_pow_finrank (K := k) (V := LinearMap.ker A.mulVecLin)
  have e : LinearMap.ker A.mulVecLin ≃ {v : Fin n → k // A *ᵥ v = 0} :=
    Equiv.subtypeEquivRight fun v => by rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
  rw [Fintype.card_congr e] at hc
  rw [hc]
  congr 1
  omega

theorem two_pow_commDim (x : G) : 2 ^ (5 - commDim x) = 1 + fixCount x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := card_ker_eq ((x : Matrix (Fin 5) (Fin 5) (ZMod 2)) - 1)
  rw [ZMod.card] at h
  rw [commDim, ← h, ← card_fixed_vectors]
  exact Fintype.card_congr (Equiv.subtypeEquivRight fun v => by
    rw [sub_mulVec, one_mulVec, sub_eq_zero])

theorem bijective_toGL :
    Function.Bijective (Matrix.SpecialLinearGroup.toGL :
      SpecialLinearGroup (Fin 5) (ZMod 2) →* GL (Fin 5) (ZMod 2)) := by
  refine ⟨Matrix.SpecialLinearGroup.toGL_injective, fun g => ?_⟩
  have hdet : (g : Matrix (Fin 5) (Fin 5) (ZMod 2)).det = 1 := by
    have hu : IsUnit (g : Matrix (Fin 5) (Fin 5) (ZMod 2)).det := g.isUnit.map Matrix.detMonoidHom
    obtain ⟨u, hu⟩ := hu
    rw [← hu]
    have : u = 1 := Subsingleton.elim _ _
    rw [this, Units.val_one]
  exact ⟨⟨g, hdet⟩, Units.ext (Matrix.SpecialLinearGroup.coe_GL_coe_matrix _)⟩

theorem center_SL_eq_bot : Subgroup.center (SpecialLinearGroup (Fin 5) (ZMod 2)) = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  obtain ⟨r, hr, hA'⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hA
  rw [Subgroup.mem_bot]
  have key : ∀ s : ZMod 2, s ^ 5 = 1 → s = 1 := by
    intro s hs
    rcases (by decide : ∀ s : ZMod 2, s = 0 ∨ s = 1) s with rfl | rfl
    · simp at hs
    · rfl
  rw [Fintype.card_fin] at hr
  have hr1 : r = 1 := key r hr
  rw [hr1, map_one] at hA'
  exact Subtype.ext hA'.symm

theorem bijective_mk_center : Function.Bijective
    (QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin 5) (ZMod 2)))) := by
  refine ⟨?_, QuotientGroup.mk'_surjective _⟩
  rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', center_SL_eq_bot]

theorem card_GL52 : Nat.card G = 2 ^ 10 * 3 ^ 2 * 5 * 7 * 31 := by
  rw [Matrix.card_GL_field, ZMod.card, Fin.prod_univ_five]
  norm_num [Fin.val_zero, Fin.val_one, Fin.val_two]

@[expose] noncomputable def equivPSL : G ≃* ProjectiveSpecialLinearGroup (Fin 5) (ZMod 2) :=
  (MulEquiv.ofBijective _ bijective_toGL).symm.trans (MulEquiv.ofBijective _ bijective_mk_center)

theorem isSimpleGroup_GL52 : IsSimpleGroup G := by
  obtain ⟨h1, h2, -⟩ := CFSG.LinearGroups.linear_projective_simple (K := ZMod 2) (n := 5)
    (by norm_num) (Or.inl (by norm_num))
  have : Nontrivial G := equivPSL.toEquiv.nontrivial
  exact IsSimpleGroup.isSimpleGroup_of_surjective equivPSL.symm.toMonoidHom equivPSL.symm.surjective

end CFSG.Literature.GL52
