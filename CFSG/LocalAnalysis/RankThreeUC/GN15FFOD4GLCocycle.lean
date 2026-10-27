module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.GraphAutomorphism

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.D4

open Matrix

variable {K : Type*} [Field K] {Z : Type*} [AddCommGroup Z]

@[expose] noncomputable def glDualAct (A : GL (Fin 4) K) (f : (Fin 4 → K) →+ Z) :
    (Fin 4 → K) →+ Z :=
  f.comp (Matrix.mulVecLin ((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)).toAddMonoidHom

@[expose] noncomputable def glTransAct (A : GL (Fin 4) K) (f : (Fin 4 → K) →+ Z) :
    (Fin 4 → K) →+ Z :=
  f.comp (Matrix.mulVecLin ((A : Matrix (Fin 4) (Fin 4) K)ᵀ)).toAddMonoidHom

@[simp] theorem glDualAct_apply (A : GL (Fin 4) K) (f : (Fin 4 → K) →+ Z) (x : Fin 4 → K) :
    glDualAct A f x = f (((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ x) := rfl

@[simp] theorem glTransAct_apply (A : GL (Fin 4) K) (f : (Fin 4 → K) →+ Z) (x : Fin 4 → K) :
    glTransAct A f x = f (((A : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)ᵀ *ᵥ x) := rfl

theorem glDualAct_one (f : (Fin 4 → K) →+ Z) :
    glDualAct (1 : GL (Fin 4) K) f = f := by
  unfold glDualAct
  simp only [inv_one, Units.val_one, Matrix.mulVecLin_one]
  exact AddMonoidHom.comp_id f

theorem glTransAct_one (f : (Fin 4 → K) →+ Z) :
    glTransAct (1 : GL (Fin 4) K) f = f := by
  unfold glTransAct
  simp only [Units.val_one, Matrix.transpose_one, Matrix.mulVecLin_one]
  exact AddMonoidHom.comp_id f

theorem glDualAct_mul (A B : GL (Fin 4) K) (f : (Fin 4 → K) →+ Z) :
    glDualAct (A * B) f = glDualAct A (glDualAct B f) := by
  unfold glDualAct
  rw [_root_.mul_inv_rev, Units.val_mul, Matrix.mulVecLin_mul]
  rfl

theorem glTransAct_mul (A B : GL (Fin 4) K) (f : (Fin 4 → K) →+ Z) :
    glTransAct (A * B) f = glTransAct A (glTransAct B f) := by
  unfold glTransAct
  rw [Units.val_mul, Matrix.transpose_mul, Matrix.mulVecLin_mul]
  rfl

theorem glDualAct_add (A : GL (Fin 4) K) (f g : (Fin 4 → K) →+ Z) :
    glDualAct A (f + g) = glDualAct A f + glDualAct A g := by
  simp only [glDualAct, AddMonoidHom.add_comp]

theorem glTransAct_add (A : GL (Fin 4) K) (f g : (Fin 4 → K) →+ Z) :
    glTransAct A (f + g) = glTransAct A f + glTransAct A g := by
  simp only [glTransAct, AddMonoidHom.add_comp]

theorem glDualAct_sub (A : GL (Fin 4) K) (f g : (Fin 4 → K) →+ Z) :
    glDualAct A (f - g) = glDualAct A f - glDualAct A g := by
  simp only [glDualAct, AddMonoidHom.sub_comp]

theorem glTransAct_sub (A : GL (Fin 4) K) (f g : (Fin 4 → K) →+ Z) :
    glTransAct A (f - g) = glTransAct A f - glTransAct A g := by
  simp only [glTransAct, AddMonoidHom.sub_comp]

private noncomputable def smulEnd (μ : K) : (Fin 4 → K) →+ (Fin 4 → K) :=
  (Matrix.mulVecLin (Matrix.scalar (Fin 4) μ)).toAddMonoidHom

private lemma smulEnd_apply (μ : K) (x : Fin 4 → K) : smulEnd μ x = μ • x := by
  simp [smulEnd, Matrix.scalar_apply]

private lemma smulEnd_comp (μ ν : K) :
    (smulEnd μ).comp (smulEnd ν) = smulEnd (μ * ν) := by
  ext x
  simp [smulEnd_apply, mul_assoc]

private lemma smulEnd_one : smulEnd (1 : K) = AddMonoidHom.id _ := by
  ext x
  simp [smulEnd_apply]

private lemma smulEnd_sub (μ ν : K) : smulEnd (μ - ν) = smulEnd μ - smulEnd ν := by
  ext x
  simp [smulEnd_apply, sub_mul]

private lemma smulEnd_mul_inv (μ : K) (hμ : μ ≠ 0) :
    (smulEnd μ).comp (smulEnd μ⁻¹) = AddMonoidHom.id _ := by
  rw [smulEnd_comp, mul_inv_cancel₀ hμ, smulEnd_one]

private lemma smulEnd_inv_mul (μ : K) (hμ : μ ≠ 0) :
    (smulEnd μ⁻¹).comp (smulEnd μ) = AddMonoidHom.id _ := by
  rw [smulEnd_comp, inv_mul_cancel₀ hμ, smulEnd_one]

private noncomputable def scalarGL (l : K) (hl : l ≠ 0) : GL (Fin 4) K :=
  Matrix.GeneralLinearGroup.scalar (Fin 4) (Units.mk0 l hl)

private lemma coe_scalarGL (l : K) (hl : l ≠ 0) :
    (scalarGL l hl : Matrix (Fin 4) (Fin 4) K) = Matrix.scalar (Fin 4) l := by
  simp [scalarGL]

private lemma scalarGL_commute (l : K) (hl : l ≠ 0) (A : GL (Fin 4) K) :
    scalarGL l hl * A = A * scalarGL l hl := by
  simpa [scalarGL] using Matrix.GeneralLinearGroup.scalar_commute (n := Fin 4) (Units.mk0 l hl) A

private lemma precomp_injective {s s' : (Fin 4 → K) →+ (Fin 4 → K)}
    (h : s.comp s' = AddMonoidHom.id _) :
    Function.Injective (fun g : (Fin 4 → K) →+ Z => g.comp s) := by
  intro g hg heq
  refine AddMonoidHom.ext fun x => ?_
  have hx : s (s' x) = x := by
    have := congrArg (fun k : (Fin 4 → K) →+ (Fin 4 → K) => k x) h
    simpa using this
  have := congrArg (fun k : (Fin 4 → K) →+ Z => k (s' x)) heq
  simpa [AddMonoidHom.comp_apply, hx] using this

private lemma precomp_leftInverse {s s' : (Fin 4 → K) →+ (Fin 4 → K)}
    (h : s'.comp s = AddMonoidHom.id _) (g : (Fin 4 → K) →+ Z) :
    (g.comp s').comp s = g := by
  rw [AddMonoidHom.comp_assoc, h, AddMonoidHom.comp_id]

private theorem exists_eq_glDualAct_sub_of_scalar
    (h : ∃ l : K, l ≠ 0 ∧ l ≠ 1)
    (c : GL (Fin 4) K → ((Fin 4 → K) →+ Z))
    (hc : ∀ A B, c (A * B) = c A + glDualAct A (c B)) :
    ∃ f : (Fin 4 → K) →+ Z, ∀ A, c A = glDualAct A f - f := by
  obtain ⟨l, hl0, hl1⟩ := h
  let z : GL (Fin 4) K := scalarGL l hl0
  let μ : K := l⁻¹ - 1
  have hμ : μ ≠ 0 := by
    intro h0
    apply hl1
    have h1 : l⁻¹ = 1 := sub_eq_zero.mp h0
    calc l = (l⁻¹)⁻¹ := (inv_inv l).symm
      _ = 1 := by rw [h1, inv_one]
  let s : (Fin 4 → K) →+ (Fin 4 → K) := smulEnd μ
  let s' : (Fin 4 → K) →+ (Fin 4 → K) := smulEnd μ⁻¹
  have hs : s.comp s' = AddMonoidHom.id _ := smulEnd_mul_inv μ hμ
  have hs' : s'.comp s = AddMonoidHom.id _ := smulEnd_inv_mul μ hμ
  let T : ((Fin 4 → K) →+ Z) → ((Fin 4 → K) →+ Z) := fun g => g.comp s
  have hT_inj : Function.Injective T := precomp_injective hs
  let f : (Fin 4 → K) →+ Z := (c z).comp s'
  have hTf : T f = c z := precomp_leftInverse hs' (c z)
  have hz_inv_gl : z⁻¹ = scalarGL l⁻¹ (inv_ne_zero hl0) := by
    apply Units.ext
    simp only [z, scalarGL]
    rfl
  have hz_inv : ((z⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      Matrix.scalar (Fin 4) l⁻¹ := by
    rw [hz_inv_gl]
    exact coe_scalarGL l⁻¹ (inv_ne_zero hl0)
  have hglDualAct_z : ∀ g : (Fin 4 → K) →+ Z, glDualAct z g = g.comp (smulEnd l⁻¹) := by
    intro g
    rw [glDualAct, hz_inv]
    rfl
  have hT_eq : ∀ g : (Fin 4 → K) →+ Z, T g = glDualAct z g - g := by
    intro g
    have hsub : smulEnd l⁻¹ - AddMonoidHom.id _ = smulEnd μ := by
      rw [← smulEnd_one, ← smulEnd_sub]
    calc T g = g.comp (smulEnd μ) := rfl
      _ = g.comp (smulEnd l⁻¹ - AddMonoidHom.id _) := by rw [hsub]
      _ = g.comp (smulEnd l⁻¹) - g.comp (AddMonoidHom.id _) := AddMonoidHom.comp_sub _ _ _
      _ = glDualAct z g - g := by rw [hglDualAct_z g, AddMonoidHom.comp_id]
  have hT_sub : ∀ g h : (Fin 4 → K) →+ Z, T (g - h) = T g - T h := by
    intro g h
    exact AddMonoidHom.sub_comp g h s
  have hT_comm : ∀ (A : GL (Fin 4) K) (g : (Fin 4 → K) →+ Z),
      T (glDualAct A g) = glDualAct A (T g) := by
    intro A g
    rw [hT_eq, hT_eq, glDualAct_sub, ← glDualAct_mul, ← glDualAct_mul, scalarGL_commute l hl0 A]
  refine ⟨f, fun A => ?_⟩
  have h1 : c (z * A) = c z + glDualAct z (c A) := hc z A
  have h2 : c (A * z) = c A + glDualAct A (c z) := hc A z
  have hcomm : z * A = A * z := scalarGL_commute l hl0 A
  have h3 : c z + glDualAct z (c A) = c A + glDualAct A (c z) := by
    rw [← h1, hcomm, h2]
  have hEq : glDualAct z (c A) - c A = glDualAct A (c z) - c z := by
    calc glDualAct z (c A) - c A
        = (c z + glDualAct z (c A)) - (c z + c A) := by abel
      _ = (c A + glDualAct A (c z)) - (c z + c A) := by rw [h3]
      _ = glDualAct A (c z) - c z := by abel
  have hT_cA : T (c A) = glDualAct A (c z) - c z := (hT_eq (c A)).trans hEq
  have hT_f : T (glDualAct A f - f) = glDualAct A (c z) - c z := by
    rw [hT_sub, hT_comm A, hTf]
  exact hT_inj (hT_cA.trans hT_f.symm)

section TwoElement

private lemma one_add_one_eq_zero (h2 : ∀ a : K, a = 0 ∨ a = 1) : (1 : K) + 1 = 0 := by
  rcases h2 ((1 : K) + 1) with h | h
  · exact h
  · exact absurd (add_left_cancel (a := (1 : K)) (b := 1) (c := 0) (by simp at h)) one_ne_zero

private lemma neg_one_eq_one (h2 : ∀ a : K, a = 0 ∨ a = 1) : (-1 : K) = 1 := by
  rw [neg_eq_iff_add_eq_zero]
  exact one_add_one_eq_zero h2

private lemma add_self_eq_zero_vec (h2 : ∀ a : K, a = 0 ∨ a = 1) (x : Fin 4 → K) :
    x + x = 0 := by
  ext i
  rcases h2 (x i) with h | h <;> simp [Pi.add_apply, h, one_add_one_eq_zero h2]

private lemma map_add_self_eq_zero (h2 : ∀ a : K, a = 0 ∨ a = 1) (f : (Fin 4 → K) →+ Z)
    (x : Fin 4 → K) : f x + f x = 0 := by
  rw [← map_add, add_self_eq_zero_vec h2, map_zero]

private lemma transvectionUnit_self_inv (h2 : ∀ a : K, a = 0 ∨ a = 1) {i j : Fin 4}
    (hij : i ≠ j) :
    (TauCeti.transvectionUnit hij (1 : K))⁻¹ = TauCeti.transvectionUnit hij (1 : K) := by
  rw [TauCeti.transvectionUnit_inv, neg_one_eq_one h2]

private lemma transvectionUnit_mul_self (h2 : ∀ a : K, a = 0 ∨ a = 1) {i j : Fin 4}
    (hij : i ≠ j) :
    TauCeti.transvectionUnit hij (1 : K) * TauCeti.transvectionUnit hij (1 : K) = 1 := by
  have h := transvectionUnit_self_inv h2 hij
  calc TauCeti.transvectionUnit hij (1 : K) * TauCeti.transvectionUnit hij (1 : K) =
      (TauCeti.transvectionUnit hij (1 : K))⁻¹ * TauCeti.transvectionUnit hij (1 : K) := by
        rw [h]
    _ = 1 := inv_mul_cancel _

private lemma transvectionUnit_mulVec_single {i j : Fin 4} (hij : i ≠ j) (k : Fin 4) :
    ((TauCeti.transvectionUnit hij (1 : K) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ
        Pi.single k (1 : K) =
      Pi.single k (1 : K) + (if k = j then Pi.single i (1 : K) else 0) := by
  rw [TauCeti.coe_transvectionUnit, Matrix.transvection, Matrix.add_mulVec, Matrix.one_mulVec,
    Matrix.single_mulVec_eq]
  by_cases h : k = j
  · simp [h]
  · simp [h]

private lemma glDualAct_transvection_single (h2 : ∀ a : K, a = 0 ∨ a = 1) {i j : Fin 4}
    (hij : i ≠ j) (f : (Fin 4 → K) →+ Z) (k : Fin 4) :
    glDualAct (TauCeti.transvectionUnit hij (1 : K)) f (Pi.single k (1 : K)) =
      f (Pi.single k (1 : K)) + (if k = j then f (Pi.single i (1 : K)) else 0) := by
  rw [glDualAct_apply, transvectionUnit_self_inv h2 hij, transvectionUnit_mulVec_single hij k,
    map_add]
  by_cases h : k = j <;> simp [h]

private def otherIndex (i : Fin 4) : Fin 4 := if i = 0 then 1 else 0

private lemma otherIndex_ne (i : Fin 4) : otherIndex i ≠ i := by
  unfold otherIndex
  split_ifs with h
  · rw [h]
    decide
  · exact fun h0 => h h0.symm

private lemma exists_fourth : ∀ i j k : Fin 4, ∃ l : Fin 4, l ≠ i ∧ l ≠ j ∧ l ≠ k := by
  decide

end TwoElement

private lemma cocycle_one_zero {c : GL (Fin 4) K → ((Fin 4 → K) →+ Z)}
    (hc : ∀ A B, c (A * B) = c A + glDualAct A (c B)) : c 1 = 0 := by
  have h := hc 1 1
  rw [mul_one, glDualAct_one] at h
  have h' : c 1 + 0 = c 1 + c 1 := by simpa using h
  exact (add_left_cancel h').symm

section TwoElement

private lemma transvection_cocycle_apply_self (h2 : ∀ a : K, a = 0 ∨ a = 1)
    {c : GL (Fin 4) K → ((Fin 4 → K) →+ Z)}
    (hc : ∀ A B, c (A * B) = c A + glDualAct A (c B)) {i j : Fin 4} (hij : i ≠ j) :
    c (TauCeti.transvectionUnit hij (1 : K)) (Pi.single i (1 : K)) = 0 := by
  have ht : TauCeti.transvectionUnit hij (1 : K) * TauCeti.transvectionUnit hij (1 : K) = 1 :=
    transvectionUnit_mul_self h2 hij
  have h1 : c 1 = 0 := cocycle_one_zero hc
  have h := hc (TauCeti.transvectionUnit hij (1 : K)) (TauCeti.transvectionUnit hij (1 : K))
  rw [ht, h1] at h
  have hval : 0 = c (TauCeti.transvectionUnit hij (1 : K)) (Pi.single j (1 : K)) +
      glDualAct (TauCeti.transvectionUnit hij (1 : K))
        (c (TauCeti.transvectionUnit hij (1 : K))) (Pi.single j (1 : K)) := by
    simpa only [AddMonoidHom.zero_apply, AddMonoidHom.add_apply] using
      congrArg (fun g : (Fin 4 → K) →+ Z => g (Pi.single j (1 : K))) h
  rw [glDualAct_transvection_single h2 hij] at hval
  simp only [if_true] at hval
  have h2j : c (TauCeti.transvectionUnit hij (1 : K)) (Pi.single j (1 : K)) +
      c (TauCeti.transvectionUnit hij (1 : K)) (Pi.single j (1 : K)) = 0 :=
    map_add_self_eq_zero h2 _ _
  have hval' : c (TauCeti.transvectionUnit hij (1 : K)) (Pi.single j (1 : K)) +
      c (TauCeti.transvectionUnit hij (1 : K)) (Pi.single j (1 : K)) +
      c (TauCeti.transvectionUnit hij (1 : K)) (Pi.single i (1 : K)) = 0 := by
    calc c (TauCeti.transvectionUnit hij (1 : K)) (Pi.single j (1 : K)) +
          c (TauCeti.transvectionUnit hij (1 : K)) (Pi.single j (1 : K)) +
          c (TauCeti.transvectionUnit hij (1 : K)) (Pi.single i (1 : K)) =
        c (TauCeti.transvectionUnit hij (1 : K)) (Pi.single j (1 : K)) +
          (c (TauCeti.transvectionUnit hij (1 : K)) (Pi.single j (1 : K)) +
            c (TauCeti.transvectionUnit hij (1 : K)) (Pi.single i (1 : K))) := by abel
      _ = 0 := hval.symm
  rwa [h2j, zero_add] at hval'

private lemma transvection_cocycle_apply_ne (h2 : ∀ a : K, a = 0 ∨ a = 1)
    {c : GL (Fin 4) K → ((Fin 4 → K) →+ Z)}
    (hc : ∀ A B, c (A * B) = c A + glDualAct A (c B)) {i j k : Fin 4} (hij : i ≠ j)
    (_hki : k ≠ i) (hkj : k ≠ j) :
    c (TauCeti.transvectionUnit hij (1 : K)) (Pi.single k (1 : K)) = 0 := by
  obtain ⟨l, hli, hlj, hlk⟩ := exists_fourth i j k
  let u : GL (Fin 4) K := TauCeti.transvectionUnit (Ne.symm hlk) (1 : K)
  have hcomm : TauCeti.transvectionUnit hij (1 : K) * u = u * TauCeti.transvectionUnit hij (1 : K) :=
    (TauCeti.commute_transvectionUnit hij (Ne.symm hlk) hkj.symm hli (1 : K) (1 : K)).eq
  have h1 := hc (TauCeti.transvectionUnit hij (1 : K)) u
  have h2' := hc u (TauCeti.transvectionUnit hij (1 : K))
  have hEq : c (TauCeti.transvectionUnit hij (1 : K)) +
        glDualAct (TauCeti.transvectionUnit hij (1 : K)) (c u) =
      c u + glDualAct u (c (TauCeti.transvectionUnit hij (1 : K))) := by
    rw [← h1, hcomm, h2']
  have h : c (TauCeti.transvectionUnit hij (1 : K)) (Pi.single l (1 : K)) +
      glDualAct (TauCeti.transvectionUnit hij (1 : K)) (c u) (Pi.single l (1 : K)) =
      c u (Pi.single l (1 : K)) +
        glDualAct u (c (TauCeti.transvectionUnit hij (1 : K))) (Pi.single l (1 : K)) := by
    simpa only [AddMonoidHom.add_apply] using
      congrArg (fun g : (Fin 4 → K) →+ Z => g (Pi.single l (1 : K))) hEq
  rw [glDualAct_transvection_single h2 hij (c u) l,
    glDualAct_transvection_single h2 (Ne.symm hlk)
      (c (TauCeti.transvectionUnit hij (1 : K))) l] at h
  simp only [hlj, if_false, add_zero, if_true] at h
  have h' : c (TauCeti.transvectionUnit hij (1 : K)) (Pi.single l (1 : K)) +
        c u (Pi.single l (1 : K)) +
        c (TauCeti.transvectionUnit hij (1 : K)) (Pi.single k (1 : K)) =
      c (TauCeti.transvectionUnit hij (1 : K)) (Pi.single l (1 : K)) +
        c u (Pi.single l (1 : K)) + 0 := by
    calc c (TauCeti.transvectionUnit hij (1 : K)) (Pi.single l (1 : K)) +
          c u (Pi.single l (1 : K)) +
          c (TauCeti.transvectionUnit hij (1 : K)) (Pi.single k (1 : K)) =
        c u (Pi.single l (1 : K)) +
          (c (TauCeti.transvectionUnit hij (1 : K)) (Pi.single l (1 : K)) +
            c (TauCeti.transvectionUnit hij (1 : K)) (Pi.single k (1 : K))) := by abel
      _ = c (TauCeti.transvectionUnit hij (1 : K)) (Pi.single l (1 : K)) +
          c u (Pi.single l (1 : K)) := h.symm
      _ = c (TauCeti.transvectionUnit hij (1 : K)) (Pi.single l (1 : K)) +
          c u (Pi.single l (1 : K)) + 0 := by abel
  exact add_left_cancel h'

private lemma transvection_cocycle_apply_e_j_eq (h2 : ∀ a : K, a = 0 ∨ a = 1)
    {c : GL (Fin 4) K → ((Fin 4 → K) →+ Z)}
    (hc : ∀ A B, c (A * B) = c A + glDualAct A (c B)) {i j k : Fin 4} (hij : i ≠ j)
    (hjk : j ≠ k) (hik : i ≠ k) :
    c (TauCeti.transvectionUnit hij (1 : K)) (Pi.single j (1 : K)) =
      c (TauCeti.transvectionUnit hik (1 : K)) (Pi.single k (1 : K)) := by
  have hrel : TauCeti.transvectionUnit hij (1 : K) * TauCeti.transvectionUnit hjk (1 : K) =
      TauCeti.transvectionUnit hjk (1 : K) * TauCeti.transvectionUnit hij (1 : K) *
        TauCeti.transvectionUnit hik (1 : K) := by
    simpa only [mul_one] using
      TauCeti.transvectionUnit_mul_transvectionUnit_eq_mul_mul hij hjk hik (1 : K) (1 : K)
  have h1 := hc (TauCeti.transvectionUnit hij (1 : K)) (TauCeti.transvectionUnit hjk (1 : K))
  have h2' := hc (TauCeti.transvectionUnit hjk (1 : K) * TauCeti.transvectionUnit hij (1 : K))
    (TauCeti.transvectionUnit hik (1 : K))
  have h3 := hc (TauCeti.transvectionUnit hjk (1 : K)) (TauCeti.transvectionUnit hij (1 : K))
  have hEq : c (TauCeti.transvectionUnit hij (1 : K)) +
        glDualAct (TauCeti.transvectionUnit hij (1 : K))
          (c (TauCeti.transvectionUnit hjk (1 : K))) =
      (c (TauCeti.transvectionUnit hjk (1 : K)) +
          glDualAct (TauCeti.transvectionUnit hjk (1 : K))
            (c (TauCeti.transvectionUnit hij (1 : K)))) +
        glDualAct (TauCeti.transvectionUnit hjk (1 : K) *
          TauCeti.transvectionUnit hij (1 : K))
          (c (TauCeti.transvectionUnit hik (1 : K))) := by
    rw [← h1, hrel, h2', h3]
  have h : c (TauCeti.transvectionUnit hij (1 : K)) (Pi.single k (1 : K)) +
      glDualAct (TauCeti.transvectionUnit hij (1 : K))
        (c (TauCeti.transvectionUnit hjk (1 : K))) (Pi.single k (1 : K)) =
      (c (TauCeti.transvectionUnit hjk (1 : K)) (Pi.single k (1 : K)) +
        glDualAct (TauCeti.transvectionUnit hjk (1 : K))
          (c (TauCeti.transvectionUnit hij (1 : K))) (Pi.single k (1 : K))) +
      glDualAct (TauCeti.transvectionUnit hjk (1 : K) *
        TauCeti.transvectionUnit hij (1 : K))
        (c (TauCeti.transvectionUnit hik (1 : K))) (Pi.single k (1 : K)) := by
    simpa only [AddMonoidHom.add_apply] using
      congrArg (fun g : (Fin 4 → K) →+ Z => g (Pi.single k (1 : K))) hEq
  have hc_ij_k : c (TauCeti.transvectionUnit hij (1 : K)) (Pi.single k (1 : K)) = 0 :=
    transvection_cocycle_apply_ne h2 hc hij hik.symm hjk.symm
  have hc_ik_j : c (TauCeti.transvectionUnit hik (1 : K)) (Pi.single j (1 : K)) = 0 :=
    transvection_cocycle_apply_ne h2 hc hik (Ne.symm hij) hjk
  have hc_ik_i : c (TauCeti.transvectionUnit hik (1 : K)) (Pi.single i (1 : K)) = 0 :=
    transvection_cocycle_apply_self h2 hc hik
  have hL : c (TauCeti.transvectionUnit hij (1 : K)) (Pi.single k (1 : K)) +
        glDualAct (TauCeti.transvectionUnit hij (1 : K))
          (c (TauCeti.transvectionUnit hjk (1 : K))) (Pi.single k (1 : K)) =
      c (TauCeti.transvectionUnit hjk (1 : K)) (Pi.single k (1 : K)) := by
    rw [glDualAct_transvection_single h2 hij (c (TauCeti.transvectionUnit hjk (1 : K))) k,
      if_neg hjk.symm, add_zero, hc_ij_k, zero_add]
  have hM : c (TauCeti.transvectionUnit hjk (1 : K)) (Pi.single k (1 : K)) +
        glDualAct (TauCeti.transvectionUnit hjk (1 : K))
          (c (TauCeti.transvectionUnit hij (1 : K))) (Pi.single k (1 : K)) =
      c (TauCeti.transvectionUnit hjk (1 : K)) (Pi.single k (1 : K)) +
        c (TauCeti.transvectionUnit hij (1 : K)) (Pi.single j (1 : K)) := by
    rw [glDualAct_transvection_single h2 hjk (c (TauCeti.transvectionUnit hij (1 : K))) k,
      if_pos rfl, hc_ij_k, zero_add]
  have hN : glDualAct (TauCeti.transvectionUnit hjk (1 : K) *
        TauCeti.transvectionUnit hij (1 : K)) (c (TauCeti.transvectionUnit hik (1 : K)))
        (Pi.single k (1 : K)) =
      c (TauCeti.transvectionUnit hik (1 : K)) (Pi.single k (1 : K)) := by
    rw [glDualAct_mul,
      glDualAct_transvection_single h2 hjk
        (glDualAct (TauCeti.transvectionUnit hij (1 : K))
          (c (TauCeti.transvectionUnit hik (1 : K)))) k,
      if_pos rfl,
      glDualAct_transvection_single h2 hij (c (TauCeti.transvectionUnit hik (1 : K))) k,
      glDualAct_transvection_single h2 hij (c (TauCeti.transvectionUnit hik (1 : K))) j,
      if_neg hjk.symm, hc_ik_j, hc_ik_i, if_pos rfl, add_zero, zero_add, add_zero]
  rw [hL, hM, hN] at h
  have hbij : c (TauCeti.transvectionUnit hij (1 : K)) (Pi.single j (1 : K)) +
      c (TauCeti.transvectionUnit hij (1 : K)) (Pi.single j (1 : K)) = 0 :=
    map_add_self_eq_zero h2 _ _
  have hbik : c (TauCeti.transvectionUnit hik (1 : K)) (Pi.single k (1 : K)) +
      c (TauCeti.transvectionUnit hik (1 : K)) (Pi.single k (1 : K)) = 0 :=
    map_add_self_eq_zero h2 _ _
  have h0 : c (TauCeti.transvectionUnit hij (1 : K)) (Pi.single j (1 : K)) +
      c (TauCeti.transvectionUnit hik (1 : K)) (Pi.single k (1 : K)) = 0 := by
    have h' : c (TauCeti.transvectionUnit hjk (1 : K)) (Pi.single k (1 : K)) +
          (c (TauCeti.transvectionUnit hij (1 : K)) (Pi.single j (1 : K)) +
            c (TauCeti.transvectionUnit hik (1 : K)) (Pi.single k (1 : K))) =
        c (TauCeti.transvectionUnit hjk (1 : K)) (Pi.single k (1 : K)) + 0 := by
      calc c (TauCeti.transvectionUnit hjk (1 : K)) (Pi.single k (1 : K)) +
            (c (TauCeti.transvectionUnit hij (1 : K)) (Pi.single j (1 : K)) +
              c (TauCeti.transvectionUnit hik (1 : K)) (Pi.single k (1 : K))) =
          (c (TauCeti.transvectionUnit hjk (1 : K)) (Pi.single k (1 : K)) +
            c (TauCeti.transvectionUnit hij (1 : K)) (Pi.single j (1 : K))) +
            c (TauCeti.transvectionUnit hik (1 : K)) (Pi.single k (1 : K)) := by abel
        _ = c (TauCeti.transvectionUnit hjk (1 : K)) (Pi.single k (1 : K)) := h.symm
        _ = c (TauCeti.transvectionUnit hjk (1 : K)) (Pi.single k (1 : K)) + 0 := by abel
    exact add_left_cancel h'
  have hb : c (TauCeti.transvectionUnit hik (1 : K)) (Pi.single k (1 : K)) =
      -c (TauCeti.transvectionUnit hij (1 : K)) (Pi.single j (1 : K)) := by
    rw [eq_neg_iff_add_eq_zero, add_comm]
    exact h0
  have ha : c (TauCeti.transvectionUnit hij (1 : K)) (Pi.single j (1 : K)) =
      -c (TauCeti.transvectionUnit hij (1 : K)) (Pi.single j (1 : K)) := by
    rw [eq_neg_iff_add_eq_zero]
    exact hbij
  rw [hb]
  exact ha

end TwoElement

private noncomputable def beta (c : GL (Fin 4) K → ((Fin 4 → K) →+ Z)) (i : Fin 4) : Z :=
  c (TauCeti.transvectionUnit (Ne.symm (otherIndex_ne i)) (1 : K))
    (Pi.single (otherIndex i) (1 : K))

private lemma beta_torsion (h2 : ∀ a : K, a = 0 ∨ a = 1)
    (c : GL (Fin 4) K → ((Fin 4 → K) →+ Z)) (i : Fin 4) : beta c i + beta c i = 0 :=
  map_add_self_eq_zero h2 _ _

private lemma transvection_cocycle_apply_eq_beta (h2 : ∀ a : K, a = 0 ∨ a = 1)
    {c : GL (Fin 4) K → ((Fin 4 → K) →+ Z)}
    (hc : ∀ A B, c (A * B) = c A + glDualAct A (c B)) {i j : Fin 4} (hij : i ≠ j) :
    c (TauCeti.transvectionUnit hij (1 : K)) (Pi.single j (1 : K)) = beta c i := by
  by_cases hj : j = otherIndex i
  · subst hj
    rfl
  · exact transvection_cocycle_apply_e_j_eq h2 hc hij hj (Ne.symm (otherIndex_ne i))

private lemma ext_of_basis (h2 : ∀ a : K, a = 0 ∨ a = 1)
    {f g : (Fin 4 → K) →+ Z}
    (h : ∀ i, f (Pi.single i (1 : K)) = g (Pi.single i (1 : K))) : f = g := by
  refine AddMonoidHom.ext fun x => ?_
  have hx : x = ∑ i, Pi.single i (x i) := (Finset.univ_sum_single x).symm
  rw [hx, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rcases h2 (x i) with hxi | hxi <;> simp [hxi, h i]

private noncomputable def glCochain (h2 : ∀ a : K, a = 0 ∨ a = 1) (β : Fin 4 → Z)
    (hβ : ∀ i, β i + β i = 0) : (Fin 4 → K) →+ Z := by
  classical
  exact AddMonoidHom.mk' (fun x => ∑ i, if x i = 1 then β i else 0) (by
    intro x y
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rcases h2 (x i) with hx | hx <;> rcases h2 (y i) with hy | hy <;>
      simp [hx, hy, Pi.add_apply, one_add_one_eq_zero h2, hβ i])

private lemma glCochain_single (h2 : ∀ a : K, a = 0 ∨ a = 1) (β : Fin 4 → Z)
    (hβ : ∀ i, β i + β i = 0) (k : Fin 4) :
    glCochain h2 β hβ (Pi.single k (1 : K)) = β k := by
  classical
  change (∑ i, if (Pi.single k (1 : K) : Fin 4 → K) i = 1 then β i else 0) = β k
  rw [Finset.sum_eq_single k]
  · simp
  · intro b _ hbk
    simp [Pi.single_eq_of_ne hbk]
  · intro hk
    exact absurd (Finset.mem_univ k) hk

private lemma transvection_cocycle_eq_coboundary (h2 : ∀ a : K, a = 0 ∨ a = 1)
    {c : GL (Fin 4) K → ((Fin 4 → K) →+ Z)}
    (hc : ∀ A B, c (A * B) = c A + glDualAct A (c B)) (m : (Fin 4 → K) →+ Z)
    (hm : ∀ i, m (Pi.single i (1 : K)) = beta c i) {i j : Fin 4} (hij : i ≠ j) :
    c (TauCeti.transvectionUnit hij (1 : K)) =
      glDualAct (TauCeti.transvectionUnit hij (1 : K)) m - m := by
  apply ext_of_basis h2
  intro k
  have hRHS : (glDualAct (TauCeti.transvectionUnit hij (1 : K)) m - m)
        (Pi.single k (1 : K)) = if k = j then beta c i else 0 := by
    rw [AddMonoidHom.sub_apply, glDualAct_apply, transvectionUnit_self_inv h2 hij,
      transvectionUnit_mulVec_single hij k, map_add]
    by_cases hk : k = j
    · simp [hk, hm i]
    · simp [hk]
  rw [hRHS]
  by_cases hk : k = j
  · subst hk
    rw [if_pos rfl, transvection_cocycle_apply_eq_beta h2 hc hij]
  · rw [if_neg hk]
    by_cases hki : k = i
    · subst hki
      exact transvection_cocycle_apply_self h2 hc hij
    · exact transvection_cocycle_apply_ne h2 hc hij hki hk

private theorem exists_eq_glDualAct_sub_of_two (h2 : ∀ a : K, a = 0 ∨ a = 1)
    (c : GL (Fin 4) K → ((Fin 4 → K) →+ Z))
    (hc : ∀ A B, c (A * B) = c A + glDualAct A (c B)) :
    ∃ f : (Fin 4 → K) →+ Z, ∀ A, c A = glDualAct A f - f := by
  classical
  let β : Fin 4 → Z := beta c
  have hβ : ∀ i, β i + β i = 0 := beta_torsion h2 c
  let m : (Fin 4 → K) →+ Z := glCochain h2 β hβ
  have hm : ∀ i, m (Pi.single i (1 : K)) = β i := glCochain_single h2 β hβ
  let c' : GL (Fin 4) K → ((Fin 4 → K) →+ Z) :=
    fun A => c A - (glDualAct A m - m)
  have hc'_one : c' 1 = 0 := by
    simp [c', glDualAct_one, cocycle_one_zero hc]
  have hc' : ∀ A B, c' (A * B) = c' A + glDualAct A (c' B) := by
    intro A B
    have hb : glDualAct (A * B) m - m =
        (glDualAct A m - m) + glDualAct A (glDualAct B m - m) := by
      rw [glDualAct_mul, glDualAct_sub]
      abel
    change c (A * B) - (glDualAct (A * B) m - m) =
      (c A - (glDualAct A m - m)) +
        glDualAct A (c B - (glDualAct B m - m))
    rw [hc A B, hb]
    simp only [glDualAct_sub]
    abel
  have htrans : ∀ {i j : Fin 4} (hij : i ≠ j),
      c' (TauCeti.transvectionUnit hij (1 : K)) = 0 := by
    intro i j hij
    change c (TauCeti.transvectionUnit hij (1 : K)) -
        (glDualAct (TauCeti.transvectionUnit hij (1 : K)) m - m) = 0
    rw [transvection_cocycle_eq_coboundary h2 hc m hm hij]
    abel
  have hzero : ∀ A, c' A = 0 := by
    intro A
    let P : Matrix (Fin 4) (Fin 4) K → Prop := fun M =>
      ∀ B : GL (Fin 4) K, (B : Matrix (Fin 4) (Fin 4) K) = M → c' B = 0
    have hdiag : ∀ D : Fin 4 → K, (Matrix.diagonal D).det ≠ 0 → P (Matrix.diagonal D) := by
      intro D hD B hB
      have hD1 : Matrix.diagonal D = 1 := by
        ext i j
        by_cases hij : i = j
        · subst hij
          have hDi : D i ≠ 0 := by
            intro h0
            apply hD
            rw [Matrix.det_diagonal]
            exact Finset.prod_eq_zero (Finset.mem_univ i) h0
          have hDi1 : D i = 1 := by
            rcases h2 (D i) with h | h
            · exact absurd h hDi
            · exact h
          simp [hDi1]
        · simp [hij]
      have hB1 : B = 1 := Units.ext (by rw [hB, hD1]; rfl)
      rw [hB1]
      exact hc'_one
    have htransvec : ∀ t : Matrix.TransvectionStruct (Fin 4) K, P t.toMatrix := by
      intro t B hB
      rcases h2 t.c with hc0 | hc1
      · have ht : t.toMatrix = 1 := by
          rw [Matrix.TransvectionStruct.toMatrix_mk, hc0, Matrix.transvection_zero]
        have hB1 : B = 1 := Units.ext (by rw [hB, ht]; rfl)
        rw [hB1]
        exact hc'_one
      · have ht : t.toMatrix =
            ((TauCeti.transvectionUnit t.hij (1 : K)) : Matrix (Fin 4) (Fin 4) K) := by
          rw [Matrix.TransvectionStruct.toMatrix_mk, hc1]
          exact (TauCeti.coe_transvectionUnit t.hij (1 : K)).symm
        have hB1 : B = TauCeti.transvectionUnit t.hij (1 : K) := Units.ext (by rw [hB, ht])
        rw [hB1]
        exact htrans t.hij
    have hmul : ∀ M N : Matrix (Fin 4) (Fin 4) K, M.det ≠ 0 → N.det ≠ 0 → P M → P N →
        P (M * N) := by
      intro M N hM hN PM PN B hB
      let B₁ : GL (Fin 4) K := Matrix.GeneralLinearGroup.mkOfDetNeZero M hM
      let B₂ : GL (Fin 4) K := Matrix.GeneralLinearGroup.mkOfDetNeZero N hN
      have hB1 : (B₁ : Matrix (Fin 4) (Fin 4) K) = M := by simp [B₁]
      have hB2 : (B₂ : Matrix (Fin 4) (Fin 4) K) = N := by simp [B₂]
      have hB' : B = B₁ * B₂ := Units.ext (by rw [hB, Units.val_mul, hB1, hB2])
      rw [hB', hc' B₁ B₂, PM B₁ hB1, PN B₂ hB2]
      simp [glDualAct]
    have hP := Matrix.diagonal_transvection_induction_of_det_ne_zero P
      ((A : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)
      (Matrix.GeneralLinearGroup.det_ne_zero A) hdiag htransvec hmul
    exact hP A rfl
  refine ⟨m, fun A => ?_⟩
  have h := hzero A
  change c A - (glDualAct A m - m) = 0 at h
  exact sub_eq_zero.mp h

private lemma coe_inverseTranspose_inv (A : GL (Fin 4) K) :
    (((Matrix.GeneralLinearGroup.inverseTranspose A)⁻¹ : GL (Fin 4) K) :
      Matrix (Fin 4) (Fin 4) K) = ((A : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)ᵀ := by
  have h1 : (Matrix.GeneralLinearGroup.inverseTranspose A)⁻¹ =
      Matrix.GeneralLinearGroup.inverseTranspose A⁻¹ :=
    (map_inv (Matrix.GeneralLinearGroup.inverseTranspose) A).symm
  rw [h1, Matrix.GeneralLinearGroup.coe_inverseTranspose]
  simp

private lemma glTransAct_eq_glDualAct_inverseTranspose (A : GL (Fin 4) K)
    (f : (Fin 4 → K) →+ Z) :
    glTransAct A f = glDualAct (Matrix.GeneralLinearGroup.inverseTranspose A) f := by
  refine AddMonoidHom.ext fun x => ?_
  rw [glTransAct_apply, glDualAct_apply, coe_inverseTranspose_inv]

theorem exists_eq_glDualAct_sub (c : GL (Fin 4) K → ((Fin 4 → K) →+ Z))
    (hc : ∀ A B, c (A * B) = c A + glDualAct A (c B)) :
    ∃ f : (Fin 4 → K) →+ Z, ∀ A, c A = glDualAct A f - f := by
  by_cases h : ∃ l : K, l ≠ 0 ∧ l ≠ 1
  · exact exists_eq_glDualAct_sub_of_scalar h c hc
  · push Not at h
    have h2 : ∀ a : K, a = 0 ∨ a = 1 := by
      intro a
      by_cases ha : a = 0
      · exact Or.inl ha
      · exact Or.inr (h a ha)
    exact exists_eq_glDualAct_sub_of_two h2 c hc

theorem exists_eq_glTransAct_sub (c : GL (Fin 4) K → ((Fin 4 → K) →+ Z))
    (hc : ∀ A B, c (A * B) = c A + glTransAct A (c B)) :
    ∃ f : (Fin 4 → K) →+ Z, ∀ A, c A = glTransAct A f - f := by
  let c' : GL (Fin 4) K → ((Fin 4 → K) →+ Z) :=
    fun B => c (Matrix.GeneralLinearGroup.inverseTranspose B)
  have hc' : ∀ A B, c' (A * B) = c' A + glDualAct A (c' B) := by
    intro A B
    change c (Matrix.GeneralLinearGroup.inverseTranspose (A * B)) =
      c (Matrix.GeneralLinearGroup.inverseTranspose A) +
        glDualAct A (c (Matrix.GeneralLinearGroup.inverseTranspose B))
    rw [map_mul, hc]
    congr 1
    rw [glTransAct_eq_glDualAct_inverseTranspose,
      Matrix.GeneralLinearGroup.inverseTranspose_inverseTranspose]
  obtain ⟨f, hf⟩ := exists_eq_glDualAct_sub c' hc'
  refine ⟨f, fun A => ?_⟩
  have h := hf (Matrix.GeneralLinearGroup.inverseTranspose A)
  have hinv : c' (Matrix.GeneralLinearGroup.inverseTranspose A) = c A := by
    simp [c', Matrix.GeneralLinearGroup.inverseTranspose_inverseTranspose]
  rw [hinv, ← glTransAct_eq_glDualAct_inverseTranspose A f] at h
  exact h

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.D4
