module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotFRNonaltBasic

public section

namespace CFSG.SeitzReduction.LinearPilot

namespace Nonalt

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial LinearFlag FourGroupEvenCanonical
open CFSG.ComponentClassification.UnbalancedCatalog.NonalternatingRadical
open CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane (linearFieldPart linearFieldPart_eq)

variable {n : ℕ} {K : Type} [Field K] [CharP K 2]

section OrthElt

theorem det_eq_one_of_transpose_mul_self {g : Matrix (Fin n) (Fin n) K} (hg : gᵀ * g = 1) :
    g.det = 1 := by
  have h := congrArg Matrix.det hg
  rw [det_mul, det_transpose, det_one] at h
  have h1 : (g.det - 1) ^ 2 = 0 := by
    have e : (g.det - 1) ^ 2 = g.det * g.det - 1 - 2 * (g.det - 1) := by ring
    rw [e, h, CharTwo.two_eq_zero]
    ring
  exact sub_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h1)

@[expose] def orthSLElt (g : Matrix (Fin n) (Fin n) K) (hg : gᵀ * g = 1) :
    SpecialLinearGroup (Fin n) K :=
  ⟨g, det_eq_one_of_transpose_mul_self hg⟩

theorem coe_orthSLElt {g : Matrix (Fin n) (Fin n) K} (hg : gᵀ * g = 1) :
    (orthSLElt g hg : Matrix (Fin n) (Fin n) K) = g :=
  rfl

@[expose] def orthElt (g : Matrix (Fin n) (Fin n) K) (hg : gᵀ * g = 1) : projectiveSL n K :=
  proj n K (orthSLElt g hg)

theorem orthElt_mem_autFixSubgroup {g : Matrix (Fin n) (Fin n) K} (hg : gᵀ * g = 1) :
    orthElt g hg ∈ autFixSubgroup (dualAut n K) :=
  proj_mem_autFixSubgroup_dualAut (A := orthSLElt g hg) hg

end OrthElt

section Rad

variable (hn : Even n)
include hn

theorem radicalMatrix_orth {x : Fin n → K} (hx : onesVec ⬝ᵥ x = 0) (c : K) :
    (radicalMatrix x c)ᵀ * radicalMatrix x c = 1 := by
  rw [radicalMatrix_transpose, radicalMatrix_mul_self hn hx]

@[expose] def radElt (x : Fin n → K) (hx : onesVec ⬝ᵥ x = 0) (c : K) : projectiveSL n K :=
  orthElt (radicalMatrix x c) (radicalMatrix_orth hn hx c)

theorem exists_radElt_eq {i : Fin n} {y : projectiveSL n K} (hy : y ∈ radical (K := K) i) :
    ∃ v ∈ radicalW i, ∃ c : K, ∃ hv : onesVec ⬝ᵥ v = 0, y = radElt hn v hv c := by
  obtain ⟨A, hA, rfl⟩ := hy
  obtain ⟨v, hv, c, hc⟩ := (mem_radicalGroup hn).1 hA
  refine ⟨v, hv, c, (mem_radicalW.1 hv).1, ?_⟩
  rw [radElt, orthElt]
  congr 1
  exact Subtype.ext hc

omit hn in
theorem onesVec_dotProduct_orth {g : Matrix (Fin n) (Fin n) K} (hg : gᵀ * g = 1)
    (x : Fin n → K) : onesVec ⬝ᵥ (g *ᵥ x) = onesVec ⬝ᵥ x :=
  onesVec_dotProduct_mulVec_of_mem (toGL_mem_matrixIsometryGroup (A := orthSLElt g hg) hg) x

omit hn in
theorem mulVec_onesVec_orth {g : Matrix (Fin n) (Fin n) K} (hg : gᵀ * g = 1) :
    g *ᵥ onesVec = onesVec :=
  mulVec_onesVec_of_mem (toGL_mem_matrixIsometryGroup (A := orthSLElt g hg) hg)

end Rad

section Trans

omit [CharP K 2] in
theorem vecMulVec_mulVec' (u x : Fin n → K) : vecMulVec u u *ᵥ x = (u ⬝ᵥ x) • u := by
  rw [vecMulVec_mulVec, op_smul_eq_smul]

theorem dotProduct_self_of_dotProduct {u : Fin n → K} (hu : onesVec ⬝ᵥ u = 0) : u ⬝ᵥ u = 0 := by
  rw [dotProduct_self_eq_sq, hu, zero_pow two_ne_zero]

theorem transMatrix_orth {u : Fin n → K} (hu : onesVec ⬝ᵥ u = 0) (c : K) :
    (1 + c • vecMulVec u u)ᵀ * (1 + c • vecMulVec u u) = 1 := by
  have hM : vecMulVec u u * vecMulVec u u = 0 := by
    rw [vecMulVec_mul_vecMulVec, dotProduct_self_of_dotProduct hu, zero_smul]
    ext a b
    simp [vecMulVec_apply]
  have h2 : c • vecMulVec u u + c • vecMulVec u u = 0 := by
    rw [← two_smul K (c • vecMulVec u u), CharTwo.two_eq_zero, zero_smul]
  rw [transpose_add, transpose_one, transpose_smul, transpose_vecMulVec, Matrix.add_mul,
    Matrix.one_mul, Matrix.mul_add, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, hM,
    smul_zero, smul_zero, add_zero, add_assoc, h2, add_zero]

@[expose] def transElt (u : Fin n → K) (hu : onesVec ⬝ᵥ u = 0) (c : K) : projectiveSL n K :=
  orthElt (1 + c • vecMulVec u u) (transMatrix_orth hu c)

omit [CharP K 2] in
theorem transMatrix_mulVec (u : Fin n → K) (c : K) (x : Fin n → K) :
    (1 + c • vecMulVec u u) *ᵥ x = x + (c * (u ⬝ᵥ x)) • u := by
  rw [add_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec', smul_smul]

theorem transElt_mem_levi {i : Fin n} {u : Fin n → K} (hu : onesVec ⬝ᵥ u = 0) (hui : u i = 0)
    (c : K) : transElt u hu c ∈ levi (K := K) i :=
  ⟨orthSLElt _ (transMatrix_orth hu c), ⟨transMatrix_orth hu c, by
    rw [coe_orthSLElt, transMatrix_mulVec, dotProduct_single_one, hui, mul_zero, zero_smul,
      add_zero]⟩, rfl⟩

end Trans

section Faithful

omit [CharP K 2] in
theorem pairVec_apply (a b j : Fin n) :
    (Pi.single a (1 : K) + Pi.single b 1 : Fin n → K) j =
      (if j = a then 1 else 0) + (if j = b then 1 else 0) := by
  simp only [Pi.add_apply, Pi.single_apply]

theorem onesVec_dotProduct_pairVec (a b : Fin n) :
    (onesVec : Fin n → K) ⬝ᵥ (Pi.single a (1 : K) + Pi.single b 1) = 0 := by
  rw [dotProduct_add, onesVec_dotProduct_single, onesVec_dotProduct_single,
    CharTwo.add_self_eq_zero]

omit [CharP K 2] in
theorem ringEquiv_pairVec (σ : K ≃+* K) (a b j : Fin n) :
    σ ((Pi.single a (1 : K) + Pi.single b 1 : Fin n → K) j) =
      (Pi.single a (1 : K) + Pi.single b 1 : Fin n → K) j := by
  rw [pairVec_apply, map_add]
  split_ifs <;> simp

theorem fieldAut_transElt (σ : K ≃+* K) {u : Fin n → K} (hu : onesVec ⬝ᵥ u = 0)
    (hσu : ∀ j, σ (u j) = u j) (c : K) :
    fieldAut n K σ (transElt u hu c) = transElt u hu (σ c) := by
  rw [transElt, orthElt, fieldAut_proj, transElt, orthElt]
  congr 1
  apply Subtype.ext
  change (1 + c • vecMulVec u u).map σ.toRingHom = 1 + σ c • vecMulVec u u
  ext j k
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, vecMulVec_apply,
    smul_eq_mul, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, map_add, map_mul, hσu,
    Matrix.one_apply]
  split_ifs <;> simp

variable [Finite K]

theorem linearFieldPart_eq_one_of_mem_radical (hn : Even n) (hn3 : 3 ≤ n) {i a b : Fin n}
    (hab : a ≠ b) (hia : i ≠ a) (hib : i ≠ b) (α : MulAut (projectiveSL n K))
    (hα : ∀ c : K, (transElt (Pi.single a 1 + Pi.single b 1) (onesVec_dotProduct_pairVec a b)
      c)⁻¹ * α (transElt _ (onesVec_dotProduct_pairVec a b) c) ∈ radical (K := K) i) :
    linearFieldPart K hn3 α = 1 := by
  set u : Fin n → K := Pi.single a 1 + Pi.single b 1 with hudef
  have hu : onesVec ⬝ᵥ u = 0 := onesVec_dotProduct_pairVec a b
  obtain ⟨y, hydef⟩ : ∃ y : Fin n → K, y = Pi.single a 1 + Pi.single i 1 := ⟨_, rfl⟩
  have hy : onesVec ⬝ᵥ y = 0 := hydef ▸ onesVec_dotProduct_pairVec a i
  have huy : u ⬝ᵥ y = 1 := by
    rw [hudef, add_dotProduct, single_dotProduct, single_dotProduct, hydef, Pi.add_apply,
      Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hia.symm, Pi.single_eq_of_ne hab.symm,
      Pi.single_eq_of_ne hib.symm]
    ring
  have hud : u ⬝ᵥ onesVec = 0 := by rw [dotProduct_comm, hu]
  have hdy : onesVec ⬝ᵥ y = 0 := hy
  obtain ⟨A, σ, ε, hε, rfl⟩ := (automorphism_generation hn3).2 α
  rw [linearFieldPart_eq hn3 hε]
  set β : K := u ⬝ᵥ (((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ y) with hβ
  have key : ∀ x : K, ∃ s : K,
      (σ x * β) • ((A : Matrix (Fin n) (Fin n) K) *ᵥ u) = s • onesVec + x • u := by
    intro x
    obtain ⟨v, hvW, c', hv, hρ⟩ := exists_radElt_eq hn (hα x)
    have hδ : (dualAut n K ^ ε) (transElt u hu x) = transElt u hu x := by
      rcases (by omega : ε = 0 ∨ ε = 1) with rfl | rfl
      · rfl
      · rw [pow_one]
        exact orthElt_mem_autFixSubgroup _
    have hαt : (conjAut n K A * fieldAut n K σ * dualAut n K ^ ε) (transElt u hu x) =
        proj n K (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation n K A
          (orthSLElt _ (transMatrix_orth hu (σ x)))) := by
      rw [MulAut.mul_apply, MulAut.mul_apply, hδ,
        fieldAut_transElt σ hu (fun j => ringEquiv_pairVec σ a b j), transElt, orthElt,
        conjAut_proj]
    rw [hαt] at hρ
    set X := CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation n K A
      (orthSLElt _ (transMatrix_orth hu (σ x))) with hX
    set Y := orthSLElt _ (transMatrix_orth hu x) * orthSLElt _ (radicalMatrix_orth hn hv c')
      with hY
    have hπ : proj n K X = proj n K Y := by
      have h1 : proj n K X = transElt u hu x * radElt hn v hv c' := by
        rw [← hρ, mul_inv_cancel_left]
      rw [h1, hY, map_mul]
      rfl
    obtain ⟨l, -, hl⟩ := mem_scalars.1 (proj_eq_proj_iff.1 hπ)
    have hXX : X * X = 1 := by
      rw [hX, ← map_mul]
      have : orthSLElt _ (transMatrix_orth hu (σ x)) * orthSLElt _ (transMatrix_orth hu (σ x)) =
          1 := by
        apply Subtype.ext
        have h := transMatrix_orth hu (σ x)
        rw [transpose_add, transpose_one, transpose_smul, transpose_vecMulVec] at h
        exact h
      rw [this, map_one]
    have hYX : (Y : Matrix (Fin n) (Fin n) K) = (l : K) • (X : Matrix (Fin n) (Fin n) K) := by
      have e : Y = X * (X⁻¹ * Y) := by rw [mul_inv_cancel_left]
      rw [e, Matrix.SpecialLinearGroup.coe_mul, hl, scalar_apply]
      ext a' b'
      rw [mul_diagonal, Matrix.smul_apply, smul_eq_mul, mul_comm]
    have hYd : (Y : Matrix (Fin n) (Fin n) K) *ᵥ onesVec = onesVec := by
      rw [hY, Matrix.SpecialLinearGroup.coe_mul, coe_orthSLElt, coe_orthSLElt, ← mulVec_mulVec,
        radicalMatrix_mulVec_onesVec hn hvW, transMatrix_mulVec, hud, mul_zero, zero_smul,
        add_zero]
    have hl1 : (l : K) = 1 := by
      have hYY : (Y : Matrix (Fin n) (Fin n) K) * (Y : Matrix (Fin n) (Fin n) K) =
          ((l : K) * l) • 1 := by
        rw [hYX, Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← Matrix.SpecialLinearGroup.coe_mul,
          hXX, Matrix.SpecialLinearGroup.coe_one]
      have h2 : ((l : K) * l) • (onesVec : Fin n → K) = onesVec := by
        have h5 : ((Y : Matrix (Fin n) (Fin n) K) * (Y : Matrix (Fin n) (Fin n) K)) *ᵥ
            onesVec = onesVec := by
          rw [← mulVec_mulVec, hYd, hYd]
        rw [hYY, smul_mulVec, one_mulVec] at h5
        exact h5
      have h3 := congrFun h2 ⟨0, by omega⟩
      rw [Pi.smul_apply, onesVec_apply, smul_eq_mul, mul_one] at h3
      have h4 : ((l : K) - 1) ^ 2 = 0 := by
        have e : ((l : K) - 1) ^ 2 = (l : K) * l - 1 - 2 * ((l : K) - 1) := by ring
        rw [e, h3, CharTwo.two_eq_zero]
        ring
      exact sub_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h4)
    rw [hl1, one_smul] at hYX
    have hXy : (X : Matrix (Fin n) (Fin n) K) *ᵥ y = y + (σ x * β) • ((A : Matrix (Fin n) (Fin n)
        K) *ᵥ u) := by
      rw [hX, coe_slConjugation, coe_orthSLElt, ← mulVec_mulVec, ← mulVec_mulVec,
        transMatrix_mulVec, mulVec_add, mulVec_mulVec, ← Units.val_mul, mul_inv_cancel,
        Units.val_one, one_mulVec, mulVec_smul, ← hβ]
    have hRy : radicalMatrix v c' *ᵥ y = y + (v ⬝ᵥ y) • onesVec := by
      rw [radicalMatrix_mulVec, hdy, zero_smul, add_zero, mul_zero, zero_smul, add_zero]
    have hYy : (Y : Matrix (Fin n) (Fin n) K) *ᵥ y = y + (v ⬝ᵥ y) • onesVec + x • u := by
      rw [hY, Matrix.SpecialLinearGroup.coe_mul, coe_orthSLElt, coe_orthSLElt, ← mulVec_mulVec,
        hRy, transMatrix_mulVec, dotProduct_add, huy, dotProduct_smul, hud, smul_zero, add_zero,
        mul_one]
    refine ⟨v ⬝ᵥ y, ?_⟩
    have h := hXy.symm.trans ((congrArg (· *ᵥ y) hYX.symm).trans hYy)
    rw [add_assoc] at h
    exact add_left_cancel h
  obtain ⟨s₁, h₁⟩ := key 1
  rw [map_one, one_mul] at h₁
  refine RingEquiv.ext fun c => ?_
  obtain ⟨s, hs⟩ := key c
  rw [mul_smul, h₁] at hs
  have hi := congrFun hs i
  have ha := congrFun hs a
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, onesVec_apply, mul_one, hudef,
    Pi.single_eq_same, Pi.single_eq_of_ne hia, Pi.single_eq_of_ne hib,
    Pi.single_eq_of_ne hab, add_zero, mul_zero] at hi ha
  change σ c = c
  linear_combination ha - hi

end Faithful

end Nonalt

end CFSG.SeitzReduction.LinearPilot
