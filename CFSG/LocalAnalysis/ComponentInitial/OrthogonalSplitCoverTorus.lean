module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitCoverLevi

public section

namespace CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit

open Matrix QuadraticMap CFSG.ClassicalGroups.Orthogonal Module CFSG.LieType.Universal.Spin
open scoped commutatorElement

variable {r : ℕ} {K : Type*} [Field K]

variable (r K) in
@[expose] def swapAll : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K) :=
  LinearEquiv.funCongrLeft K K (Equiv.sumComm (Fin r) (Fin r))

theorem swapAll_apply (v : Fin r ⊕ Fin r → K) (c : Fin r ⊕ Fin r) :
    swapAll r K v c = v c.swap :=
  rfl

theorem swapAll_mem_orthogonalGroup :
    swapAll r K ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus r K) := by
  refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.2 fun v => ?_
  rw [quadPlus_apply, quadPlus_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  change v (Sum.inr j) * v (Sum.inl j) = v (Sum.inl j) * v (Sum.inr j)
  exact mul_comm _ _

theorem swapAll_mul_self : swapAll r K * swapAll r K = 1 :=
  LinearEquiv.ext fun v => funext fun c => by
    rw [LinearEquiv.mul_apply, swapAll_apply, swapAll_apply, Sum.swap_swap]
    rfl

theorem swapAll_mul_torusElt_mul_swapAll (d : Fin r → Kˣ) :
    swapAll r K * torusElt r K d * swapAll r K = torusElt r K d⁻¹ := by
  refine LinearEquiv.ext fun v => funext fun c => ?_
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, swapAll_apply, torusElt_apply, swapAll_apply,
    Sum.swap_swap, torusElt_apply]
  rcases c with i | i <;> simp

theorem commutatorElement_swapAll_torusElt (d : Fin r → Kˣ) :
    ⁅swapAll r K, torusElt r K d⁆ = torusElt r K (d⁻¹ * d⁻¹) := by
  have hinv : (swapAll r K)⁻¹ = swapAll r K := inv_eq_of_mul_eq_one_right swapAll_mul_self
  rw [commutatorElement_def, hinv, swapAll_mul_torusElt_mul_swapAll, ← map_inv, ← map_mul]

theorem torusElt_mem_orthogonalGroup (d : Fin r → Kˣ) :
    torusElt r K d ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus r K) :=
  posBorel_le_orthogonalGroup (torusElt_mem_posBorel d)

theorem eq_of_mul_self_eq_mul_self [CharP K 2] {a b : K} (h : a * a = b * b) : a = b := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have h' : (a - b) ^ 2 = 0 := by linear_combination h + b * (b - a) * h2
  exact sub_eq_zero.1 (pow_eq_zero_iff (by norm_num) |>.1 h')

theorem torusElt_mem_orthElementaryGroup [CharP K 2] [Finite K] (hr : 3 ≤ r) (d : Fin r → Kˣ) :
    torusElt r K d ∈ orthElementaryGroup (quadPlus r K) := by
  have : Finite Kˣ := Finite.of_injective (fun u : Kˣ => (u : K)) fun _ _ => Units.ext
  have hinj : Function.Injective fun x : Kˣ => x⁻¹ * x⁻¹ := by
    intro x y h
    have h' : ((x⁻¹ : Kˣ) : K) * ((x⁻¹ : Kˣ) : K) = ((y⁻¹ : Kˣ) : K) * ((y⁻¹ : Kˣ) : K) := by
      rw [← Units.val_mul, ← Units.val_mul]
      exact congrArg Units.val h
    exact inv_injective (Units.ext (eq_of_mul_self_eq_mul_self h'))
  choose e he using fun i => (Finite.injective_iff_surjective.1 hinj) (d i)
  have hd : d = e⁻¹ * e⁻¹ := funext fun i => (he i).symm
  rw [hd, ← commutatorElement_swapAll_torusElt, ← commutator_orthogonalGroup_quadPlus hr]
  exact Subgroup.commutator_mem_commutator swapAll_mem_orthogonalGroup
    (torusElt_mem_orthogonalGroup e)

theorem torusElt_eq_levi (d : Fin r → Kˣ) : torusElt r K d = levi r K (diagGL d) := by
  apply LinearEquiv.toLinearMap_injective
  apply LinearMap.toMatrix'.injective
  rw [toMatrix'_torusElt, toMatrix'_levi_eq, Matrix.mul_zero]
  simp [diagGL, diagonal_transpose]

theorem torusElt_mul_radical_mul_inv (d : Fin r → Kˣ) (B : Matrix (Fin r) (Fin r) K) :
    torusElt r K d * radical r K (Multiplicative.ofAdd B) * (torusElt r K d)⁻¹ =
      radical r K (Multiplicative.ofAdd
        (diagonal (fun i => (d i : K)) * B * diagonal (fun i => (d i : K)))) := by
  rw [torusElt_eq_levi, levi_mul_radical_mul_inv]
  simp [diagGL, diagonal_transpose]

@[expose] def altUnit (i j : Fin r) : Matrix (Fin r) (Fin r) K :=
  Matrix.single i j 1 - Matrix.single j i 1

theorem altUnit_mem_altSubgroup (i j : Fin r) :
    (altUnit i j : Matrix (Fin r) (Fin r) K) ∈ altSubgroup r K := by
  refine ⟨?_, fun k => ?_⟩
  · rw [altUnit, transpose_sub, transpose_single, transpose_single, neg_sub]
  · rw [altUnit, Matrix.sub_apply, Matrix.single_apply, Matrix.single_apply]
    by_cases hk : i = k
    · subst hk
      by_cases hj : j = i
      · simp [hj]
      · simp [hj]
    · simp [hk]

theorem smul_mem_altSubgroup (a : K) {B : Matrix (Fin r) (Fin r) K} (hB : B ∈ altSubgroup r K) :
    a • B ∈ altSubgroup r K :=
  ⟨by rw [transpose_smul, hB.1, smul_neg], fun k => by rw [Matrix.smul_apply, hB.2 k, smul_zero]⟩

theorem smul_altUnit_mem_altSubgroup (i j : Fin r) (a : K) :
    a • (altUnit i j : Matrix (Fin r) (Fin r) K) ∈ altSubgroup r K :=
  smul_mem_altSubgroup a (altUnit_mem_altSubgroup i j)

theorem diagonal_mul_altUnit_mul_diagonal (d : Fin r → K) (i j : Fin r) (a : K) :
    diagonal d * (a • altUnit i j) * diagonal d = (d i * d j * a) • altUnit i j := by
  rw [altUnit, smul_sub, Matrix.mul_sub, Matrix.sub_mul, Matrix.smul_single, Matrix.smul_single,
    TauCeti.diagonal_mul_single_mul_diagonal, TauCeti.diagonal_mul_single_mul_diagonal, smul_sub,
    Matrix.smul_single, Matrix.smul_single]
  congr 2 <;> ring

theorem torusElt_mul_levi_rootElt_mul_inv (d : Fin r → Kˣ) (i j : Fin r) (a : K) :
    torusElt r K d * levi r K (SpecialLinearGroup.toGL (LinearCover.rootElt i j a)) *
        (torusElt r K d)⁻¹ =
      levi r K (SpecialLinearGroup.toGL
        (LinearCover.rootElt i j ((d i : K) * a * (((d j)⁻¹ : Kˣ) : K)))) := by
  by_cases hij : i = j
  · subst hij
    rw [LinearCover.rootElt_self, LinearCover.rootElt_self, map_one, map_one, mul_one,
      mul_inv_cancel]
  rw [torusElt_eq_levi, ← map_inv, ← map_mul, ← map_mul]
  congr 1
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, SpecialLinearGroup.coe_GL_coe_matrix,
    SpecialLinearGroup.coe_GL_coe_matrix, LinearCover.coe_rootElt_of_ne hij,
    LinearCover.coe_rootElt_of_ne hij]
  change diagonal (fun k => (d k : K)) * transvection i j a *
    diagonal (fun k => (((d k)⁻¹ : Kˣ) : K)) = _
  exact TauCeti.diagonal_mul_transvection_mul_diagonal (fun k => by simp) a

theorem transvection_mul_altUnit_mul_transpose_of_ne {i j m : Fin r} (hmi : m ≠ i) (hmj : m ≠ j)
    (a b : K) :
    transvection i m a * (b • altUnit i j) * (transvection i m a)ᵀ = b • altUnit i j := by
  simp [transvection, altUnit, Matrix.add_mul, Matrix.mul_add, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.single_mul_single_of_ne, hmi, hmj, hmi.symm, hmj.symm]

theorem transvection_mul_altUnit_mul_transpose {i j m : Fin r} (hmj : m ≠ j) (a b : K) :
    transvection i m a * (b • altUnit m j) * (transvection i m a)ᵀ =
      b • altUnit m j + (a * b) • altUnit i j := by
  simp [transvection, altUnit, Matrix.add_mul, Matrix.mul_add, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.single_mul_single_of_ne, hmj, hmj.symm]
  simp only [smul_add, smul_sub, Matrix.smul_single, smul_eq_mul, mul_one]
  rw [show b * a = a * b from mul_comm b a]
  abel

theorem levi_rootElt_mul_radical_comm {i j m : Fin r} (hmi : m ≠ i) (hmj : m ≠ j) (a b : K) :
    levi r K (SpecialLinearGroup.toGL (LinearCover.rootElt i m a)) *
        radical r K (Multiplicative.ofAdd (b • altUnit i j)) =
      radical r K (Multiplicative.ofAdd (b • altUnit i j)) *
        levi r K (SpecialLinearGroup.toGL (LinearCover.rootElt i m a)) := by
  rw [← mul_inv_eq_iff_eq_mul, levi_mul_radical_mul_inv, SpecialLinearGroup.coe_GL_coe_matrix,
    LinearCover.coe_rootElt_of_ne (Ne.symm hmi), transvection_mul_altUnit_mul_transpose_of_ne hmi hmj]

theorem commutatorElement_levi_rootElt_radical {i j m : Fin r} (hmi : m ≠ i) (hmj : m ≠ j)
    (a b : K) :
    ⁅levi r K (SpecialLinearGroup.toGL (LinearCover.rootElt i m a)),
        radical r K (Multiplicative.ofAdd (b • altUnit m j))⁆ =
      radical r K (Multiplicative.ofAdd ((a * b) • altUnit i j)) := by
  rw [commutatorElement_def, levi_mul_radical_mul_inv, SpecialLinearGroup.coe_GL_coe_matrix,
    LinearCover.coe_rootElt_of_ne (Ne.symm hmi), transvection_mul_altUnit_mul_transpose hmj,
    ofAdd_add, map_mul, ← map_inv, ← map_mul, ← map_mul]
  congr 1
  rw [mul_comm, inv_mul_cancel_left]

variable (r K) in
@[expose] noncomputable def radicalE :
    Multiplicative (altSubgroup r K) →* orthElementaryGroup (quadPlus r K) :=
  ((radical r K).comp (AddMonoidHom.toMultiplicative (altSubgroup r K).subtype)).codRestrict _
    fun B => posUnip_le_orthElementaryGroup (radical_mem_posUnip B.toAdd.2)

theorem coe_radicalE (B : Multiplicative (altSubgroup r K)) :
    (radicalE r K B : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) =
      radical r K (Multiplicative.ofAdd (B.toAdd : Matrix (Fin r) (Fin r) K)) :=
  rfl

theorem radicalE_injective : Function.Injective (radicalE r K) := by
  intro B C h
  have h' := radical_injective (congrArg Subtype.val h)
  exact Multiplicative.toAdd.injective (Subtype.ext (Multiplicative.ofAdd.injective h'))

theorem radicalE_mul_comm (B C : Multiplicative (altSubgroup r K)) :
    radicalE r K B * radicalE r K C = radicalE r K C * radicalE r K B := by
  rw [← map_mul, ← map_mul, mul_comm]

variable (r K) in
@[expose] noncomputable def radRoot (i j : Fin r) (a : K) : orthElementaryGroup (quadPlus r K) :=
  radicalE r K (Multiplicative.ofAdd ⟨a • altUnit i j, smul_altUnit_mem_altSubgroup i j a⟩)

theorem coe_radRoot (i j : Fin r) (a : K) :
    (radRoot r K i j a : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) =
      radical r K (Multiplicative.ofAdd (a • altUnit i j)) :=
  rfl

theorem radRoot_add (i j : Fin r) (a b : K) :
    radRoot r K i j (a + b) = radRoot r K i j a * radRoot r K i j b := by
  rw [radRoot, radRoot, radRoot, ← map_mul, ← ofAdd_add]
  congr 2
  exact Subtype.ext (add_smul a b _)

theorem altUnit_swap (i j : Fin r) : (altUnit j i : Matrix (Fin r) (Fin r) K) = -altUnit i j := by
  rw [altUnit, altUnit, neg_sub]

theorem radRoot_swap (i j : Fin r) (b : K) : radRoot r K j i b = radRoot r K i j (-b) := by
  rw [radRoot, radRoot]
  congr 2
  apply Subtype.ext
  change b • altUnit j i = -b • altUnit i j
  rw [altUnit_swap, smul_neg, neg_smul]

theorem radRoot_mul_comm (i j k l : Fin r) (a b : K) :
    radRoot r K i j a * radRoot r K k l b = radRoot r K k l b * radRoot r K i j a :=
  radicalE_mul_comm _ _

theorem radicalE_mem_closure_radRoot (B : Multiplicative (altSubgroup r K)) :
    radicalE r K B ∈ Subgroup.closure {g | ∃ i j a, i < j ∧ radRoot r K i j a = g} := by
  set S := Finset.univ.filter fun p : Fin r × Fin r => p.1 < p.2
  have hB : B = ∏ p ∈ S, Multiplicative.ofAdd
      (⟨(B.toAdd : Matrix (Fin r) (Fin r) K) p.1 p.2 • altUnit p.1 p.2,
        smul_altUnit_mem_altSubgroup p.1 p.2 _⟩ : altSubgroup r K) := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    rw [toAdd_prod, AddSubgroup.val_finsetSum]
    exact eq_sum_of_alternating B.toAdd.2.1 B.toAdd.2.2
  have hmem : B ∈ (Subgroup.closure {g | ∃ i j a, i < j ∧ radRoot r K i j a = g}).comap
      (radicalE r K) := by
    rw [hB]
    exact Subgroup.prod_mem _ fun p hp => Subgroup.subset_closure
      ⟨p.1, p.2, _, (Finset.mem_filter.1 hp).2, rfl⟩
  exact hmem

section Levi

variable [CharP K 2]

variable (r K) in
@[expose] noncomputable def leviSL (hr : 3 ≤ r) :
    SpecialLinearGroup (Fin r) K →* orthElementaryGroup (quadPlus r K) :=
  ((levi r K).comp SpecialLinearGroup.toGL).codRestrict _ fun A =>
    levi_toGL_mem_orthElementaryGroup hr A

theorem coe_leviSL (hr : 3 ≤ r) (A : SpecialLinearGroup (Fin r) K) :
    (leviSL r K hr A : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) =
      levi r K (SpecialLinearGroup.toGL A) :=
  rfl

theorem leviSL_injective (hr : 3 ≤ r) : Function.Injective (leviSL r K hr) := fun _ _ h =>
  SpecialLinearGroup.toGL_injective (levi_injective (congrArg Subtype.val h))

variable (r K) in
@[expose] noncomputable def leviRoot (hr : 3 ≤ r) (i j : Fin r) (a : K) :
    orthElementaryGroup (quadPlus r K) :=
  leviSL r K hr (LinearCover.rootElt i j a)

theorem leviRoot_mul_radRoot_comm (hr : 3 ≤ r) {i j m : Fin r} (hmi : m ≠ i) (hmj : m ≠ j)
    (a b : K) :
    leviRoot r K hr i m a * radRoot r K i j b = radRoot r K i j b * leviRoot r K hr i m a :=
  Subtype.ext (levi_rootElt_mul_radical_comm hmi hmj a b)

theorem commutatorElement_leviRoot_radRoot (hr : 3 ≤ r) {i j m : Fin r} (hmi : m ≠ i)
    (hmj : m ≠ j) (a b : K) :
    ⁅leviRoot r K hr i m a, radRoot r K m j b⁆ = radRoot r K i j (a * b) := by
  apply Subtype.ext
  have h := commutatorElement_levi_rootElt_radical (K := K) hmi hmj a b
  rw [commutatorElement_def] at h ⊢
  exact h

theorem leviSL_mul_radicalE_mul_inv (hr : 3 ≤ r) (A : SpecialLinearGroup (Fin r) K)
    (B : Multiplicative (altSubgroup r K)) :
    leviSL r K hr A * radicalE r K B * (leviSL r K hr A)⁻¹ =
      radicalE r K (Multiplicative.ofAdd ⟨(A : Matrix (Fin r) (Fin r) K) *
        (B.toAdd : Matrix (Fin r) (Fin r) K) * (A : Matrix (Fin r) (Fin r) K)ᵀ,
          congr_mem_altSubgroup _ B.toAdd.2⟩) := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_leviSL, coe_radicalE,
    coe_radicalE, levi_mul_radical_mul_inv, SpecialLinearGroup.coe_GL_coe_matrix]
  rfl

theorem exists_leviSL_radicalE_of_mem_posUnip (hr : 3 ≤ r) {g : orthElementaryGroup (quadPlus r K)}
    (hg : (g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) ∈ posUnip r K) :
    ∃ A ∈ LinearFlag.unitriangular r K, ∃ B : Multiplicative (altSubgroup r K),
      g = leviSL r K hr A * radicalE r K B := by
  obtain ⟨A, B, hA, h1, hB, hgAB⟩ := mem_posUnip_iff_levi_radical.1 hg
  have hdet : (A : Matrix (Fin r) (Fin r) K).det = 1 := by
    rw [Matrix.det_of_isUpperTriangular hA]
    exact Finset.prod_eq_one fun i _ => h1 i
  refine ⟨⟨A, hdet⟩, ⟨fun i j hij => hA hij, h1⟩, Multiplicative.ofAdd ⟨B, hB⟩, Subtype.ext ?_⟩
  rw [Subgroup.coe_mul, hgAB]
  congr 1
  show levi r K A = levi r K (SpecialLinearGroup.toGL ⟨A, hdet⟩)
  exact congrArg (levi r K) (Units.ext rfl)

theorem leviSL_eq_one_of_eq_radicalE (hr : 3 ≤ r) {A : SpecialLinearGroup (Fin r) K}
    {B : Multiplicative (altSubgroup r K)} (h : leviSL r K hr A = radicalE r K B) :
    leviSL r K hr A = 1 := by
  have h' := congrArg Subtype.val h
  rw [coe_leviSL, coe_radicalE] at h'
  obtain ⟨hA, -⟩ := eq_one_of_levi_eq_radical h'
  apply Subtype.ext
  rw [coe_leviSL, hA, map_one]
  rfl

section Torus

variable [Finite K]

variable (r K) in
@[expose] noncomputable def torusE (hr : 3 ≤ r) :
    (Fin r → Kˣ) →* orthElementaryGroup (quadPlus r K) :=
  (torusElt r K).codRestrict _ fun d => torusElt_mem_orthElementaryGroup hr d

theorem coe_torusE (hr : 3 ≤ r) (d : Fin r → Kˣ) :
    (torusE r K hr d : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) = torusElt r K d :=
  rfl

theorem torusE_mul_radRoot_mul_inv (hr : 3 ≤ r) (d : Fin r → Kˣ) (i j : Fin r) (a : K) :
    torusE r K hr d * radRoot r K i j a * (torusE r K hr d)⁻¹ =
      radRoot r K i j ((d i : K) * d j * a) := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_torusE, coe_radRoot, coe_radRoot,
    torusElt_mul_radical_mul_inv, diagonal_mul_altUnit_mul_diagonal]

theorem torusE_mul_leviRoot_mul_inv (hr : 3 ≤ r) (d : Fin r → Kˣ) (i j : Fin r) (a : K) :
    torusE r K hr d * leviRoot r K hr i j a * (torusE r K hr d)⁻¹ =
      leviRoot r K hr i j ((d i : K) * a * (((d j)⁻¹ : Kˣ) : K)) :=
  Subtype.ext (torusElt_mul_levi_rootElt_mul_inv d i j a)

theorem torusE_const_mul_radicalE_mul_inv (hr : 3 ≤ r) (s : Kˣ)
    (B : Multiplicative (altSubgroup r K)) :
    torusE r K hr (fun _ => s) * radicalE r K B * (torusE r K hr (fun _ => s))⁻¹ =
      radicalE r K (Multiplicative.ofAdd ⟨((s : K) * s) • (B.toAdd : Matrix (Fin r) (Fin r) K),
        smul_mem_altSubgroup _ B.toAdd.2⟩) := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_torusE, coe_radicalE,
    coe_radicalE, torusElt_mul_radical_mul_inv]
  congr 2
  show _ = ((s : K) * s) • (B.toAdd : Matrix (Fin r) (Fin r) K)
  ext k l
  simp only [diagonal_mul, mul_diagonal, Matrix.smul_apply, smul_eq_mul]
  ring

theorem torusE_const_mul_leviSL_comm (hr : 3 ≤ r) (s : Kˣ) (A : SpecialLinearGroup (Fin r) K) :
    torusE r K hr (fun _ => s) * leviSL r K hr A = leviSL r K hr A * torusE r K hr (fun _ => s) := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_torusE, coe_leviSL, torusElt_eq_levi, ← map_mul,
    ← map_mul]
  congr 1
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  ext k l
  simp [diagGL, diagonal_mul, mul_diagonal, mul_comm]

end Torus

end Levi

end CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
