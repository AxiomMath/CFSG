module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitEta

public section

namespace CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit

open Matrix QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
open scoped commutatorElement

variable {r : ℕ}

@[expose] def coordWt (c : Fin r ⊕ Fin r) : Fin r → ℤ :=
  Sum.elim (eps r) (fun i => -eps r i) c

@[simp] theorem coordWt_inl (i : Fin r) : coordWt (Sum.inl i : Fin r ⊕ Fin r) = eps r i := rfl

@[simp] theorem coordWt_inr (i : Fin r) : coordWt (Sum.inr i : Fin r ⊕ Fin r) = -eps r i := rfl

theorem coordWt_swap (c : Fin r ⊕ Fin r) : coordWt c.swap = -coordWt c := by
  rcases c with i | i <;> simp

theorem coordWt_dotProduct (c d : Fin r ⊕ Fin r) :
    coordWt c ⬝ᵥ coordWt d = if c = d then 1 else if c = d.swap then -1 else 0 := by
  rcases c with i | i <;> rcases d with j | j <;>
    simp [eps, Pi.single_apply, eq_comm] <;> split_ifs <;> simp

theorem coordWt_injective : Function.Injective (coordWt (r := r)) := by
  intro c d h
  have h1 : coordWt c ⬝ᵥ coordWt d = 1 := by simp [h, coordWt_dotProduct]
  rw [coordWt_dotProduct] at h1
  by_contra hcd
  rw [ite_eq_right hcd] at h1
  split_ifs at h1
  omega

theorem coordWt_sub_mem_roots {a b : Fin r ⊕ Fin r} (h : coordIdx a ≠ coordIdx b) :
    coordWt a - coordWt b ∈ roots r := by
  rcases a with i | i <;> rcases b with j | j <;>
    simp only [coordIdx_inl, coordIdx_inr] at h <;> rcases lt_or_gt_of_ne h with hij | hij
  · exact ⟨i, j, hij, Or.inl rfl⟩
  · exact ⟨j, i, hij, Or.inr (Or.inl (by simp only [coordWt_inl]; abel))⟩
  · exact ⟨i, j, hij, Or.inr (Or.inr (Or.inl (by simp only [coordWt_inl, coordWt_inr]; abel)))⟩
  · exact ⟨j, i, hij, Or.inr (Or.inr (Or.inl (by simp only [coordWt_inl, coordWt_inr]; abel)))⟩
  · exact ⟨i, j, hij, Or.inr (Or.inr (Or.inr (by simp only [coordWt_inl, coordWt_inr])))⟩
  · exact ⟨j, i, hij, Or.inr (Or.inr (Or.inr (by simp only [coordWt_inl, coordWt_inr]; abel)))⟩
  · exact ⟨i, j, hij, Or.inr (Or.inl (by simp only [coordWt_inr]; abel))⟩
  · exact ⟨j, i, hij, Or.inl (by simp only [coordWt_inr]; abel)⟩

theorem coordWt_sub_dotProduct_self {a b : Fin r ⊕ Fin r} (h : coordIdx a ≠ coordIdx b) :
    (coordWt a - coordWt b) ⬝ᵥ (coordWt a - coordWt b) = 2 := by
  simp [sub_dotProduct, dotProduct_sub, coordWt_dotProduct, ne_of_coordIdx_ne h,
    ne_swap_of_coordIdx_ne h, ne_of_coordIdx_ne (Ne.symm h), ne_swap_of_coordIdx_ne (Ne.symm h)]

theorem eq_or_eq_of_coordWt_sub_eq {a b c d : Fin r ⊕ Fin r} (hab : coordIdx a ≠ coordIdx b)
    (hcd : coordIdx c ≠ coordIdx d) (h : coordWt a - coordWt b = coordWt c - coordWt d) :
    (c = a ∧ d = b) ∨ (c = b.swap ∧ d = a.swap) := by
  have h1 : (coordWt c - coordWt d) ⬝ᵥ coordWt a = 1 := by
    rw [← h, sub_dotProduct, coordWt_dotProduct, coordWt_dotProduct,
      ite_eq_right (ne_of_coordIdx_ne (Ne.symm hab)),
      ite_eq_right (ne_swap_of_coordIdx_ne (Ne.symm hab))]
    simp
  rw [sub_dotProduct, coordWt_dotProduct, coordWt_dotProduct] at h1
  by_cases hca : c = a
  · subst hca
    exact Or.inl ⟨rfl, coordWt_injective (by linear_combination h)⟩
  by_cases hda : d = a.swap
  · subst hda
    refine Or.inr ⟨coordWt_injective ?_, rfl⟩
    rw [coordWt_swap] at h ⊢
    linear_combination -h
  rw [ite_eq_right hca, ite_eq_right hda] at h1
  split_ifs at h1 <;> omega

theorem dotProduct_self_of_mem_roots {α : Fin r → ℤ} (hα : α ∈ roots r) : α ⬝ᵥ α = 2 := by
  obtain ⟨i, j, hij, h | h | h | h⟩ := hα <;> subst h
  · exact coordWt_sub_dotProduct_self (a := Sum.inl i) (b := Sum.inl j) hij.ne
  · have := coordWt_sub_dotProduct_self (a := Sum.inl j) (b := Sum.inl i) hij.ne'
    simp only [coordWt_inl] at this
    rwa [neg_add_eq_sub]
  · have := coordWt_sub_dotProduct_self (a := Sum.inl i) (b := Sum.inr j) hij.ne
    simp only [coordWt_inl, coordWt_inr, sub_neg_eq_add] at this
    exact this
  · have := coordWt_sub_dotProduct_self (a := Sum.inr i) (b := Sum.inl j) hij.ne
    simp only [coordWt_inl, coordWt_inr] at this
    exact this

theorem dotProduct_eq_neg_one_of_add_mem_roots {α β : Fin r → ℤ} (hα : α ∈ roots r)
    (hβ : β ∈ roots r) (h : α + β ∈ roots r) : α ⬝ᵥ β = -1 := by
  have h2 := dotProduct_self_of_mem_roots h
  rw [add_dotProduct, dotProduct_add, dotProduct_add, dotProduct_self_of_mem_roots hα,
    dotProduct_self_of_mem_roots hβ, dotProduct_comm β α] at h2
  linarith

theorem zero_notMem_roots : (0 : Fin r → ℤ) ∉ roots r := fun h => by
  have := dotProduct_self_of_mem_roots h
  simp at this

section AutMat

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [Field K]

@[expose] noncomputable def autMat : ((ι → K) ≃ₗ[K] (ι → K)) →* Matrix ι ι K :=
  (LinearMap.toMatrixAlgEquiv' : ((ι → K) →ₗ[K] (ι → K)) ≃ₐ[K] Matrix ι ι K).toMonoidHom.comp
    LinearEquiv.automorphismGroup.toLinearMapMonoidHom

theorem autMat_apply (g : (ι → K) ≃ₗ[K] (ι → K)) :
    autMat g = LinearMap.toMatrix' (g : (ι → K) →ₗ[K] (ι → K)) :=
  rfl

theorem autMat_injective : Function.Injective (autMat (ι := ι) (K := K)) := fun _ _ hgh =>
  LinearEquiv.toLinearMap_injective (LinearMap.toMatrix'.injective hgh)

theorem apply_eq_autMat_mulVec (g : (ι → K) ≃ₗ[K] (ι → K)) (v : ι → K) : g v = autMat g *ᵥ v :=
  (LinearMap.toMatrix'_mulVec _ v).symm

theorem commutatorElement_eq_iff {G : Type*} [Group G] {g h k : G} :
    ⁅g, h⁆ = k ↔ g * h = k * h * g := by
  rw [commutatorElement_def, mul_inv_eq_iff_eq_mul, mul_inv_eq_iff_eq_mul]

end AutMat

section RpElt

variable {K : Type*} [Field K]

@[expose] noncomputable def rpElt (a b : Fin r ⊕ Fin r) (t : K) :
    (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K) :=
  eichler (quadPlus r K) (Pi.single a 1) ((-t) • Pi.single b.swap 1)

variable (K) in
@[expose] def rpMat (a b : Fin r ⊕ Fin r) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K :=
  single a b 1 - single b.swap a.swap 1

theorem rpElt_apply {a b : Fin r ⊕ Fin r} (h : coordIdx a ≠ coordIdx b) (t : K)
    (v : Fin r ⊕ Fin r → K) :
    rpElt a b t v = v + (t * v b) • Pi.single a 1 - (t * v a.swap) • Pi.single b.swap 1 := by
  have hw : polar (quadPlus r K) (Pi.single a 1) ((-t) • Pi.single b.swap 1) = 0 :=
    polar_single_smul_single (swap_ne_swap_of_coordIdx_ne (Ne.symm h)) _
  rw [rpElt, eichler_apply (quadPlus_single a) hw]
  simp only [polar_smul_right_eq, polar_single, Sum.swap_swap, map_smul_eq_sq, quadPlus_single,
    mul_zero, zero_mul, add_zero]
  module

theorem autMat_rpElt {a b : Fin r ⊕ Fin r} (h : coordIdx a ≠ coordIdx b) (t : K) :
    autMat (rpElt a b t) = 1 + t • rpMat K a b := by
  rw [autMat_apply, ← LinearMap.toMatrix'_toLin' (1 + t • rpMat K a b)]
  congr 1
  refine LinearMap.ext fun v => funext fun x => ?_
  rw [LinearEquiv.coe_coe, rpElt_apply h, Matrix.toLin'_apply, Matrix.add_mulVec,
    Matrix.one_mulVec, Matrix.smul_mulVec, rpMat, Matrix.sub_mulVec, single_mulVec,
    single_mulVec]
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply,
    Function.update_apply, Pi.zero_apply]
  split_ifs <;> ring

theorem rpElt_swap_swap {a b : Fin r ⊕ Fin r} (h : coordIdx a ≠ coordIdx b) (t : K) :
    rpElt b.swap a.swap t = rpElt a b (-t) := by
  have h' : coordIdx b.swap ≠ coordIdx a.swap := by
    rw [coordIdx_swap, coordIdx_swap]
    exact Ne.symm h
  apply autMat_injective
  rw [autMat_rpElt h', autMat_rpElt h, rpMat, rpMat, Sum.swap_swap, Sum.swap_swap, neg_smul,
    ← smul_neg, neg_sub]

theorem exists_rootElt_eq_rpElt {α : Fin r → ℤ} (hα : α ∈ roots r) :
    ∃ a b : Fin r ⊕ Fin r, coordIdx a ≠ coordIdx b ∧ coordWt a - coordWt b = α ∧
      (∀ t : K, rootElt r K α t = rpElt a b t) ∧ ∀ t : K, rootElt r K (-α) t = rpElt b a t := by
  obtain ⟨i, j, hij, h | h | h | h⟩ := hα <;> subst h
  · refine ⟨Sum.inl i, Sum.inl j, hij.ne, rfl, fun t => rootElt_eps_sub_eps' hij t,
      fun t => ?_⟩
    rw [neg_sub, sub_eq_neg_add, rootElt_neg_eps_add_eps' hij]
    rfl
  · refine ⟨Sum.inl j, Sum.inl i, hij.ne', by simp only [coordWt_inl]; abel,
      fun t => rootElt_neg_eps_add_eps' hij t, fun t => ?_⟩
    rw [neg_add, neg_neg, ← sub_eq_add_neg, rootElt_eps_sub_eps' hij]
    rfl
  · refine ⟨Sum.inl i, Sum.inr j, hij.ne, by simp only [coordWt_inl, coordWt_inr]; abel,
      fun t => rootElt_eps_add_eps' hij t, fun t => ?_⟩
    rw [neg_add, ← sub_eq_add_neg, rootElt_neg_eps_sub_eps' hij]
    rfl
  · refine ⟨Sum.inr j, Sum.inl i, hij.ne', by simp only [coordWt_inl, coordWt_inr]; abel,
      fun t => rootElt_neg_eps_sub_eps' hij t, fun t => ?_⟩
    rw [neg_sub, sub_neg_eq_add, add_comm, rootElt_eps_add_eps' hij]
    rfl

theorem exists_sign_rootElt_eq_rpElt {a b : Fin r ⊕ Fin r} (h : coordIdx a ≠ coordIdx b) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
      (∀ t : K, rootElt r K (coordWt a - coordWt b) t = rpElt a b ((ε : K) * t)) ∧
      ∀ t : K, rootElt r K (coordWt b - coordWt a) t = rpElt b a ((ε : K) * t) := by
  obtain ⟨c, d, hcd, hw, h1, h2⟩ := exists_rootElt_eq_rpElt (K := K) (coordWt_sub_mem_roots h)
  rw [neg_sub] at h2
  rcases eq_or_eq_of_coordWt_sub_eq h hcd hw.symm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨1, Or.inl rfl, fun t => by rw [h1, Int.cast_one, one_mul],
      fun t => by rw [h2, Int.cast_one, one_mul]⟩
  · refine ⟨-1, Or.inr rfl, fun t => ?_, fun t => ?_⟩
    · rw [h1, rpElt_swap_swap h, Int.cast_neg, Int.cast_one, neg_one_mul]
    · rw [h2, rpElt_swap_swap (Ne.symm h), Int.cast_neg, Int.cast_one, neg_one_mul]

end RpElt

end CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
