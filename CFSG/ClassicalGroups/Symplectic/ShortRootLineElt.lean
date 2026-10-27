module

public import CFSG.ClassicalGroups.Symplectic.StandardForm
public import CFSG.ClassicalGroups.Alternating.I4SpDefs
public import CFSG.ClassicalGroups.Alternating.PointRadicalFixedCard
public import CFSG.LieType.Universal.SymplecticExtras.Matrices

public section

namespace CFSG.ClassicalGroups.Symplectic

open CFSG.ClassicalGroups.Alternating CFSG.LieType.Universal.Symplectic TauCeti.GLSymplecticFin
open Matrix

variable {m : ℕ} {K : Type} [Field K] [CharP K 2]

theorem spForm_apply_single_inl (x : Fin m ⊕ Fin m → K) (i : Fin m) (c : K) :
    spForm m K x (Pi.single (Sum.inl i) c) = x (Sum.inr i) * c := by
  rw [spForm_apply]
  simp only [dotProduct, Fintype.sum_sum_type, spJ_mulVec_inl, spJ_mulVec_inr, Pi.single_apply,
    Sum.inl.injEq, Sum.inr_ne_inl, reduceIte]
  simp [CharTwo.neg_eq]

omit [CharP K 2] in
theorem spForm_apply_single_inr (x : Fin m ⊕ Fin m → K) (i : Fin m) (c : K) :
    spForm m K x (Pi.single (Sum.inr i) c) = x (Sum.inl i) * c := by
  rw [spForm_apply]
  simp only [dotProduct, Fintype.sum_sum_type, spJ_mulVec_inl, spJ_mulVec_inr, Pi.single_apply,
    Sum.inr.injEq, Sum.inl_ne_inr, reduceIte]
  simp

theorem spEquiv_elt_difference (i j : Fin m) (hij : i ≠ j) (c : K) :
    spEquiv (SpExtras.elt (.difference i j hij) c) =
      lineElt spForm_isAlt (Pi.single (Sum.inl i) 1) (Pi.single (Sum.inr j) c) := by
  have hac : spForm m K (Pi.single (Sum.inl i) 1) (Pi.single (Sum.inr j) c) = 0 := by
    rw [spForm_apply_single_inr]
    simp [hij]
  apply Gsp.ext'
  intro x
  rw [spEquiv_app, lineElt_app spForm_isAlt hac, ← SpExtras.mat_apply, SpExtras.mat_elt,
    spForm_apply_single_inl, spForm_apply_single_inr]
  funext k
  rcases k with k | k <;>
    simp [Matrix.add_mulVec, Matrix.smul_mulVec, SpExtras.E, Matrix.sub_mulVec,
      Matrix.single_mulVec, Pi.single_apply, CharTwo.sub_eq_add, mul_comm, Function.update_apply,
      mul_ite]

theorem spEquiv_elt_positiveSum (i j : Fin m) (hij : i < j) (c : K) :
    spEquiv (SpExtras.elt (.positiveSum i j hij) c) =
      lineElt spForm_isAlt (Pi.single (Sum.inl i) 1) (Pi.single (Sum.inl j) c) := by
  have hac : spForm m K (Pi.single (Sum.inl i) 1) (Pi.single (Sum.inl j) c) = 0 := by
    rw [spForm_apply_single_inl]
    simp
  apply Gsp.ext'
  intro x
  rw [spEquiv_app, lineElt_app spForm_isAlt hac, ← SpExtras.mat_apply, SpExtras.mat_elt,
    spForm_apply_single_inl, spForm_apply_single_inl]
  funext k
  rcases k with k | k
  · simp [Matrix.add_mulVec, SpExtras.E, Matrix.single_mulVec, Pi.single_apply, mul_comm,
      Function.update_apply]
    abel
  · simp [Matrix.add_mulVec, SpExtras.E, Matrix.single_mulVec, mul_comm]

omit [CharP K 2] in
theorem spEquiv_elt_negativeSum (i j : Fin m) (hij : i < j) (c : K) :
    spEquiv (SpExtras.elt (.negativeSum i j hij) c) =
      lineElt spForm_isAlt (Pi.single (Sum.inr i) 1) (Pi.single (Sum.inr j) c) := by
  have hac : spForm m K (Pi.single (Sum.inr i) 1) (Pi.single (Sum.inr j) c) = 0 := by
    rw [spForm_apply_single_inr]
    simp
  apply Gsp.ext'
  intro x
  rw [spEquiv_app, lineElt_app spForm_isAlt hac, ← SpExtras.mat_apply, SpExtras.mat_elt,
    spForm_apply_single_inr, spForm_apply_single_inr]
  funext k
  rcases k with k | k
  · simp [Matrix.add_mulVec, SpExtras.E, Matrix.single_mulVec, mul_comm]
  · simp [Matrix.add_mulVec, SpExtras.E, Matrix.single_mulVec, Pi.single_apply, mul_comm,
      Function.update_apply]
    abel

omit [CharP K 2] in
theorem linearIndependent_single_pair {p q : Fin m ⊕ Fin m} (hpq : p ≠ q) {c : K} (hc : c ≠ 0) :
    LinearIndependent K ![(Pi.single p 1 : Fin m ⊕ Fin m → K), Pi.single q c] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have h1 := congrFun hst p
  have h2 := congrFun hst q
  simp only [Pi.add_apply, Pi.smul_apply, Pi.single_apply, hpq, hpq.symm, reduceIte,
    smul_eq_mul, mul_one, mul_zero, add_zero, zero_add, Pi.zero_apply] at h1 h2
  exact ⟨h1, (mul_eq_zero.mp h2).resolve_right hc⟩

theorem exists_lineElt_eq_spEquiv_elt (r : RootSubgroupIndex m)
    (hr : ∀ i, r ≠ .positiveLong i) (hr' : ∀ i, r ≠ .negativeLong i) {c : K} (hc : c ≠ 0) :
    ∃ a b : Fin m ⊕ Fin m → K, spForm m K a b = 0 ∧ LinearIndependent K ![a, b] ∧
      spEquiv (SpExtras.elt r c) = lineElt spForm_isAlt a b := by
  cases r with
  | positiveLong i => exact absurd rfl (hr i)
  | negativeLong i => exact absurd rfl (hr' i)
  | difference i j hij =>
    refine ⟨_, _, ?_, linearIndependent_single_pair (by simp) hc,
      spEquiv_elt_difference i j hij c⟩
    rw [spForm_apply_single_inr]
    simp [hij]
  | positiveSum i j hij =>
    refine ⟨_, _, ?_, linearIndependent_single_pair (by simp [hij.ne]) hc,
      spEquiv_elt_positiveSum i j hij c⟩
    rw [spForm_apply_single_inl]
    simp
  | negativeSum i j hij =>
    refine ⟨_, _, ?_, linearIndependent_single_pair (by simp [hij.ne]) hc,
      spEquiv_elt_negativeSum i j hij c⟩
    rw [spForm_apply_single_inr]
    simp

end CFSG.ClassicalGroups.Symplectic
