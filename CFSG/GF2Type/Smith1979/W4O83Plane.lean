module

public import CFSG.GF2Type.Smith1979.W4O83Defs
public import CFSG.RankThree.OrthogonalInvolutions.Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.W4O83.Omega83Pre

open Subgroup Module QuadraticMap CFSG.LargeExtraspecial CFSG.Open
open CFSG.RankThree.OrthogonalInvolutions (add_self_vec neg_vec_eq)
open CFSG.RankThree.Literature.FSmith (zmod2_cases)

variable {G : Type} [Group G] [Finite G] {S : Setting G} (C : Omega83Pre S)

theorem exists_decomp (v : S.Qt) :
    ∃ w : Fin 4 → S.Qt, (∀ i, w i ∈ C.plane i) ∧ ∑ i, w i = v := by
  have hv : v ∈ ⨆ i, C.plane i := by
    rw [C.iSup_plane]
    exact Submodule.mem_top
  refine Submodule.iSup_induction C.plane
    (motive := fun v => ∃ w : Fin 4 → S.Qt, (∀ i, w i ∈ C.plane i) ∧ ∑ i, w i = v) hv ?_ ?_ ?_
  · intro i x hx
    refine ⟨Pi.single i x, fun j => ?_, by simp⟩
    by_cases hj : j = i
    · subst hj
      simpa using hx
    · simp [hj]
  · exact ⟨0, fun _ => zero_mem _, by simp⟩
  · rintro x y ⟨wx, hwx, rfl⟩ ⟨wy, hwy, rfl⟩
    exact ⟨wx + wy, fun i => add_mem (hwx i) (hwy i), by simp [Finset.sum_add_distrib]⟩

@[expose] def prL (i : Fin 4) : S.Qt →ₗ[ZMod 2] S.Qt :=
  (C.th i).toLinearMap ∘ₗ (C.th i).toLinearMap + (C.th i).toLinearMap

theorem prL_apply (i : Fin 4) (v : S.Qt) : C.prL i v = C.th i (C.th i v) + C.th i v := rfl

theorem th_th_eq_add {i : Fin 4} {v : S.Qt} (hv : v ∈ C.plane i) :
    C.th i (C.th i v) = v + C.th i v := by
  have hw : C.th i (C.th i v) + C.th i v + v ∈ C.plane i :=
    add_mem (add_mem (C.th_mem_plane (C.th_mem_plane hv)) (C.th_mem_plane hv)) hv
  have hfix : C.th i (C.th i (C.th i v) + C.th i v + v) =
      C.th i (C.th i v) + C.th i v + v := by
    simp only [map_add, C.th_th_th]
    abel
  have h := C.eq_zero_of_th_eq hw hfix
  have h2 : C.th i (C.th i v) + (v + C.th i v) = 0 := by
    rw [← h]
    abel
  rw [eq_neg_of_add_eq_zero_left h2, neg_vec_eq (ZMod 2)]

theorem prL_of_mem_self {i : Fin 4} {v : S.Qt} (hv : v ∈ C.plane i) : C.prL i v = v := by
  rw [prL_apply, C.th_th_eq_add hv, add_assoc, add_self_vec (ZMod 2), add_zero]

theorem prL_of_mem_ne {i j : Fin 4} (hij : i ≠ j) {v : S.Qt} (hv : v ∈ C.plane j) :
    C.prL i v = 0 := by
  rw [prL_apply, C.th_eq_of_ne hij hv, C.th_eq_of_ne hij hv, add_self_vec (ZMod 2)]

theorem prL_decomp {w : Fin 4 → S.Qt} (hw : ∀ j, w j ∈ C.plane j) (i : Fin 4) :
    C.prL i (∑ j, w j) = w i := by
  rw [map_sum, Finset.sum_eq_single i]
  · exact C.prL_of_mem_self (hw i)
  · intro j _ hji
    exact C.prL_of_mem_ne hji.symm (hw j)
  · simp

theorem prL_mem_plane (i : Fin 4) (v : S.Qt) : C.prL i v ∈ C.plane i := by
  obtain ⟨w, hw, rfl⟩ := C.exists_decomp v
  rw [C.prL_decomp hw]
  exact hw i

theorem sum_prL (v : S.Qt) : ∑ i, C.prL i v = v := by
  obtain ⟨w, hw, rfl⟩ := C.exists_decomp v
  exact (Finset.sum_congr rfl fun i _ => C.prL_decomp hw i).trans rfl

theorem th_eq_iff (i : Fin 4) (v : S.Qt) : C.th i v = v ↔ C.prL i v = 0 := by
  constructor
  · intro h
    rw [prL_apply, h, h, add_self_vec (ZMod 2)]
  · intro h
    conv_lhs => rw [← C.sum_prL v]
    rw [map_sum]
    conv_rhs => rw [← C.sum_prL v]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hji : j = i
    · subst hji
      rw [h, map_zero]
    · exact C.th_eq_of_ne (Ne.symm hji) (C.prL_mem_plane j v)

theorem th_ne_iff (i : Fin 4) (v : S.Qt) : C.th i v ≠ v ↔ C.prL i v ≠ 0 :=
  not_congr (C.th_eq_iff i v)

theorem plane_eq_span_pair {i : Fin 4} {q : S.Qt} (hq : q ∈ C.plane i) (hq0 : q ≠ 0) :
    C.plane i = Submodule.span (ZMod 2) {q, C.th i q} := by
  have hth : C.th i q ∈ C.plane i := C.th_mem_plane hq
  have hne : C.th i q ≠ q := fun h => hq0 (C.eq_zero_of_th_eq hq h)
  have hth0 : C.th i q ≠ 0 := fun h => hq0 ((C.th i).injective (h.trans (map_zero _).symm))
  have hli : LinearIndependent (ZMod 2) ![q, C.th i q] := by
    rw [LinearIndependent.pair_iff' hq0]
    intro a ha
    rcases zmod2_cases a with rfl | rfl
    · exact hth0 (by simpa using ha.symm)
    · exact hne (by simpa using ha.symm)
  have hspan : Submodule.span (ZMod 2) {q, C.th i q} ≤ C.plane i := by
    rw [Submodule.span_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact hq
    · exact hth
  refine (Submodule.eq_of_le_of_finrank_eq hspan ?_).symm
  rw [C.finrank_plane i]
  have h2 := finrank_span_eq_card hli
  rw [Matrix.range_cons_cons_empty] at h2
  simpa using h2

theorem mem_orbit {i : Fin 4} {q : S.Qt} (hq : q ∈ C.plane i) (hq0 : q ≠ 0) {w : S.Qt}
    (hw : w ∈ C.plane i) : w = 0 ∨ w = q ∨ w = C.th i q ∨ w = C.th i (C.th i q) := by
  rw [C.plane_eq_span_pair hq hq0, Submodule.mem_span_pair] at hw
  obtain ⟨a, b, rfl⟩ := hw
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl
  · left
    simp
  · right
    right
    left
    simp
  · right
    left
    simp
  · right
    right
    right
    rw [C.th_th_eq_add hq]
    simp

theorem polar_th_self {i : Fin 4} {u : S.Qt} (hu : u ∈ C.plane i) (hu0 : u ≠ 0) :
    polar S.q u (C.th i u) = 1 := by
  have hth : C.th i u ∈ C.plane i := C.th_mem_plane hu
  have hne : C.th i u ≠ u := fun h => hu0 (C.eq_zero_of_th_eq hu h)
  have hsum : u + C.th i u ≠ 0 := by
    intro h
    apply hne
    rw [eq_neg_of_add_eq_zero_right h, neg_vec_eq (ZMod 2)]
  have h1 := C.q_eq_one i u hu hu0
  have h2 : S.q (C.th i u) = 1 := by rw [C.q_th, h1]
  have h3 := C.q_eq_one i (u + C.th i u) (add_mem hu hth) hsum
  simp only [polar]
  rw [h1, h2, h3]
  decide

theorem polar_sum_left (f : Fin 4 → S.Qt) (w : S.Qt) :
    polar S.q (∑ j, f j) w = ∑ j, polar S.q (f j) w := by
  rw [Fin.sum_univ_four, Fin.sum_univ_four]
  simp only [polar_add_left]

theorem polar_eq_polar_prL (i : Fin 4) (u : S.Qt) {w : S.Qt} (hw : w ∈ C.plane i) :
    polar S.q u w = polar S.q (C.prL i u) w := by
  conv_lhs => rw [← C.sum_prL u]
  rw [polar_sum_left, Finset.sum_eq_single i]
  · intro j _ hji
    exact C.polar_eq_zero j i hji _ (C.prL_mem_plane j u) _ hw
  · simp

theorem prL_eq_zero_of_polar {i : Fin 4} {u : S.Qt}
    (h : ∀ w ∈ C.plane i, polar S.q u w = 0) : C.prL i u = 0 := by
  by_contra hne
  have hmem := C.prL_mem_plane i u
  have h1 := C.polar_th_self hmem hne
  have h2 := C.polar_eq_polar_prL i u (C.th_mem_plane hmem)
  rw [h _ (C.th_mem_plane hmem), h1] at h2
  exact zero_ne_one h2

theorem eq_of_comm_th {i : Fin 4} (ℓ : S.Qt ≃ₗ[ZMod 2] S.Qt) (hℓ2 : ∀ v, ℓ (ℓ v) = v)
    (hcomm : ∀ v, ℓ (C.th i v) = C.th i (ℓ v)) {p : S.Qt} (hp : p ∈ C.plane i) : ℓ p = p := by
  have hpres : ∀ v ∈ C.plane i, ℓ v ∈ C.plane i := by
    intro v hv
    have h1 : ℓ v = C.prL i (ℓ v) := by
      conv_lhs => rw [← C.prL_of_mem_self hv]
      simp only [prL_apply, map_add, hcomm]
    rw [h1]
    exact C.prL_mem_plane i _
  by_contra hne
  have hqm : ℓ p + p ∈ C.plane i := add_mem (hpres p hp) hp
  have hq0 : ℓ p + p ≠ 0 := by
    intro h
    apply hne
    rw [eq_neg_of_add_eq_zero_left h, neg_vec_eq (ZMod 2)]
  have hℓq : ℓ (ℓ p + p) = ℓ p + p := by
    rw [map_add, hℓ2, add_comm]
  rcases C.mem_orbit hqm hq0 hp with h | h | h | h
  · exact hne (by rw [h, map_zero])
  · exact hne (by rw [h, hℓq])
  · exact hne (by rw [h, hcomm, hℓq])
  · exact hne (by rw [h, hcomm, hcomm, hℓq])

end CFSG.GF2Type.Smith1979.W4O83.Omega83Pre
