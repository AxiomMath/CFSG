module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG.GroupTheory

open Equiv Equiv.Perm

theorem exists_isPGroup_three_not_isCyclic_alternatingGroup {n : ℕ} (hn : 6 ≤ n) :
    ∃ P : Subgroup (alternatingGroup (Fin n)), IsPGroup 3 P ∧ ¬ IsCyclic P := by
  classical
  let i0 : Fin n := ⟨0, by omega⟩
  let i1 : Fin n := ⟨1, by omega⟩
  let i2 : Fin n := ⟨2, by omega⟩
  let i3 : Fin n := ⟨3, by omega⟩
  let i4 : Fin n := ⟨4, by omega⟩
  let i5 : Fin n := ⟨5, by omega⟩
  have h01 : i0 ≠ i1 := by simp [i0, i1]
  have h02 : i0 ≠ i2 := by simp [i0, i2]
  have h12 : i1 ≠ i2 := by simp [i1, i2]
  have h34 : i3 ≠ i4 := by simp [i3, i4]
  have h35 : i3 ≠ i5 := by simp [i3, i5]
  have h45 : i4 ≠ i5 := by simp [i4, i5]
  let σ : Equiv.Perm (Fin n) := Equiv.swap i0 i1 * Equiv.swap i0 i2
  let τ : Equiv.Perm (Fin n) := Equiv.swap i3 i4 * Equiv.swap i3 i5
  have hσcyc : σ.IsThreeCycle := isThreeCycle_swap_mul_swap_same h01 h02 h12
  have hτcyc : τ.IsThreeCycle := isThreeCycle_swap_mul_swap_same h34 h35 h45
  have hσ3 : σ ^ 3 = 1 := by rw [← hσcyc.orderOf]; exact pow_orderOf_eq_one σ
  have hτ3 : τ ^ 3 = 1 := by rw [← hτcyc.orderOf]; exact pow_orderOf_eq_one τ
  let σA : alternatingGroup (Fin n) := ⟨σ, hσcyc.mem_alternatingGroup⟩
  let τA : alternatingGroup (Fin n) := ⟨τ, hτcyc.mem_alternatingGroup⟩
  have hσA3 : σA ^ 3 = 1 := by
    apply Subtype.ext
    simp [σA, hσ3]
  have hτA3 : τA ^ 3 = 1 := by
    apply Subtype.ext
    simp [τA, hτ3]
  have hdisj : σ.Disjoint τ := by
    intro x
    by_cases hx : x = i3 ∨ x = i4 ∨ x = i5
    · left
      rcases hx with rfl | rfl | rfl <;>
        simp [σ, Equiv.swap_apply_def, i0, i1, i2, i3, i4, i5]
    · right
      push Not at hx
      obtain ⟨hx3, hx4, hx5⟩ := hx
      simp [τ, Equiv.swap_apply_of_ne_of_ne hx3 hx5,
        Equiv.swap_apply_of_ne_of_ne hx3 hx4]
  let P : Subgroup (alternatingGroup (Fin n)) := Subgroup.closure {σA, τA}
  have hσP : σA ∈ P := Subgroup.subset_closure (by simp)
  have hτP : τA ∈ P := Subgroup.subset_closure (by simp)
  have hcomm : Commute σA τA := by
    show σA * τA = τA * σA
    apply Subtype.ext
    exact hdisj.commute
  have hCσ : ∀ x ∈ P, Commute x σA := by
    intro x hx
    refine Subgroup.closure_induction (p := fun x _ => Commute x σA) ?_ ?_ ?_ ?_ hx
    · intro z hz
      rcases (by simpa using hz) with rfl | rfl
      · exact Commute.refl σA
      · exact hcomm.symm
    · exact Commute.one_left σA
    · intro a b _ _ iha ihb
      exact iha.mul_left ihb
    · intro a _ iha
      exact iha.inv_left
  have hCτ : ∀ x ∈ P, Commute x τA := by
    intro x hx
    refine Subgroup.closure_induction (p := fun x _ => Commute x τA) ?_ ?_ ?_ ?_ hx
    · intro z hz
      rcases (by simpa using hz) with rfl | rfl
      · exact hcomm
      · exact Commute.refl τA
    · exact Commute.one_left τA
    · intro a b _ _ iha ihb
      exact iha.mul_left ihb
    · intro a _ iha
      exact iha.inv_left
  have hPab : ∀ x ∈ P, ∀ y ∈ P, Commute x y := by
    intro x hx y hy
    refine Subgroup.closure_induction (p := fun y _ => Commute x y) ?_ ?_ ?_ ?_ hy
    · intro z hz
      rcases (by simpa using hz) with rfl | rfl
      · exact hCσ x hx
      · exact hCτ x hx
    · exact Commute.one_right x
    · intro a b _ _ iha ihb
      exact iha.mul_right ihb
    · intro a _ iha
      exact iha.inv_right
  have hexp : ∀ x ∈ P, x ^ 3 = 1 := by
    intro x hx
    refine Subgroup.closure_induction (p := fun x _ => x ^ 3 = 1) ?_ ?_ ?_ ?_ hx
    · intro z hz
      rcases (by simpa using hz) with rfl | rfl
      · exact hσA3
      · exact hτA3
    · exact one_pow 3
    · intro a b ha hb iha ihb
      rw [(hPab a ha b hb).mul_pow 3, iha, ihb, mul_one]
    · intro a _ iha
      rw [inv_pow, iha, inv_one]
  have hσi0 : (σA : Equiv.Perm (Fin n)) i0 = i2 := by
    simp [σA, σ, Equiv.swap_apply_def, i0, i1, i2]
  have hσ2i0 : ((σA ^ 2 : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) i0 = i1 := by
    have h : ((σA ^ 2 : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) =
        (σA : Equiv.Perm (Fin n)) ^ 2 := rfl
    rw [h, pow_two]
    simp [σA, σ, Equiv.swap_apply_def, i0, i1, i2]
  have hσi3 : (σA : Equiv.Perm (Fin n)) i3 = i3 := by
    simp [σA, σ, Equiv.swap_apply_def, i0, i1, i2, i3]
  have hσ2i3 : ((σA ^ 2 : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) i3 = i3 := by
    have h : ((σA ^ 2 : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) =
        (σA : Equiv.Perm (Fin n)) ^ 2 := rfl
    rw [h, pow_two]
    simp [σA, σ, Equiv.swap_apply_def, i0, i1, i2, i3]
  have hτi3 : (τA : Equiv.Perm (Fin n)) i3 = i5 := by
    simp [τA, τ, Equiv.swap_apply_def, i3, i4, i5]
  refine ⟨P, ?_, ?_⟩
  · intro g
    exact ⟨1, by simpa using (Subtype.ext (hexp (g : alternatingGroup (Fin n)) g.2) :
      (g : P) ^ 3 = 1)⟩
  · intro hcyc
    have hle := IsCyclic.card_pow_eq_one_le (α := P) (n := 3) (by norm_num)
    have hall : Finset.univ.filter (fun x : P => x ^ 3 = 1) = Finset.univ := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      exact Subtype.ext (hexp x x.2)
    rw [hall, Finset.card_univ] at hle
    let e0 : P := 1
    let e1 : P := ⟨σA, hσP⟩
    let e2 : P := ⟨σA ^ 2, Subgroup.pow_mem P hσP 2⟩
    let e3 : P := ⟨τA, hτP⟩
    let f : P → Fin n := fun x =>
      (((x : P) : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) i0
    let g : P → Fin n := fun x =>
      (((x : P) : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) i3
    have hf0 : f e0 = i0 := rfl
    have hf1 : f e1 = i2 := hσi0
    have hf2 : f e2 = i1 := hσ2i0
    have hf3 : f e3 = i0 := by
      simp [f, e3, τA, τ, Equiv.swap_apply_def, i0, i3, i4, i5]
    have hg0 : g e0 = i3 := rfl
    have hg1 : g e1 = i3 := hσi3
    have hg2 : g e2 = i3 := hσ2i3
    have hg3 : g e3 = i5 := hτi3
    have h01 : e0 ≠ e1 := by
      intro h
      have hv := congrArg f h
      rw [hf0, hf1] at hv
      exact absurd hv (by simp [i0, i2])
    have h02 : e0 ≠ e2 := by
      intro h
      have hv := congrArg f h
      rw [hf0, hf2] at hv
      exact absurd hv (by simp [i0, i1])
    have h03 : e0 ≠ e3 := by
      intro h
      have hv := congrArg g h
      rw [hg0, hg3] at hv
      exact absurd hv (by simp [i3, i5])
    have h12 : e1 ≠ e2 := by
      intro h
      have hv := congrArg f h
      rw [hf1, hf2] at hv
      exact absurd hv (by simp [i1, i2])
    have h13 : e1 ≠ e3 := by
      intro h
      have hv := congrArg g h
      rw [hg1, hg3] at hv
      exact absurd hv (by simp [i3, i5])
    have h23 : e2 ≠ e3 := by
      intro h
      have hv := congrArg g h
      rw [hg2, hg3] at hv
      exact absurd hv (by simp [i3, i5])
    have hcard4 : ({e0, e1, e2, e3} : Finset P).card = 4 := by
      rw [Finset.card_eq_four]
      exact ⟨e0, e1, e2, e3, h01, h02, h03, h12, h13, h23, rfl⟩
    have hle4 : 4 ≤ Fintype.card P := by
      rw [← hcard4]
      exact Finset.card_le_univ _
    omega

theorem exists_isPGroup_three_not_isCyclic_of_mulEquiv_alternatingGroup {X : Type*} [Group X]
    {n : ℕ} (hn : 6 ≤ n) (e : X ≃* alternatingGroup (Fin n)) :
    ∃ P : Subgroup X, IsPGroup 3 P ∧ ¬ IsCyclic P := by
  obtain ⟨P, hP, hPnc⟩ := exists_isPGroup_three_not_isCyclic_alternatingGroup hn
  refine ⟨P.map e.symm.toMonoidHom, IsPGroup.map hP e.symm.toMonoidHom, ?_⟩
  intro hcyc
  haveI : IsCyclic ↥(P.map e.symm.toMonoidHom) := hcyc
  exact hPnc (isCyclic_of_injective
    (Subgroup.equivMapOfInjective P e.symm.toMonoidHom e.symm.injective).toMonoidHom
    (Subgroup.equivMapOfInjective P e.symm.toMonoidHom e.symm.injective).injective)

theorem false_of_isSimpleGroup_of_mulEquiv_alternatingGroup_of_le_four
    {Y : Type*} [Group Y] [Finite Y] (hY : IsSimpleGroup Y)
    (hna : ∃ a b : Y, a * b ≠ b * a) {m : ℕ} (hm : m ≤ 4)
    (e : Y ≃* alternatingGroup (Fin m)) : False := by
  have hperm : Group.IsSolvable (Equiv.Perm (Fin m)) :=
    Equiv.Perm.isSolvable (α := Fin m) (by simpa using hm)
  haveI : Group.IsSolvable (alternatingGroup (Fin m)) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (alternatingGroup (Fin m)).subtype) (Subgroup.subtype_injective _)
  have hsol : Group.IsSolvable Y :=
    Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  obtain ⟨a, b, hab⟩ := hna
  exact hab ((IsSimpleGroup.comm_iff_isSolvable (G := Y)).mpr hsol a b)

end CFSG.GroupTheory

end
