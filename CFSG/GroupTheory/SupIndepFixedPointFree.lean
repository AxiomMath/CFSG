module

public import Mathlib.Order.SupIndep
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Tactic.Abel

public section

namespace CFSG.GroupTheory

theorem eq_zero_of_mem_finset_sup_of_fixedPointFree {V : Type*} [AddCommGroup V] (g : V →+ V)
    {s : Finset (AddSubgroup V)} (hs : s.SupIndep id) (hinv : ∀ W ∈ s, ∀ v ∈ W, g v ∈ W)
    (hfix : ∀ W ∈ s, ∀ v ∈ W, g v = v → v = 0) {w : V} (hw : w ∈ s.sup id)
    (hgw : g w = w) : w = 0 := by
  classical
  induction s using Finset.induction_on generalizing w with
  | empty =>
      rw [Finset.sup_empty] at hw
      exact AddSubgroup.mem_bot.mp hw
  | insert a t ha ih =>
      rw [Finset.sup_insert] at hw
      obtain ⟨u, hu, v, hv, rfl⟩ := AddSubgroup.mem_sup.mp hw
      have hdis : Disjoint a (t.sup id) :=
        hs (Finset.subset_insert a t) (Finset.mem_insert_self a t) (by simpa using ha)
      have hts : t.SupIndep id := hs.subset (Finset.subset_insert a t)
      have hinh : ∀ W ∈ t, ∀ v ∈ W, g v ∈ W :=
        fun W hW => hinv W (Finset.mem_insert_of_mem hW)
      have hfixt : ∀ W ∈ t, ∀ v ∈ W, g v = v → v = 0 :=
        fun W hW => hfix W (Finset.mem_insert_of_mem hW)
      have hsupinv : ∀ v ∈ t.sup id, g v ∈ t.sup id :=
        Finset.sup_induction (f := id) (p := fun U => ∀ v ∈ U, g v ∈ U)
          (fun v hv => by rw [AddSubgroup.mem_bot] at hv; rw [hv, map_zero]; exact zero_mem _)
          (fun _A hA _B hB v hv => by
            obtain ⟨x, hx, y, hy, rfl⟩ := AddSubgroup.mem_sup.mp hv
            rw [map_add]
            exact add_mem (AddSubgroup.mem_sup_left (hA x hx))
              (AddSubgroup.mem_sup_right (hB y hy))) hinh
      have hdiff : g u - u = -(g v - v) := by
        have h := hgw
        rw [map_add] at h
        calc g u - u = g u + g v - g v - u := by abel
          _ = (u + v) - g v - u := by rw [h]
          _ = v - g v := by abel
          _ = -(g v - v) := by abel
      have hmem1 : g u - u ∈ a := a.sub_mem (hinv a (Finset.mem_insert_self a t) u hu) hu
      have hmem2 : -(g v - v) ∈ t.sup id :=
        (t.sup id).neg_mem ((t.sup id).sub_mem (hsupinv v hv) hv)
      have hinf : g u - u ∈ a ⊓ t.sup id := ⟨hmem1, by rw [hdiff]; exact hmem2⟩
      have hbot : g u - u ∈ (⊥ : AddSubgroup V) := by
        rwa [← disjoint_iff.mp hdis]
      have hgu : g u = u := sub_eq_zero.mp (AddSubgroup.mem_bot.mp hbot)
      have hgv : g v = v := by
        have h1 : -(g v - v) = 0 := by rw [← hdiff, hgu, sub_self]
        exact sub_eq_zero.mp (neg_eq_zero.mp h1)
      have hu0 : u = 0 := hfix a (Finset.mem_insert_self a t) u hu hgu
      have hv0 : v = 0 := ih hts hinh hfixt hv hgv
      rw [hu0, hv0, add_zero]

end CFSG.GroupTheory
