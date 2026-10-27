module

public import Mathlib.GroupTheory.Index

public section

namespace CFSG.GroupTheory

theorem centralizer_singleton_map_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) (x : G) :
    (Subgroup.centralizer ({x} : Set G)).map e.toMonoidHom =
      Subgroup.centralizer ({e x} : Set H) := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hz' : z * x = x * z := (Subgroup.mem_centralizer_singleton_iff).mp hz
    exact (Subgroup.mem_centralizer_singleton_iff).mpr (by
      change e z * e x = e x * e z
      rw [← map_mul, ← map_mul, hz'])
  · intro hy
    refine ⟨e.symm y, ?_, by simp⟩
    have hy' : y * e x = e x * y := (Subgroup.mem_centralizer_singleton_iff).mp hy
    exact (Subgroup.mem_centralizer_singleton_iff).mpr (by
      have := congrArg e.symm hy'
      simpa only [map_mul, MulEquiv.symm_apply_apply] using this)

theorem card_centralizer_singleton_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) (x : G) :
    Nat.card (Subgroup.centralizer ({x} : Set G)) =
      Nat.card (Subgroup.centralizer ({e x} : Set H)) := by
  rw [← centralizer_singleton_map_mulEquiv e x, Subgroup.card_map_of_injective e.injective]

theorem ncard_orbit_conjAct_mul_card_centralizer (G : Type*) [Group G] [Finite G] (x : G) :
    (MulAction.orbit (ConjAct G) x).ncard *
      Nat.card (Subgroup.centralizer ({x} : Set G)) = Nat.card G := by
  have h := Subgroup.index_mul_card (H := MulAction.stabilizer (ConjAct G) x)
  rw [MulAction.index_stabilizer, ConjAct.stabilizer_eq_centralizer] at h
  have h1 : Nat.card (Subgroup.centralizer ({ConjAct.toConjAct x} : Set (ConjAct G))) =
      Nat.card (Subgroup.centralizer ({x} : Set G)) := by
    rw [card_centralizer_singleton_mulEquiv (G := ConjAct G) (H := G) ConjAct.ofConjAct
      (ConjAct.toConjAct x)]
    simp only [ConjAct.ofConjAct_toConjAct]
  rw [h1, ← Nat.card_congr ConjAct.toConjAct.toEquiv] at h
  exact h

end CFSG.GroupTheory
