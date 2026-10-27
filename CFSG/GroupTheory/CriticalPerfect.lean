module

public import CFSG.GroupTheory.PerfectActionCritical

public section

namespace CFSG.GroupTheory

open Subgroup
open scoped commutatorElement

variable {H : Type*} [Group H] [Finite H] {q : ℕ} [Fact q.Prime]

private theorem le_centralizer_of_isCyclic_target {P E : Subgroup H} [E.Normal]
    (hP : ⁅P, P⁆ = P) (hcyc : IsCyclic ↥E) : P ≤ Subgroup.centralizer (E : Set H) := by
  have hmap : P.map (MulAut.conjNormal (H := E)) = ⊥ :=
    map_eq_bot_of_isPerfect_of_isCyclicTarget (MulAut.conjNormal (H := E)) hP
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have h1 : MulAut.conjNormal (H := E) x = 1 := by
    have hmem := Subgroup.mem_map_of_mem (MulAut.conjNormal (H := E)) hx
    rw [hmap] at hmem
    exact Subgroup.mem_bot.mp hmem
  have h2 := congrArg (fun f : MulAut ↥E => (f ⟨y, hy⟩ : ↥E)) h1
  simp only [MulAut.one_apply] at h2
  have h3 : x * y * x⁻¹ = y := by
    simpa [MulAut.conjNormal_apply] using congrArg Subtype.val h2
  have h4 : x * y = y * x := by
    calc x * y = (x * y * x⁻¹) * x := by group
      _ = y * x := by rw [h3]
  exact h4.symm

private theorem le_centralizer_of_le_centralizer_map {P Q : Subgroup H} [Q.Normal]
    {D : Subgroup ↥Q} (hP : ⁅P, P⁆ = P)
    (hfix : IsPGroup q (fixingSubgroup (MulAut ↥Q) (D : Set ↥Q)))
    (hcent : P ≤ Subgroup.centralizer (D.map Q.subtype : Set H)) :
    P ≤ Subgroup.centralizer (Q : Set H) := by
  have hmap : P.map (MulAut.conjNormal (H := Q)) = ⊥ := by
    refine map_eq_bot_of_isPerfect_of_le_fixingSubgroup (MulAut.conjNormal (H := Q)) D hfix hP ?_
    rintro _ ⟨x, hx, rfl⟩
    rw [mem_fixingSubgroup_iff]
    intro d hd
    apply Subtype.ext
    have hcomm := (Subgroup.mem_centralizer_iff.mp (hcent hx)) (d : H)
      (Subgroup.mem_map_of_mem Q.subtype hd)
    change x * (d : H) * x⁻¹ = (d : H)
    rw [← hcomm]
    group
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have h1 : MulAut.conjNormal (H := Q) x = 1 := by
    have hmem := Subgroup.mem_map_of_mem (MulAut.conjNormal (H := Q)) hx
    rw [hmap] at hmem
    exact Subgroup.mem_bot.mp hmem
  have h2 := congrArg (fun f : MulAut ↥Q => (f ⟨y, hy⟩ : ↥Q)) h1
  simp only [MulAut.one_apply] at h2
  have h3 : x * y * x⁻¹ = y := by
    simpa [MulAut.conjNormal_apply] using congrArg Subtype.val h2
  have h4 : x * y = y * x := by
    calc x * y = (x * y * x⁻¹) * x := by group
      _ = y * x := by rw [h3]
  exact h4.symm

theorem critical_map_noncyclic_and_commutator_ne_bot {P Q : Subgroup H} [Q.Normal]
    {D : Subgroup ↥Q} [(D.map Q.subtype).Normal] (hP : ⁅P, P⁆ = P)
    (hfix : IsPGroup q (fixingSubgroup (MulAut ↥Q) (D : Set ↥Q)))
    (hPQ : ⁅P, Q⁆ ≠ ⊥) :
    ¬ IsCyclic ↥(D.map Q.subtype) ∧ ⁅P, D.map Q.subtype⁆ ≠ ⊥ := by
  constructor
  · intro hcyc
    exact hPQ (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (le_centralizer_of_le_centralizer_map hP hfix (le_centralizer_of_isCyclic_target hP hcyc)))
  · intro hbot
    exact hPQ (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (le_centralizer_of_le_centralizer_map hP hfix
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot)))

end CFSG.GroupTheory
