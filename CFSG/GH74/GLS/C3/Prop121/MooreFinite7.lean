module

public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.Data.List.FinRange
public meta import Mathlib.Algebra.Group.End
public meta import Mathlib.GroupTheory.Perm.Sign
public meta import Mathlib.GroupTheory.Perm.Basic
public meta import Mathlib.GroupTheory.Perm.Fin
public meta import Mathlib.Logic.Equiv.Fin.Basic
public meta import Mathlib.Logic.Equiv.Option
public meta import Mathlib.Data.List.FinRange
public import CFSG.GH74.GLS.C3.Prop121.MooreFinite7Inputs
public meta import CFSG.GH74.GLS.C3.Prop121.MooreFinite7Inputs
public import Certificates.Certificate5094

public section

namespace CFSG.GH74.GLS.C3.Prop121

open Equiv Perm

theorem mem_allPerms : ∀ (m : ℕ) (s : Perm (Fin m)), s ∈ allPerms m
  | 0, s => by simp [allPerms, Subsingleton.elim s 1]
  | m + 1, s => by
      unfold allPerms
      simp only [List.mem_flatMap, List.mem_finRange, true_and, List.mem_map]
      obtain ⟨p, e⟩ := Equiv.Perm.decomposeFin s
      refine ⟨(Equiv.Perm.decomposeFin s).1, (Equiv.Perm.decomposeFin s).2,
        mem_allPerms m _, ?_⟩
      exact Equiv.Perm.decomposeFin.symm_apply_apply s

theorem mem_evenL7 {s : Perm (Fin 8)} :
    s ∈ evenL7 ↔ s * s = 1 ∧ sign s = 1 ∧ s * cEnd7 * s⁻¹ = cEnd7⁻¹ := by
  simp [evenL7, mem_allPerms]

theorem mem_a4L7 {s : Perm (Fin 8)} :
    s ∈ a4L7 ↔ s * s = 1 ∧ sign s = 1 ∧ s ≠ 1 ∧ (cEnd7 * s) ^ 3 = 1 := by
  simp [a4L7, mem_allPerms]

theorem mem_oddL7 {s : Perm (Fin 8)} :
    s ∈ oddL7 ↔ s * s = 1 ∧ sign s = -1 ∧ s * cEnd7 * s⁻¹ = cEnd7⁻¹ := by
  simp [oddL7, mem_allPerms]

@[expose] def searchC7 (E2 : List (Perm (Fin 8))) (s1 s2 s3 s4 : Perm (Fin 8)) : Prop :=
  ∀ s5 ∈ E2, (s4 * s5) ^ 3 = 1 → (s2 * s5) ^ 2 = 1 → (s3 * s5) ^ 2 = 1 → (s1 * s2) ^ 3 = 1

@[expose] def searchB7 (E1 E2 : List (Perm (Fin 8))) (s1 : Perm (Fin 8)) : Prop :=
  ∀ s2 ∈ E1, ∀ s3 ∈ E2, (s2 * s3) ^ 3 = 1 → s2 ≠ s3 →
    ∀ s4 ∈ E2, (s3 * s4) ^ 3 = 1 → (s2 * s4) ^ 2 = 1 → s2 ≠ s4 → searchC7 E2 s1 s2 s3 s4

@[expose] def searchAll7 (A O E : List (Perm (Fin 8))) : Prop :=
  ∀ s1 ∈ A, ∀ sg ∈ O, sg * s1 = s1 * sg →
    searchB7 (E.filter fun s => sg * s = s * sg)
      ((E.filter fun s => sg * s = s * sg).filter fun s => s * s1 = s1 * s) s1

theorem okC7_sound {E2 : List (Perm (Fin 8))} {s1 s2 s3 s4 : Perm (Fin 8)}
    (h : okC7 E2 s1 s2 s3 s4 = true) : searchC7 E2 s1 s2 s3 s4 := by
  intro s5 hs5 h1 h2 h3
  simpa [h1, h2, h3] using List.all_eq_true.1 h s5 hs5

theorem okB7_sound {E1 E2 : List (Perm (Fin 8))} {s1 : Perm (Fin 8)}
    (h : okB7 E1 E2 s1 = true) : searchB7 E1 E2 s1 := by
  intro s2 hs2 s3 hs3 h1 h2 s4 hs4 h3 h4 h5
  have h6 := List.all_eq_true.1 (List.all_eq_true.1 h s2 hs2) s3 hs3
  simp only [h1, h2, ne_eq, not_false_eq_true, ite_true, List.all_eq_true] at h6
  have h7 := h6 s4 hs4
  simp only [h3, h4, h5, not_false_eq_true, ite_true] at h7
  exact okC7_sound h7

theorem okAll7_sound {A O E : List (Perm (Fin 8))} (h : okAll7 A O E = true) : searchAll7 A O E := by
  intro s1 hs1 sg hsg hc
  have h1 := List.all_eq_true.1 (List.all_eq_true.1 h s1 hs1) sg hsg
  simp only [hc, ite_true] at h1
  exact okB7_sound h1

theorem okAll7_true : okAll7 a4L7 oddL7 evenL7 = true :=
  Certificates.certificate5094

theorem searchAll7_true :
    searchAll7 a4L7 oddL7 evenL7 := okAll7_sound okAll7_true

theorem moore_finite_seven
    (c : Perm (Fin 8)) (hc : c = cEnd7) (s1 sg s2 s3 s4 s5 : Perm (Fin 8))
    (h1 : s1 * s1 = 1 ∧ sign s1 = 1 ∧ s1 ≠ 1 ∧ (c * s1) ^ 3 = 1)
    (hs : sg * sg = 1 ∧ sign sg = -1 ∧ sg * c * sg⁻¹ = c⁻¹ ∧ sg * s1 = s1 * sg)
    (h2 : s2 * s2 = 1 ∧ sign s2 = 1 ∧ s2 * c * s2⁻¹ = c⁻¹ ∧ sg * s2 = s2 * sg)
    (h3 : s3 * s3 = 1 ∧ sign s3 = 1 ∧ s3 * c * s3⁻¹ = c⁻¹ ∧ sg * s3 = s3 * sg ∧
      s3 * s1 = s1 * s3 ∧ (s2 * s3) ^ 3 = 1 ∧ s2 ≠ s3)
    (h4 : s4 * s4 = 1 ∧ sign s4 = 1 ∧ s4 * c * s4⁻¹ = c⁻¹ ∧ sg * s4 = s4 * sg ∧
      s4 * s1 = s1 * s4 ∧ (s3 * s4) ^ 3 = 1 ∧ (s2 * s4) ^ 2 = 1 ∧ s2 ≠ s4)
    (h5 : s5 * s5 = 1 ∧ sign s5 = 1 ∧ s5 * c * s5⁻¹ = c⁻¹ ∧ sg * s5 = s5 * sg ∧
      s5 * s1 = s1 * s5 ∧ (s4 * s5) ^ 3 = 1 ∧ (s2 * s5) ^ 2 = 1 ∧ (s3 * s5) ^ 2 = 1) :
    (s1 * s2) ^ 3 = 1 := by
  subst hc
  have e2 : s2 ∈ evenL7.filter fun s => sg * s = s * sg :=
    List.mem_filter.2 ⟨mem_evenL7.2 ⟨h2.1, h2.2.1, h2.2.2.1⟩, by simpa using h2.2.2.2⟩
  have e3 : s3 ∈ (evenL7.filter fun s => sg * s = s * sg).filter fun s => s * s1 = s1 * s :=
    List.mem_filter.2 ⟨List.mem_filter.2 ⟨mem_evenL7.2 ⟨h3.1, h3.2.1, h3.2.2.1⟩,
      by simpa using h3.2.2.2.1⟩, by simpa using h3.2.2.2.2.1⟩
  have e4 : s4 ∈ (evenL7.filter fun s => sg * s = s * sg).filter fun s => s * s1 = s1 * s :=
    List.mem_filter.2 ⟨List.mem_filter.2 ⟨mem_evenL7.2 ⟨h4.1, h4.2.1, h4.2.2.1⟩,
      by simpa using h4.2.2.2.1⟩, by simpa using h4.2.2.2.2.1⟩
  have e5 : s5 ∈ (evenL7.filter fun s => sg * s = s * sg).filter fun s => s * s1 = s1 * s :=
    List.mem_filter.2 ⟨List.mem_filter.2 ⟨mem_evenL7.2 ⟨h5.1, h5.2.1, h5.2.2.1⟩,
      by simpa using h5.2.2.2.1⟩, by simpa using h5.2.2.2.2.1⟩
  exact searchAll7_true s1 (mem_a4L7.2 h1) sg (mem_oddL7.2 ⟨hs.1, hs.2.1, hs.2.2.1⟩) hs.2.2.2
    s2 e2 s3 e3 h3.2.2.2.2.2.1 h3.2.2.2.2.2.2 s4 e4 h4.2.2.2.2.2.1 h4.2.2.2.2.2.2.1
    h4.2.2.2.2.2.2.2 s5 e5 h5.2.2.2.2.2.1 h5.2.2.2.2.2.2.1 h5.2.2.2.2.2.2.2

end CFSG.GH74.GLS.C3.Prop121
