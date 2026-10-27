module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSixE32Abel

public section

namespace CFSG.ComponentClassification.SolMax.Sig36.E32

open Subgroup

variable {X : Type} [Group X]

namespace FinalAux

private def Conj (g : Fin 5 → X) (ν : X) (u z : Fin 5 → ZMod 2) : Prop :=
  ν * mono g u * ν⁻¹ = mono g z

section Calculus

variable {g : Fin 5 → X}

private theorem Conj.comp {ν μ : X} {u z r : Fin 5 → ZMod 2} (h₁ : Conj g ν u z)
    (h₂ : Conj g μ z r) : Conj g (μ * ν) u r := by
  unfold Conj at *
  rw [← h₂, ← h₁]
  group

private theorem Conj.inv {ν : X} {u z : Fin 5 → ZMod 2} (h : Conj g ν u z) :
    Conj g ν⁻¹ z u := by
  unfold Conj at *
  rw [← h]
  group

private theorem Conj.zero (hg : IsE5 g) (ν : X) : Conj g ν 0 0 := by
  unfold Conj
  rw [hg.mono_zero]
  group

private theorem Conj.add (hg : IsE5 g) {ν : X} {p p' q q' : Fin 5 → ZMod 2}
    (hp : Conj g ν p p') (hq : Conj g ν q q') : Conj g ν (p + q) (p' + q') := by
  unfold Conj at *
  rw [hg.mono_add, hg.mono_add, ← hp, ← hq]
  group

private theorem Conj.smul (hg : IsE5 g) {ν : X} {p q : Fin 5 → ZMod 2} (a : ZMod 2)
    (h : Conj g ν p q) : Conj g ν (a • p) (a • q) := by
  obtain rfl | rfl : a = 0 ∨ a = 1 := by revert a; decide
  · simpa using Conj.zero hg ν
  · simpa using h

private theorem Conj.span (hg : IsE5 g) {ν : X} {P Q : Fin 5 → Fin 5 → ZMod 2}
    (h : ∀ j, Conj g ν (P j) (Q j)) {u z : Fin 5 → ZMod 2}
    (hw : ∃ w : Fin 5 → ZMod 2, ∑ j, w j • P j = u ∧ ∑ j, w j • Q j = z) :
    Conj g ν u z := by
  obtain ⟨w, rfl, rfl⟩ := hw
  rw [Fin.sum_univ_five, Fin.sum_univ_five]
  exact Conj.add hg (Conj.add hg (Conj.add hg (Conj.add hg (Conj.smul hg (w 0) (h 0))
    (Conj.smul hg (w 1) (h 1))) (Conj.smul hg (w 2) (h 2))) (Conj.smul hg (w 3) (h 3)))
    (Conj.smul hg (w 4) (h 4))

end Calculus

private def Pid : Fin 5 → Fin 5 → ZMod 2 :=
  ![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]

private def Mw (a b : ZMod 2) : Fin 5 → Fin 5 → ZMod 2 :=
  ![![1, 1, 0, 0, 0], ![1, 0, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![a, b, 0, 0, 1]]

private def Pa : Fin 5 → Fin 5 → ZMod 2 :=
  ![![0, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![1, 0, 1, 1, 0], ![1, 0, 0, 0, 1]]

private def Qa : Fin 5 → Fin 5 → ZMod 2 :=
  ![![0, 1, 0, 0, 0], ![1, 0, 0, 1, 0], ![1, 0, 1, 1, 0], ![1, 0, 0, 0, 1], ![1, 0, 1, 0, 0]]

section Translate

variable {g : Fin 5 → X}

private theorem val_one : (1 : ZMod 2).val = 1 := by decide

private theorem m_e0 : mono g ![1, 0, 0, 0, 0] = g 0 := by simp [mono, val_one]
private theorem m_e1 : mono g ![0, 1, 0, 0, 0] = g 1 := by simp [mono, val_one]
private theorem m_e2 : mono g ![0, 0, 1, 0, 0] = g 2 := by simp [mono, val_one]
private theorem m_e3 : mono g ![0, 0, 0, 1, 0] = g 3 := by simp [mono, val_one]
private theorem m_e4 : mono g ![0, 0, 0, 0, 1] = g 4 := by simp [mono, val_one]
private theorem m_st : mono g ![1, 1, 0, 0, 0] = g 0 * g 1 := by simp [mono, val_one]
private theorem m_a0 : mono g ![1, 0, 1, 0, 0] = g 0 * g 2 := by simp [mono, val_one]
private theorem m_a1 : mono g ![1, 0, 0, 1, 0] = g 0 * g 3 := by simp [mono, val_one]
private theorem m_a2 : mono g ![1, 0, 1, 1, 0] = g 0 * (g 2 * g 3) := by
  simp [mono, val_one, mul_assoc]
private theorem m_a3 : mono g ![1, 0, 0, 0, 1] = g 0 * g 4 := by simp [mono, val_one]
private theorem m_b : mono g ![1, 0, 1, 1, 1] = g 0 * g 2 * g 3 * g 4 := by
  simp [mono, val_one]
private theorem m_d : mono g ![0, 0, 1, 1, 1] = g 2 * g 3 * g 4 := by simp [mono, val_one]

private theorem m_b' (hg : IsE5 g) :
    mono g ![1, 1, 1, 1, 1] = g 0 * g 2 * g 3 * g 4 * g 1 := by
  rw [← m_b, ← m_e1 (g := g), ← hg.mono_add]
  congr 1
  decide

private theorem m_x (hg : IsE5 g) (a b : ZMod 2) :
    g 4 * mono g ![a, b, 0, 0, 0] = mono g ![a, b, 0, 0, 1] := by
  rw [← m_e4 (g := g), ← hg.mono_add]
  congr 1
  ext i
  fin_cases i <;> simp

end Translate

end FinalAux

open FinalAux

theorem final_false {g : Fin 5 → X} (hg : IsE5 g) (ω c : X)
    (hω : ω * g 1 * ω⁻¹ = g 0 ∧ ω * g 0 * ω⁻¹ = g 0 * g 1 ∧ ω * g 2 * ω⁻¹ = g 2 ∧
      ω * g 3 * ω⁻¹ = g 3)
    {v : Fin 5 → ZMod 2} (hv2 : v 2 = 0) (hv3 : v 3 = 0) (hv4 : v 4 = 0)
    (hωx : ω * g 4 * ω⁻¹ = g 4 * mono g v)
    (hc : c * g 1 * c⁻¹ = g 1 ∧ c * (g 0 * g 2) * c⁻¹ = g 0 * g 3 ∧
      c * (g 0 * g 3) * c⁻¹ = g 0 * (g 2 * g 3) ∧
      c * (g 0 * (g 2 * g 3)) * c⁻¹ = g 0 * g 4 ∧ c * (g 0 * g 4) * c⁻¹ = g 0 * g 2)
    (hS₁ : IsConj (g 1) (g 0 * g 2 * g 3 * g 4 * g 1)) (hS₂ : IsConj (g 1) (g 0 * g 2 * g 3 * g 4))
    (hP2 : ¬ IsConj (g 1) (g 2 * g 3 * g 4))
    (hP1 : ∀ y : X, y * g 1 * y⁻¹ = g 1 → y * (g 0 * g 3) * y⁻¹ ≠ g 0 * g 2 * g 3 * g 4) :
    False := by
  obtain ⟨a, b, rfl⟩ : ∃ a b : ZMod 2, v = ![a, b, 0, 0, 0] :=
    ⟨v 0, v 1, by ext i; fin_cases i <;> simp [hv2, hv3, hv4]⟩
  have hS₁' : IsConj (mono g ![0, 1, 0, 0, 0]) (mono g ![1, 1, 1, 1, 1]) := by
    rw [m_e1, m_b' hg]; exact hS₁
  have hS₂' : IsConj (mono g ![0, 1, 0, 0, 0]) (mono g ![1, 0, 1, 1, 1]) := by
    rw [m_e1, m_b]; exact hS₂
  have hP2' : ¬ IsConj (mono g ![0, 1, 0, 0, 0]) (mono g ![0, 0, 1, 1, 1]) := by
    rw [m_e1, m_d]; exact hP2
  have rΩ : ∀ j, Conj g ω (Pid j) (Mw a b j) := by
    have r0 : Conj g ω ![1, 0, 0, 0, 0] ![1, 1, 0, 0, 0] := by
      unfold Conj; rw [m_e0, m_st]; exact hω.2.1
    have r1 : Conj g ω ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] := by
      unfold Conj; rw [m_e1, m_e0]; exact hω.1
    have r2 : Conj g ω ![0, 0, 1, 0, 0] ![0, 0, 1, 0, 0] := by
      unfold Conj; rw [m_e2]; exact hω.2.2.1
    have r3 : Conj g ω ![0, 0, 0, 1, 0] ![0, 0, 0, 1, 0] := by
      unfold Conj; rw [m_e3]; exact hω.2.2.2
    have r4 : Conj g ω ![0, 0, 0, 0, 1] ![a, b, 0, 0, 1] := by
      unfold Conj; rw [m_e4, ← m_x hg a b]; exact hωx
    intro j
    fin_cases j
    exacts [r0, r1, r2, r3, r4]
  have rC : ∀ j, Conj g c (Pa j) (Qa j) := by
    have r0 : Conj g c ![0, 1, 0, 0, 0] ![0, 1, 0, 0, 0] := by
      unfold Conj; rw [m_e1]; exact hc.1
    have r1 : Conj g c ![1, 0, 1, 0, 0] ![1, 0, 0, 1, 0] := by
      unfold Conj; rw [m_a0, m_a1]; exact hc.2.1
    have r2 : Conj g c ![1, 0, 0, 1, 0] ![1, 0, 1, 1, 0] := by
      unfold Conj; rw [m_a1, m_a2]; exact hc.2.2.1
    have r3 : Conj g c ![1, 0, 1, 1, 0] ![1, 0, 0, 0, 1] := by
      unfold Conj; rw [m_a2, m_a3]; exact hc.2.2.2.1
    have r4 : Conj g c ![1, 0, 0, 0, 1] ![1, 0, 1, 0, 0] := by
      unfold Conj; rw [m_a3, m_a0]; exact hc.2.2.2.2
    intro j
    fin_cases j
    exacts [r0, r1, r2, r3, r4]
  have Ω : ∀ u z, (∃ w : Fin 5 → ZMod 2, ∑ j, w j • Pid j = u ∧ ∑ j, w j • Mw a b j = z) →
      Conj g ω u z := fun _ _ hw => Conj.span hg rΩ hw
  have Cc : ∀ u z, (∃ w : Fin 5 → ZMod 2, ∑ j, w j • Pa j = u ∧ ∑ j, w j • Qa j = z) →
      Conj g c u z := fun _ _ hw => Conj.span hg rC hw
  have Ci : ∀ u z, (∃ w : Fin 5 → ZMod 2, ∑ j, w j • Qa j = u ∧ ∑ j, w j • Pa j = z) →
      Conj g c⁻¹ u z := fun _ _ hw => Conj.span hg (fun j => (rC j).inv) hw
  rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) a with rfl | rfl <;>
    rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) b with rfl | rfl
  ·
    have e1 : Conj g ω ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] := Ω _ _ (by decide)
    have e2 : Conj g c⁻¹ ![1, 0, 0, 0, 0] ![1, 0, 1, 1, 1] := Ci _ _ (by decide)
    have e3 : Conj g ω ![1, 0, 1, 1, 1] ![1, 1, 1, 1, 1] := Ω _ _ (by decide)
    have e4 : Conj g c ![1, 1, 1, 1, 1] ![1, 1, 0, 0, 0] := Cc _ _ (by decide)
    have e5 : Conj g ω ![1, 1, 0, 0, 0] ![0, 1, 0, 0, 0] := Ω _ _ (by decide)
    have f1 : Conj g ω ![1, 0, 0, 1, 0] ![1, 1, 0, 1, 0] := Ω _ _ (by decide)
    have f2 : Conj g c⁻¹ ![1, 1, 0, 1, 0] ![1, 1, 1, 0, 0] := Ci _ _ (by decide)
    have f3 : Conj g ω ![1, 1, 1, 0, 0] ![0, 1, 1, 0, 0] := Ω _ _ (by decide)
    have f4 : Conj g c ![0, 1, 1, 0, 0] ![0, 1, 1, 1, 1] := Cc _ _ (by decide)
    have f5 : Conj g ω ![0, 1, 1, 1, 1] ![1, 0, 1, 1, 1] := Ω _ _ (by decide)
    refine hP1 (ω * (c * (ω * (c⁻¹ * ω)))) ?_ ?_
    · have h := ((((e1.comp e2).comp e3).comp e4).comp e5)
      unfold Conj at h
      rwa [m_e1] at h
    · have h := ((((f1.comp f2).comp f3).comp f4).comp f5)
      unfold Conj at h
      rwa [m_a1, m_b] at h
  ·
    have h := Ω ![1, 1, 1, 1, 1] ![0, 0, 1, 1, 1] (by decide)
    exact hP2' (hS₁'.trans (isConj_iff.mpr ⟨ω, h⟩))
  ·
    have h₁ := Ω ![1, 0, 1, 1, 1] ![0, 1, 1, 1, 1] (by decide)
    have h₂ := Ω ![0, 1, 1, 1, 1] ![0, 0, 1, 1, 1] (by decide)
    exact hP2' ((hS₂'.trans (isConj_iff.mpr ⟨ω, h₁⟩)).trans (isConj_iff.mpr ⟨ω, h₂⟩))
  ·
    have h := Ω ![1, 0, 1, 1, 1] ![0, 0, 1, 1, 1] (by decide)
    exact hP2' (hS₂'.trans (isConj_iff.mpr ⟨ω, h⟩))

end CFSG.ComponentClassification.SolMax.Sig36.E32
