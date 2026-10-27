module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotQ2EnnolaFrame

public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap Module

section Family

variable {K : Type} [Field K] [CharP K 2] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}

structure IsOrthUnitFamily (Q : QuadraticForm K (Fin d → K)) {ι : Type*}
    (a a' : ι → Fin d → K) : Prop where
  unit : ∀ k, IsUnitPlane Q (a k) (a' k)
  orth_aa : ∀ k l, k ≠ l → polar Q (a k) (a l) = 0
  orth_aa' : ∀ k l, k ≠ l → polar Q (a k) (a' l) = 0
  orth_a'a' : ∀ k l, k ≠ l → polar Q (a' k) (a' l) = 0

theorem IsOrthUnitFamily.isEnnolaFrame {r : ℕ} {a a' : Fin (r + 1) → Fin d → K}
    (h : IsOrthUnitFamily Q a a') (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) :
    IsEnnolaFrame Q a a' :=
  ⟨hQ, hT, h.unit, h.orth_aa, h.orth_aa', h.orth_a'a'⟩

theorem IsOrthUnitFamily.cons {n : ℕ} {a a' : Fin n → Fin d → K} (h : IsOrthUnitFamily Q a a')
    {u u' : Fin d → K} (hu : IsUnitPlane Q u u') (h1 : ∀ k, polar Q u (a k) = 0)
    (h2 : ∀ k, polar Q u (a' k) = 0) (h3 : ∀ k, polar Q u' (a k) = 0)
    (h4 : ∀ k, polar Q u' (a' k) = 0) :
    IsOrthUnitFamily Q (Fin.cons u a : Fin (n + 1) → Fin d → K)
      (Fin.cons u' a' : Fin (n + 1) → Fin d → K) where
  unit k := by
    rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨k', rfl⟩
    · rw [Fin.cons_zero, Fin.cons_zero]
      exact hu
    · rw [Fin.cons_succ, Fin.cons_succ]
      exact h.unit k'
  orth_aa k l hkl := by
    rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨k', rfl⟩ <;>
      rcases Fin.eq_zero_or_eq_succ l with rfl | ⟨l', rfl⟩
    · exact absurd rfl hkl
    · exact h1 l'
    · rw [Fin.cons_succ, Fin.cons_zero, polar_comm]
      exact h1 k'
    · exact h.orth_aa k' l' fun h' => hkl (by rw [h'])
  orth_aa' k l hkl := by
    rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨k', rfl⟩ <;>
      rcases Fin.eq_zero_or_eq_succ l with rfl | ⟨l', rfl⟩
    · exact absurd rfl hkl
    · exact h2 l'
    · rw [Fin.cons_succ, Fin.cons_zero, polar_comm]
      exact h3 k'
    · exact h.orth_aa' k' l' fun h' => hkl (by rw [h'])
  orth_a'a' k l hkl := by
    rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨k', rfl⟩ <;>
      rcases Fin.eq_zero_or_eq_succ l with rfl | ⟨l', rfl⟩
    · exact absurd rfl hkl
    · exact h4 l'
    · rw [Fin.cons_succ, Fin.cons_zero, polar_comm]
      exact h4 k'
    · exact h.orth_a'a' k' l' fun h' => hkl (by rw [h'])

end Family

section Block

variable {K : Type} [Field K] [CharP K 2] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}

structure IsHypSystem (Q : QuadraticForm K (Fin d → K)) (N : ℕ) (e f : ℕ → Fin d → K) :
    Prop where
  map_e : ∀ l, Q (e l) = 0
  map_f : ∀ l, Q (f l) = 0
  ee : ∀ l m, polar Q (e l) (e m) = 0
  ff : ∀ l m, polar Q (f l) (f m) = 0
  ef : ∀ l m, l ≠ m → polar Q (e l) (f m) = 0
  ef_self : ∀ l, l < N → polar Q (e l) (f l) = 1

@[expose] def blockVec (e f : ℕ → Fin d → K) (i : ℕ) : Fin d → K :=
  if i % 2 = 0 then e (2 * (i / 2)) + f (2 * (i / 2))
  else e (2 * (i / 2)) + f (2 * (i / 2)) + f (2 * (i / 2) + 1)

@[expose] def blockVec' (e f : ℕ → Fin d → K) (i : ℕ) : Fin d → K :=
  if i % 2 = 0 then f (2 * (i / 2)) + e (2 * (i / 2) + 1) + f (2 * (i / 2) + 1)
  else e (2 * (i / 2) + 1) + f (2 * (i / 2) + 1)

variable {N : ℕ} {e f : ℕ → Fin d → K}

namespace IsHypSystem

variable (hS : IsHypSystem Q N e f)
include hS

theorem fe {l m : ℕ} (h : l ≠ m) : polar Q (f l) (e m) = 0 := by
  rw [polar_comm]
  exact hS.ef m l h.symm

theorem fe_self {l : ℕ} (h : l < N) : polar Q (f l) (e l) = 1 := by
  rw [polar_comm]
  exact hS.ef_self l h

theorem polar_blockVec_of_ne (i : ℕ) {l : ℕ} (h1 : l ≠ 2 * (i / 2)) (h2 : l ≠ 2 * (i / 2) + 1) :
    polar Q (blockVec e f i) (e l) = 0 ∧ polar Q (blockVec e f i) (f l) = 0 ∧
      polar Q (blockVec' e f i) (e l) = 0 ∧ polar Q (blockVec' e f i) (f l) = 0 := by
  have a1 := hS.ef _ _ h1.symm
  have a2 := hS.ef _ _ h2.symm
  have a3 := hS.fe h1.symm
  have a4 := hS.fe h2.symm
  unfold blockVec blockVec'
  split_ifs <;> simp only [polar_add_left, hS.ee, hS.ff, a1, a2, a3, a4, add_zero] <;>
    exact ⟨trivial, trivial, trivial, trivial⟩

theorem polar_blockVec_of_perp (i : ℕ) {w : Fin d → K}
    (hw : ∀ l, (l = 2 * (i / 2) ∨ l = 2 * (i / 2) + 1) →
      polar Q w (e l) = 0 ∧ polar Q w (f l) = 0) :
    polar Q w (blockVec e f i) = 0 ∧ polar Q w (blockVec' e f i) = 0 := by
  obtain ⟨b1, b2⟩ := hw _ (Or.inl rfl)
  obtain ⟨b3, b4⟩ := hw _ (Or.inr rfl)
  unfold blockVec blockVec'
  split_ifs <;> simp only [polar_add_right, b1, b2, b3, b4, add_zero] <;> exact ⟨trivial, trivial⟩

theorem isUnitPlane_blockVec {i : ℕ} (hi : 2 * (i / 2) + 1 < N) :
    IsUnitPlane Q (blockVec e f i) (blockVec' e f i) := by
  have hne : 2 * (i / 2) ≠ 2 * (i / 2) + 1 := by omega
  have a1 := hS.ef _ _ hne
  have a2 := hS.ef _ _ hne.symm
  have a3 := hS.fe hne
  have a4 := hS.fe hne.symm
  have a5 := hS.ef_self _ (by omega : 2 * (i / 2) < N)
  have a6 := hS.ef_self _ hi
  have a7 := hS.fe_self (by omega : 2 * (i / 2) < N)
  have a8 := hS.fe_self hi
  unfold blockVec blockVec'
  split_ifs
  · refine ⟨?_, ?_, ?_⟩ <;>
      simp only [QuadraticMap.map_add Q, polar_add_left, polar_add_right, hS.map_e, hS.map_f,
        hS.ee, hS.ff, a1, a2, a3, a4, a5, a6, a7, a8] <;> norm_num
  · refine ⟨?_, ?_, ?_⟩ <;>
      simp only [QuadraticMap.map_add Q, polar_add_left, polar_add_right, hS.map_e, hS.map_f,
        hS.ee, hS.ff, a1, a2, a3, a4, a5, a6, a7, a8] <;> norm_num

theorem polar_blockVec_same {i i' : ℕ} (hi : 2 * (i / 2) + 1 < N) (hii : i / 2 = i' / 2)
    (hpar : i % 2 ≠ i' % 2) :
    polar Q (blockVec e f i) (blockVec e f i') = 0 ∧
      polar Q (blockVec e f i) (blockVec' e f i') = 0 ∧
      polar Q (blockVec' e f i) (blockVec' e f i') = 0 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hne : 2 * (i / 2) ≠ 2 * (i / 2) + 1 := by omega
  have a1 := hS.ef _ _ hne
  have a2 := hS.ef _ _ hne.symm
  have a3 := hS.fe hne
  have a4 := hS.fe hne.symm
  have a5 := hS.ef_self _ (by omega : 2 * (i / 2) < N)
  have a6 := hS.ef_self _ hi
  have a7 := hS.fe_self (by omega : 2 * (i / 2) < N)
  have a8 := hS.fe_self hi
  unfold blockVec blockVec'
  rw [← hii]
  split_ifs with h h' h'
  · omega
  · refine ⟨?_, ?_, ?_⟩ <;>
      simp only [polar_add_left, polar_add_right, hS.ee, hS.ff, a1, a2, a3, a4, a5, a6, a7, a8] <;>
      grind
  · refine ⟨?_, ?_, ?_⟩ <;>
      simp only [polar_add_left, polar_add_right, hS.ee, hS.ff, a1, a2, a3, a4, a5, a6, a7, a8] <;>
      grind
  · omega

theorem polar_blockVec_ne {i i' : ℕ} (hi : 2 * (i / 2) + 1 < N) (hne : i ≠ i') :
    polar Q (blockVec e f i) (blockVec e f i') = 0 ∧
      polar Q (blockVec e f i) (blockVec' e f i') = 0 ∧
      polar Q (blockVec' e f i) (blockVec' e f i') = 0 := by
  by_cases hii : i / 2 = i' / 2
  · exact hS.polar_blockVec_same hi hii (by omega)
  · have hw : ∀ l, (l = 2 * (i' / 2) ∨ l = 2 * (i' / 2) + 1) →
        (polar Q (blockVec e f i) (e l) = 0 ∧ polar Q (blockVec e f i) (f l) = 0) ∧
          (polar Q (blockVec' e f i) (e l) = 0 ∧ polar Q (blockVec' e f i) (f l) = 0) := by
      intro l hl
      have h := hS.polar_blockVec_of_ne i (l := l) (by omega) (by omega)
      exact ⟨⟨h.1, h.2.1⟩, ⟨h.2.2.1, h.2.2.2⟩⟩
    have h1 := hS.polar_blockVec_of_perp i' (w := blockVec e f i) fun l hl => (hw l hl).1
    have h2 := hS.polar_blockVec_of_perp i' (w := blockVec' e f i) fun l hl => (hw l hl).2
    exact ⟨h1.1, h1.2, h2.2⟩

theorem isOrthUnitFamily_blocks {n : ℕ} (hn : ∀ i, i < n → 2 * (i / 2) + 1 < N) :
    IsOrthUnitFamily Q (fun i : Fin n => blockVec e f i) (fun i : Fin n => blockVec' e f i) where
  unit i := hS.isUnitPlane_blockVec (hn i i.2)
  orth_aa k _ hkl := (hS.polar_blockVec_ne (hn k k.2) (Fin.val_injective.ne hkl)).1
  orth_aa' k _ hkl := (hS.polar_blockVec_ne (hn k k.2) (Fin.val_injective.ne hkl)).2.1
  orth_a'a' k _ hkl := (hS.polar_blockVec_ne (hn k k.2) (Fin.val_injective.ne hkl)).2.2

end IsHypSystem

end Block

end CFSG.SeitzReduction.OmegaPilot
