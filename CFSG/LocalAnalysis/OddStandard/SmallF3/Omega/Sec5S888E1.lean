module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

private instance instDecidableIsEvenVec4 (v : Fin 4 → ZMod 2) : Decidable (IsEvenVec v) := by
  unfold IsEvenVec
  infer_instance

private def s888Invol : Finset (Equiv.Perm (Fin 4)) :=
  Finset.univ.filter (fun a => a * a = 1)

private def s888Fixed (S : Finset (Equiv.Perm (Fin 4))) : Finset (Fin 4 → ZMod 2) :=
  Finset.univ.filter (fun x => IsEvenVec x ∧ ∀ a ∈ S, ∀ i, x (a i) = x i)

private abbrev s888Pair (S : Finset (Equiv.Perm (Fin 4))) : Prop :=
  ∃ c d : Fin 4, c ≠ d ∧ ∀ a ∈ S, (a c = c ∧ a d = d) ∨ (a c = d ∧ a d = c)

private def s888Closed (S : Finset (Equiv.Perm (Fin 4))) : Bool :=
  decide (∀ a ∈ S, ∀ b ∈ S, a * b ∈ S)

private lemma s888Check :
    ∀ S ∈ s888Invol.powerset.filter (fun S => s888Closed S = true),
      S.card * (s888Fixed S).card < 16 ∨ s888Pair S := by
  decide +kernel

theorem comb_pair_of_card {P : Subgroup (Equiv.Perm (Fin 4))} (hP : ∀ a ∈ P, a * a = 1)
    {W : Finset (Fin 4 → ZMod 2)} (h0 : 0 ∈ W) (hadd : ∀ x ∈ W, ∀ y ∈ W, x + y ∈ W)
    (heven : ∀ x ∈ W, IsEvenVec x) (hfix : ∀ x ∈ W, ∀ a ∈ P, ∀ i, x (a i) = x i)
    (hcard : 16 ≤ Nat.card P * W.card) :
    ∃ c d : Fin 4, c ≠ d ∧ ∀ a ∈ P, (a c = c ∧ a d = d) ∨ (a c = d ∧ a d = c) := by
  classical
  let S : Finset (Equiv.Perm (Fin 4)) := Finset.univ.filter (fun a => a ∈ P)
  have hSmem : ∀ a, a ∈ S ↔ a ∈ P := by
    intro a
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
  have hSsub : S ⊆ s888Invol := by
    intro a ha
    rw [s888Invol, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hP a ((hSmem a).mp ha)⟩
  have hSclosed : s888Closed S = true := by
    rw [s888Closed, decide_eq_true_eq]
    intro a ha b hb
    exact (hSmem (a * b)).mpr (P.mul_mem ((hSmem a).mp ha) ((hSmem b).mp hb))
  have hScard : S.card = Nat.card P := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hWsub : W ⊆ s888Fixed S := by
    intro x hx
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, heven x hx, fun a ha i => hfix x hx a ((hSmem a).mp ha) i⟩
  have hle : Nat.card P * W.card ≤ S.card * (s888Fixed S).card := by
    rw [hScard]
    exact Nat.mul_le_mul_left _ (Finset.card_le_card hWsub)
  have hbig : 16 ≤ S.card * (s888Fixed S).card := le_trans hcard hle
  have hcheck := s888Check S
    (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hSsub, hSclosed⟩)
  rcases hcheck with hlt | hpair
  · exfalso; omega
  · obtain ⟨c, d, hcd, hcd'⟩ := hpair
    exact ⟨c, d, hcd, fun a ha => hcd' a ((hSmem a).mpr ha)⟩

end CFSG.OddStandard.SmallF3.Omega
