module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.F4Exc.Family
import CFSG.HardMathSupport.Cooperstein.Coordinator.F4Exc.PairsK

set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.F4Exc

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CoxeterSystem

theorem gamL_ne : ∀ (s : Fin Tag.F4.rank) (i i' : Fin 12), i ≠ i' → gamL s i ≠ gamL s i' := by
  decide +kernel

theorem pair_bound : ∀ (s : Fin Tag.F4.rank), (s.val = 0 ∨ s.val = 3) → ∀ (i i' : Fin 12)
    (j j' : Fin 8) (c : Fin Tag.F4.rank),
    ((betaL s i j).getD c 0 - (betaL s i' j').getD c 0).natAbs ≤ 8 ∧
      ((gamL s i).getD c 0 - (gamL s i').getD c 0).natAbs ≤ 8 := by
  decide +kernel

theorem pair_no_mult : ∀ (s : Fin Tag.F4.rank), (s.val = 0 ∨ s.val = 3) → ∀ (i i' : Fin 12),
    i ≠ i' → ∀ (j j' : Fin 8), ∀ cc ∈ ([3, 5] : List ℤ),
    ¬ ∀ c : Fin Tag.F4.rank, cc * ((betaL s i j).getD c 0 - (betaL s i' j').getD c 0) =
      (gamL s i).getD c 0 - (gamL s i').getD c 0 := by
  decide +kernel

@[expose] def vclassEq (M a dg : ℕ) (β β' γ γ' : List ℤ) : Bool :=
  (List.range 4).all fun c =>
    (((a : ℤ) * (β.getD c 0 - β'.getD c 0) - (2 : ℤ) ^ dg * (γ.getD c 0 - γ'.getD c 0)) % (M : ℤ)) == 0

@[expose] def digitOK (n b c dg : ℕ) (s : Fin Tag.F4.rank) : Bool :=
  (List.range 12).all fun i => (List.range 12).all fun i' => i == i' ||
    (List.range 8).all fun j => (List.range 8).all fun j' =>
      !vclassEq (2 ^ n - 1) (2 ^ b + 2 ^ c) dg (betaL s i j) (betaL s i' j') (gamL s i) (gamL s i')

@[expose] def smallOK : Bool :=
  (List.finRange Tag.F4.rank).all fun s => (s.val != 0 && s.val != 3) ||
    [2, 3, 4, 5, 6].all fun n => (List.range n).all fun b => (List.range n).all fun c =>
      decide (c ≤ b) || digitOK n b c b s || digitOK n b c c s

theorem smallOK_true : smallOK = true :=
  PairsK.smallG_mono PairsK.digitF digitOK (fun s hs _ _ _ _ h => PairsK.digitBody_of s hs h)
    PairsK.smallG_digitF

theorem digitOK_sound {n b c dg : ℕ} {s : Fin Tag.F4.rank} (h : digitOK n b c dg s = true)
    (i i' : Fin 12) (hii : i ≠ i') (j j' : Fin 8) :
    vclassEq (2 ^ n - 1) (2 ^ b + 2 ^ c) dg (betaL s i j) (betaL s i' j') (gamL s i) (gamL s i') =
      false := by
  simp only [digitOK, List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq,
    Bool.not_eq_true'] at h
  rcases h i i.2 i' i'.2 with h1 | h1
  · exact absurd (Fin.ext h1) hii
  · exact h1 j j.2 j' j'.2

theorem small_sep {s : Fin Tag.F4.rank} (hs : s.val = 0 ∨ s.val = 3) {n b c : ℕ}
    (hn : n ∈ ([2, 3, 4, 5, 6] : List ℕ)) (hb : b < n) (hc : c < n) (hbc : b < c) :
    digitOK n b c b s = true ∨ digitOK n b c c s = true := by
  have h := smallOK_true
  simp only [smallOK, List.all_eq_true, List.mem_finRange, Bool.or_eq_true, Bool.and_eq_true,
    bne_iff_ne, ne_eq, List.mem_range, decide_eq_true_eq, true_implies] at h
  rcases h s with h1 | h1
  · exfalso; rcases hs with h2 | h2 <;> simp [h2] at h1
  · have h2 := h1 n hn b hb c hc
    rcases h2 with (h2 | h2) | h2
    · omega
    · exact Or.inl h2
    · exact Or.inr h2

end CFSG.HardMathSupport.Cooperstein.Coordinator.F4Exc
