module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec4Pairs

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup

abbrev OtherPairs (k : ℕ) (i l : Fin k) : Type := {p : Fin k // p ≠ i ∧ p ≠ l}

noncomputable def otherHom (n k : ℕ) (h : 2 * k ≤ n) (i l : Fin k) :
    Perm (OtherPairs k i l) →* Perm (Fin n) :=
  (pairHom n k h).comp Equiv.Perm.ofSubtype

noncomputable def Q0 (n k : ℕ) (h : 2 * k ≤ n) (i l : Fin k) : Subgroup (Perm (Fin n)) :=
  (alternatingGroup (OtherPairs k i l)).map (otherHom n k h i l)

variable {n k : ℕ} {h : 2 * k ≤ n} {i l : Fin k}

theorem degQ0_otherHom_apply (c : Perm (OtherPairs k i l)) :
    otherHom n k h i l c = pairHom n k h (Equiv.Perm.ofSubtype c) := by
  unfold otherHom
  rfl

theorem degQ0_mem_iff {q : Perm (Fin n)} : q ∈ Q0 n k h i l ↔
    ∃ a ∈ alternatingGroup (OtherPairs k i l), otherHom n k h i l a = q :=
  Subgroup.mem_map

theorem otherHom_injective : Function.Injective (otherHom n k h i l) :=
  pairHom_injective.comp Equiv.Perm.ofSubtype_injective

theorem Q0_le_alternatingGroup : Q0 n k h i l ≤ alternatingGroup (Fin n) := by
  intro q hq
  obtain ⟨a, -, rfl⟩ := degQ0_mem_iff.mp hq
  rw [Perm.mem_alternatingGroup, degQ0_otherHom_apply]
  exact sign_pairHom _

theorem Q0_comm_stdInv : ∀ q ∈ Q0 n k h i l, q * stdInv n k h = stdInv n k h * q := by
  intro q hq
  obtain ⟨a, -, rfl⟩ := degQ0_mem_iff.mp hq
  rw [degQ0_otherHom_apply]
  exact pairHom_comm_stdInv _

theorem degQ0_commute_swap {α : Type*} [DecidableEq α] {f : Perm α} {x y : α} (hx : f x = x)
    (hy : f y = y) : Commute f (swap x y) := by
  show f * swap x y = swap x y * f
  rw [mul_swap_eq_swap_mul, hx, hy]

theorem degQ0_fix_pair_aux (c : Perm (OtherPairs k i l)) {p : Fin k} (hp : ¬(p ≠ i ∧ p ≠ l))
    (q : Fin 2) : otherHom n k h i l c (pairEmb n k h (p, q)) = pairEmb n k h (p, q) := by
  rw [degQ0_otherHom_apply, pairHom_apply_pair, Equiv.Perm.ofSubtype_apply_of_not_mem c hp]

theorem Q0_comm_dblPair : ∀ q ∈ Q0 n k h i l,
    q * dblPair n k h i l = dblPair n k h i l * q := by
  intro q hq
  obtain ⟨a, -, rfl⟩ := degQ0_mem_iff.mp hq
  have hi : ¬(i ≠ i ∧ i ≠ l) := fun hh => hh.1 rfl
  have hl : ¬(l ≠ i ∧ l ≠ l) := fun hh => hh.2 rfl
  exact (degQ0_commute_swap (degQ0_fix_pair_aux a hi 0) (degQ0_fix_pair_aux a hi 1)).mul_right
    (degQ0_commute_swap (degQ0_fix_pair_aux a hl 0) (degQ0_fix_pair_aux a hl 1))

theorem Q0_eq_closure : Q0 n k h i l = Subgroup.closure
    (otherHom n k h i l '' {c : Perm (OtherPairs k i l) | c.IsThreeCycle}) := by
  unfold Q0
  rw [← MonoidHom.map_closure, Equiv.Perm.closure_three_cycles_eq_alternating]

theorem otherHom_threeCycle_pow_three {c : Perm (OtherPairs k i l)} (hc : c.IsThreeCycle) :
    (otherHom n k h i l c) ^ 3 = 1 := by
  have h3 : c ^ 3 = 1 := by
    have := pow_orderOf_eq_one c
    rwa [Equiv.Perm.IsThreeCycle.orderOf hc] at this
  rw [← map_pow, h3, map_one]

theorem card_otherPairs (hil : i ≠ l) : Fintype.card (OtherPairs k i l) = k - 2 := by
  rw [Fintype.card_subtype]
  have hfil : (Finset.univ.filter fun p : Fin k => p ≠ i ∧ p ≠ l) = Finset.univ \ {i, l} := by
    ext p
    simp
  rw [hfil, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
    Fintype.card_fin, Finset.card_pair hil]

theorem degQ0_nonempty_mulEquiv :
    Nonempty (alternatingGroup (OtherPairs k i l) ≃* Q0 n k h i l) :=
  ⟨(alternatingGroup (OtherPairs k i l)).equivMapOfInjective (otherHom n k h i l)
    otherHom_injective⟩

theorem degQ0_five_le_card (hk : 7 ≤ k) (hil : i ≠ l) : 5 ≤ Nat.card (OtherPairs k i l) := by
  rw [Nat.card_eq_fintype_card, card_otherPairs hil]
  omega

theorem Q0_isSimpleGroup (hk : 7 ≤ k) (hil : i ≠ l) : IsSimpleGroup (Q0 n k h i l) := by
  obtain ⟨e⟩ := degQ0_nonempty_mulEquiv (n := n) (h := h) (i := i) (l := l)
  have : IsSimpleGroup (alternatingGroup (OtherPairs k i l)) :=
    alternatingGroup.isSimpleGroup (degQ0_five_le_card hk hil)
  exact e.symm.isSimpleGroup

theorem Q0_not_isSolvable (hk : 7 ≤ k) (hil : i ≠ l) : ¬ Group.IsSolvable (Q0 n k h i l) := by
  intro hsolv
  obtain ⟨e⟩ := degQ0_nonempty_mulEquiv (n := n) (h := h) (i := i) (l := l)
  have h5 := degQ0_five_le_card hk hil
  have : IsSimpleGroup (alternatingGroup (OtherPairs k i l)) :=
    alternatingGroup.isSimpleGroup h5
  have : Group.IsSolvable (alternatingGroup (OtherPairs k i l)) :=
    Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  have hcomm := (IsSimpleGroup.comm_iff_isSolvable (G := alternatingGroup (OtherPairs k i l))).mpr
    inferInstance
  have hle := alternatingGroup.isMulCommutative_iff_card_le_three.mp ⟨⟨hcomm⟩⟩
  omega

theorem card_Q0 (hk : 7 ≤ k) (hil : i ≠ l) : Nat.card (Q0 n k h i l) * 2 = (k - 2).factorial := by
  obtain ⟨e⟩ := degQ0_nonempty_mulEquiv (n := n) (h := h) (i := i) (l := l)
  have : Nontrivial (OtherPairs k i l) :=
    Fintype.one_lt_card_iff_nontrivial.mp (by rw [card_otherPairs hil]; omega)
  rw [← Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
    card_otherPairs hil]
  exact Nat.div_mul_cancel (Nat.dvd_factorial (by norm_num) (by omega))

end CFSG.OddStandard.Solomon75
