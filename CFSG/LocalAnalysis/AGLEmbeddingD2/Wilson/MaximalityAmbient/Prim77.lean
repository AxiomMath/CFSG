module

public import Mathlib.GroupTheory.GroupAction.Primitive
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Algebra.BigOperators.Fin
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.MaximalityAmbient.Over77
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.MaximalityAmbient.Prim77Data

public section

namespace CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.Prim77

open scoped Pointwise
open Equiv MulAction CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.Over77

theorem card_filter_fin_eq_countP (p : ℕ → Bool) (n : ℕ) :
    (Finset.univ.filter (fun y : Fin n => p y.val = true)).card = (List.range n).countP p := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.countP_append, ← ih, Finset.card_filter, Finset.card_filter,
      Fin.sum_univ_castSucc]
    simp [List.countP_cons]

theorem encP_pow (σ : Equiv.Perm (Fin 77)) (k : ℕ) : encP (σ ^ k) = powA (encP σ) k := by
  induction k with
  | zero => simp [powA, encP_one]
  | succ k ih => rw [pow_succ, encP_mul, ih]; rfl

theorem primCheck_parts (h : primCheck = true) :
    chkTrans = true ∧ chkStab = true ∧ chkOrders = true := by
  unfold primCheck at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

section Generic

variable (l : ℕ → Equiv.Perm (Fin 77)) (hl : ∀ k, encP (l k) = lettersData.getD k idA)
  (G : Subgroup (Equiv.Perm (Fin 77))) (hG : ∀ k, l k ∈ G)
include hl hG

theorem trans_word (hT : chkTrans = true) (i : Fin 77) : ∃ g ∈ G, g 0 = i := by
  unfold chkTrans at hT
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at hT
  have h := hT.2 i.val i.2
  refine ⟨evalPerm l (transWords.getD i.val []), evalPerm_mem l G hG _, ?_⟩
  have e := encP_evalPerm l lettersData hl (transWords.getD i.val [])
  have e2 := encP_getD (evalPerm l (transWords.getD i.val [])) (k := 0) (by norm_num)
  rw [e, h] at e2
  exact Fin.ext (by simpa using e2.symm)

theorem stab_word (hS : chkStab = true) (i : Fin 77) (hi : i ≠ 0) :
    ∃ h ∈ G, ∃ hr : repArr.getD i.val 0 < 77, h 0 = 0 ∧ h ⟨repArr.getD i.val 0, hr⟩ = i := by
  unfold chkStab at hS
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq,
    decide_eq_true_eq] at hS
  have h := hS.2 i.val i.2
  have hi' : i.val ≠ 0 := fun e => hi (Fin.ext e)
  rcases h with h | ⟨⟨h1, h2⟩, h3⟩
  · exact absurd h hi'
  have e := encP_evalPerm l lettersData hl (stabWords.getD i.val [])
  set w := evalPerm l (stabWords.getD i.val []) with hw
  have hr : repArr.getD i.val 0 < 77 := by
    by_contra hcon
    have : (evalW lettersData (stabWords.getD i.val [])).getD (repArr.getD i.val 0) 0 = 0 := by
      have hsz : (evalW lettersData (stabWords.getD i.val [])).size ≤ repArr.getD i.val 0 := by
        rw [← e]
        simp only [encP, Array.size_ofFn]
        omega
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none hsz]
      rfl
    rw [this] at h2
    exact hi' h2.symm
  refine ⟨w, evalPerm_mem l G hG _, hr, ?_, ?_⟩
  · have e2 := encP_getD w (k := 0) (by norm_num)
    rw [e, h1] at e2
    exact Fin.ext (by simpa using e2.symm)
  · have e2 := encP_getD w (k := repArr.getD i.val 0) hr
    rw [e, h2] at e2
    exact Fin.ext (by simpa using e2.symm)

omit hl hG in
theorem stab_count (hS : chkStab = true) (i : Fin 77) (hi : i ≠ 0) :
    12 ≤ (Finset.univ.filter
      (fun y : Fin 77 => y.val ≠ 0 ∧ repArr.getD y.val 0 = repArr.getD i.val 0)).card := by
  unfold chkStab at hS
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq,
    decide_eq_true_eq] at hS
  have hi' : i.val ≠ 0 := fun e => hi (Fin.ext e)
  rcases hS.2 i.val i.2 with h | ⟨-, h3⟩
  · exact absurd h hi'
  have := card_filter_fin_eq_countP
    (fun y => decide (y ≠ 0) && (repArr.getD y 0 == repArr.getD i.val 0)) 77
  have e : (Finset.univ.filter
      (fun y : Fin 77 => y.val ≠ 0 ∧ repArr.getD y.val 0 = repArr.getD i.val 0)) =
      Finset.univ.filter (fun y : Fin 77 =>
        (decide (y.val ≠ 0) && (repArr.getD y.val 0 == repArr.getD i.val 0)) = true) := by
    ext y
    simp
  rw [e, this]
  exact h3

theorem isPreprimitive_of_letters (hT : chkTrans = true) (hS : chkStab = true) :
    IsPreprimitive G (Fin 77) := by
  have hpre : IsPretransitive G (Fin 77) := by
    rw [isPretransitive_iff_base (0 : Fin 77)]
    intro y
    obtain ⟨g, hgG, hg0⟩ := trans_word l hl G hG hT y
    exact ⟨⟨g, hgG⟩, hg0⟩
  refine IsPreprimitive.of_isTrivialBlock_base (G := G) (0 : Fin 77) ?_
  intro B h0 hB
  by_cases hsub : B.Subsingleton
  · exact Or.inl hsub
  right
  obtain ⟨x, hxB, hx0⟩ : ∃ x ∈ B, x ≠ 0 := by
    simp only [Set.Subsingleton, not_forall] at hsub
    obtain ⟨a, ha, b, hb, hab⟩ := hsub
    by_cases ha0 : a = 0
    · exact ⟨b, hb, fun hb0 => hab (ha0.trans hb0.symm)⟩
    · exact ⟨a, ha, ha0⟩
  have hcls : ∀ y : Fin 77, y ≠ 0 → repArr.getD y.val 0 = repArr.getD x.val 0 → y ∈ B := by
    intro y hy hrep
    obtain ⟨hx', hxG, hrx, hx0', hxr⟩ := stab_word l hl G hG hS x hx0
    obtain ⟨hy', hyG, hry, hy0', hyr⟩ := stab_word l hl G hG hS y hy
    have hu : hy' * hx'⁻¹ ∈ G := G.mul_mem hyG (G.inv_mem hxG)
    have hr_eq : (⟨repArr.getD y.val 0, hry⟩ : Fin 77) = ⟨repArr.getD x.val 0, hrx⟩ :=
      Fin.ext hrep
    have hux : (hy' * hx'⁻¹) x = y := by
      have : hx'⁻¹ x = ⟨repArr.getD x.val 0, hrx⟩ := by
        rw [Equiv.Perm.inv_eq_iff_eq]; exact hxr.symm
      rw [Equiv.Perm.mul_apply, this, ← hr_eq, hyr]
    have hu0 : (hy' * hx'⁻¹) 0 = 0 := by
      have : hx'⁻¹ 0 = 0 := by rw [Equiv.Perm.inv_eq_iff_eq]; exact hx0'.symm
      rw [Equiv.Perm.mul_apply, this, hy0']
    have hblk := hB.smul_eq_or_disjoint (⟨hy' * hx'⁻¹, hu⟩ : G)
    have h0mem : (0 : Fin 77) ∈ (⟨hy' * hx'⁻¹, hu⟩ : G) • B :=
      Set.mem_smul_set.2 ⟨0, h0, hu0⟩
    have heq : (⟨hy' * hx'⁻¹, hu⟩ : G) • B = B := by
      rcases hblk with h | h
      · exact h
      · exact absurd h0 (Set.disjoint_left.1 h h0mem)
    rw [← heq]
    exact Set.mem_smul_set.2 ⟨x, hxB, hux⟩
  set F : Finset (Fin 77) := Finset.univ.filter
    (fun y : Fin 77 => y.val ≠ 0 ∧ repArr.getD y.val 0 = repArr.getD x.val 0) with hF
  have hsub' : ((insert (0 : Fin 77) F : Finset (Fin 77)) : Set (Fin 77)) ⊆ B := by
    intro y hy
    rw [Finset.mem_coe, Finset.mem_insert] at hy
    rcases hy with rfl | hy
    · exact h0
    · rw [hF, Finset.mem_filter] at hy
      exact hcls y (fun e => hy.2.1 (by rw [e]; rfl)) hy.2.2
  have hn : 13 ≤ B.ncard := by
    have h12 : 12 ≤ F.card := stab_count hS x hx0
    have hnot : (0 : Fin 77) ∉ F := by
      rw [hF]; simp
    calc 13 ≤ (insert (0 : Fin 77) F).card := by
          rw [Finset.card_insert_of_notMem hnot]; omega
      _ = ((insert (0 : Fin 77) F : Finset (Fin 77)) : Set (Fin 77)).ncard :=
          (Set.ncard_coe_finset _).symm
      _ ≤ B.ncard := Set.ncard_le_ncard hsub' (Set.toFinite B)
  have hdvd := hB.ncard_dvd_card ⟨0, h0⟩
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at hdvd
  have h77 : B.ncard = 77 := by
    obtain ⟨k, hk⟩ := hdvd
    have hk5 : k ≤ 5 := by
      by_contra hcon
      have := Nat.mul_le_mul hn (show 6 ≤ k by omega)
      omega
    interval_cases k <;> omega
  exact Set.eq_of_subset_of_ncard_le (Set.subset_univ B)
    (by rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]; omega)
    (Set.toFinite _)

omit hl hG in
theorem orderOf_eq_of_chkOrder {σ : Equiv.Perm (Fin 77)} {a : Array Nat} (h : encP σ = a) {p : ℕ}
    [Fact p.Prime] (hc : chkOrder a p = true) : orderOf σ = p := by
  unfold chkOrder at hc
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hc
  apply orderOf_eq_prime
  · apply encP_injective
    rw [encP_pow, h, hc.2, encP_one]
  · intro h1
    apply hc.1
    rw [← h, h1, encP_one]

omit hl hG in
theorem chkOrders_parts (h : chkOrders = true) :
    chkOrder dataS[0]! 3 = true ∧ chkOrder dataS[2]! 5 = true ∧ chkOrder dataS[3]! 7 = true ∧
      chkOrder dataS[4]! 11 = true ∧
      (powA (evalW lettersData w8Word) 4 != idA) = true ∧
        (powA (evalW lettersData w8Word) 8 == idA) = true := by
  unfold chkOrders at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2.1, h.2.2⟩

omit hG in
include hl in
theorem orderOf_word8 (h4 : (powA (evalW lettersData w8Word) 4 != idA) = true)
    (h8 : (powA (evalW lettersData w8Word) 8 == idA) = true) :
    orderOf (evalPerm l w8Word) = 8 := by
  have h : powA (evalW lettersData w8Word) 4 ≠ idA ∧ powA (evalW lettersData w8Word) 8 = idA := by
    simpa only [bne_iff_ne, ne_eq, beq_iff_eq] using And.intro h4 h8
  have e := encP_evalPerm l lettersData hl w8Word
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := orderOf_eq_prime_pow (p := 2) (n := 2) (x := evalPerm l w8Word) ?_ ?_
  · simpa using this
  · intro h4
    apply h.1
    rw [← e, ← encP_pow]
    have : evalPerm l w8Word ^ 4 = 1 := by simpa using h4
    rw [this, encP_one]
  · apply encP_injective
    rw [show 2 ^ (2 + 1) = 8 by norm_num, encP_pow, e, h.2, encP_one]

end Generic

end CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.Prim77
