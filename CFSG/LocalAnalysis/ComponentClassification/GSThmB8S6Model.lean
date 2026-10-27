module

public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.ComponentClassification.GSThmB

namespace Eight

namespace S6M

open Equiv

abbrev V5 := Fin 5 → ZMod 2

@[expose] def lift6 (v : V5) : Fin 6 → ZMod 2 := fun i => if h : (i : ℕ) < 5 then v ⟨i, h⟩ else 0

@[expose] def red6 (w : Fin 6 → ZMod 2) : V5 := fun i => w i.castSucc + w 5

@[expose] def act (t : Perm (Fin 6)) (v : V5) : V5 := red6 (fun j => lift6 v (t.symm j))

@[expose] def ehat (j : Fin 6) : V5 := red6 (Pi.single j 1)

@[expose] def IsEven (v : V5) : Prop := ∑ i, v i = 0

instance : DecidablePred IsEven := fun v => inferInstanceAs (Decidable (∑ i, v i = 0))

@[expose] def s01 : Perm (Fin 6) := swap 0 1
@[expose] def s23 : Perm (Fin 6) := swap 2 3
@[expose] def s45 : Perm (Fin 6) := swap 4 5
@[expose] def d0213 : Perm (Fin 6) := swap 0 2 * swap 1 3

@[expose] def Vlist : List (Perm (Fin 6)) :=
  [1, s01, s23, s45, s01 * s23, s01 * s45, s23 * s45, s01 * s23 * s45]

@[expose] def V0list : List (Perm (Fin 6)) := [1, s01 * s23, s01 * s45, s23 * s45]

@[expose] def Wlist : List (Perm (Fin 6)) := Vlist ++ Vlist.map (d0213 * ·)

@[expose] def Blist : List (Perm (Fin 6)) :=
  [d0213, d0213 * s01 * s23, d0213 * s45, d0213 * s01 * s23 * s45]

@[expose] def Clist : List (Perm (Fin 6)) := [1, s01 * s23, s45, s01 * s23 * s45] ++ Blist

theorem act_add (t : Perm (Fin 6)) (v w : V5) : act t (v + w) = act t v + act t w := by
  funext i
  simp only [act, red6, lift6, Pi.add_apply]
  split_ifs <;> ring

theorem act_zero (t : Perm (Fin 6)) : act t 0 = 0 := by
  funext i
  simp [act, red6, lift6]

theorem lift6_red6 (w : Fin 6 → ZMod 2) : lift6 (red6 w) = fun j => w j + w 5 := by
  funext j
  simp only [lift6, red6]
  split_ifs with h
  · rfl
  · have hj : (j : ℕ) = 5 := by
      have := j.2
      omega
    have : j = 5 := Fin.ext hj
    subst this
    rw [CharTwo.add_self_eq_zero]

theorem red6_add_const (w : Fin 6 → ZMod 2) (c : ZMod 2) :
    red6 (fun j => w j + c) = red6 w := by
  funext i
  simp only [red6]
  rw [add_add_add_comm, CharTwo.add_self_eq_zero, add_zero]

theorem act_red6 (t : Perm (Fin 6)) (w : Fin 6 → ZMod 2) :
    act t (red6 w) = red6 (fun j => w (t.symm j)) := by
  simp only [act, lift6_red6]
  exact red6_add_const (fun j => w (t.symm j)) (w 5)

theorem act_ehat (t : Perm (Fin 6)) (j : Fin 6) : act t (ehat j) = ehat (t j) := by
  rw [ehat, act_red6, ehat]
  congr 1
  funext k
  by_cases hk : k = t j
  · subst hk
    simp
  · rw [Pi.single_eq_of_ne hk, Pi.single_eq_of_ne]
    intro h
    exact hk (by rw [← h, apply_symm_apply])

theorem ehat_castSucc (i : Fin 5) : ehat i.castSucc = Pi.single i 1 := by
  funext k
  have h5 : (5 : Fin 6) ≠ i.castSucc := (Fin.castSucc_lt_last i).ne'
  simp only [ehat, red6, Pi.single_apply, Fin.castSucc_inj, ite_eq_right h5, add_zero]

theorem sum_act (t : Perm (Fin 6)) (v : V5) : ∑ i, act t v i = ∑ i, v i := by
  have h1 : ∑ i : Fin 5, act t v i = ∑ j : Fin 6, lift6 v (t.symm j) := by
    simp only [act, red6]
    rw [Fin.sum_univ_castSucc (fun j => lift6 v (t.symm j)), Finset.sum_add_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have : (5 : ZMod 2) = 1 := rfl
    rw [Nat.cast_ofNat, this, one_mul]
    rfl
  have h2 : ∑ j : Fin 6, lift6 v (t.symm j) = ∑ j : Fin 6, lift6 v j :=
    Equiv.sum_comp t.symm (lift6 v)
  have h3 : ∑ j : Fin 6, lift6 v j = ∑ i : Fin 5, v i := by
    rw [Fin.sum_univ_castSucc]
    simp [lift6]
  rw [h1, h2, h3]

theorem isEven_act (t : Perm (Fin 6)) (v : V5) : IsEven (act t v) ↔ IsEven v := by
  rw [IsEven, IsEven, sum_act]

theorem Vlist_sub : (Vlist.all fun t => Wlist.contains t) = true := by decide

theorem Wlist_inv_cases :
    (Wlist.all fun t => !(t * t == 1) || Vlist.contains t || Blist.contains t) = true := by
  decide

@[expose] def allV : List V5 :=
  [0, 1].flatMap fun a => [0, 1].flatMap fun b => [0, 1].flatMap fun c =>
    [0, 1].flatMap fun d => [0, 1].map fun e => ![a, b, c, d, e]

@[expose] def veq (v w : V5) : Bool := (List.finRange 5).all fun i => v i == w i

theorem veq_iff {v w : V5} : veq v w = true ↔ v = w := by
  simp only [veq, List.all_eq_true, List.mem_finRange, beq_iff_eq, true_implies]
  exact ⟨fun h => funext h, fun h i => h ▸ rfl⟩

theorem zmod2_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x
  exacts [Or.inl rfl, Or.inr rfl]

theorem mem_allV (v : V5) : v ∈ allV := by
  have hv : v = ![v 0, v 1, v 2, v 3, v 4] := by
    funext i
    fin_cases i <;> rfl
  rw [hv]
  rcases zmod2_cases (v 0) with h0 | h0 <;> rcases zmod2_cases (v 1) with h1 | h1 <;>
    rcases zmod2_cases (v 2) with h2 | h2 <;> rcases zmod2_cases (v 3) with h3 | h3 <;>
    rcases zmod2_cases (v 4) with h4 | h4 <;> rw [h0, h1, h2, h3, h4] <;> decide

theorem allV_nodup : allV.Nodup := by decide +kernel

@[expose] def isEvenB (v : V5) : Bool := v 0 + v 1 + v 2 + v 3 + v 4 == 0

theorem isEvenB_iff {v : V5} : isEvenB v = true ↔ IsEven v := by
  simp only [isEvenB, beq_iff_eq, IsEven, Fin.sum_univ_five]

@[expose] def fixlen (P : List (Perm (Fin 6))) : ℕ :=
  (allV.filter fun v => P.all fun t => veq (act t v) v).length

@[expose] def evenfixlen (P : List (Perm (Fin 6))) : ℕ :=
  (allV.filter fun v => isEvenB v && P.all fun t => veq (act t v) v).length

theorem ncard_eq_length (p : V5 → Bool) : {v : V5 | p v = true}.ncard = (allV.filter p).length := by
  classical
  have h1 : {v : V5 | p v = true} = ((allV.filter p).toFinset : Set V5) := by
    ext v
    simp [mem_allV]
  rw [h1, Set.ncard_coe_finset, List.toFinset_card_of_nodup (allV_nodup.filter p)]

@[expose] def Klist : List V5 := [0, ![1, 1, 0, 0, 0], ![0, 0, 1, 1, 0], ![1, 1, 1, 1, 0]]

@[expose] def t135 : Perm (Fin 6) := s01 * s23 * s45

theorem Wlist_fix8 :
    (Wlist.all fun t => t == 1 || [s01, s23, s45].contains t || decide (fixlen [t] ≤ 8)) =
      true := by
  decide +kernel

theorem Blist_facts :
    (Blist.all fun t => fixlen [t] == 8 &&
      (Wlist.all fun s => !(s * t == t * s) || Clist.contains s) &&
      (Clist.all fun s => s == 1 || s == t || fixlen [t, s] == 4)) = true ∧
    fixlen Clist = 2 := by
  decide +kernel

theorem V0list_evenfix :
    (V0list.all fun t => t == 1 || (allV.all fun v => !(isEvenB v && veq (act t v) v) ||
      Klist.contains v)) = true := by
  decide +kernel

theorem t135_facts : evenfixlen [t135] = 4 ∧ fixlen V0list = 4 := by decide +kernel

theorem t135_mul : (V0list.all fun t => t == 1 || [s01, s23, s45].contains (t135 * t)) = true ∧
    t135 ∈ Vlist := by
  decide +kernel

theorem Vlist_fix : (allV.all fun v => !(Vlist.all fun t => veq (act t v) v) ||
      Klist.contains v) = true ∧
    (Klist.all fun v => isEvenB v && Vlist.all fun t => veq (act t v) v) = true := by
  decide +kernel

theorem Vlist_faithful : (Vlist.all fun t => t == 1 ||
    allV.any fun v => isEvenB v && !veq (act t v) v) = true := by
  decide +kernel

theorem Wlist_centK : (Wlist.all fun t => !(Klist.all fun v => veq (act t v) v) ||
    Vlist.contains t) = true := by
  decide +kernel

theorem Vlist_split : (Vlist.all fun t => V0list.contains t ||
    [s01, s23, s45, t135].contains t) = true := by
  decide +kernel

theorem Klist_facts : Klist.Nodup ∧ Klist.contains (ehat 4 + ehat 5) = true := by
  decide +kernel

@[expose] def listSub (L : List (Perm (Fin 6))) (h1 : (1 : Perm (Fin 6)) ∈ L)
    (hmul : (L.all fun s => L.all fun t => L.contains (s * t)) = true)
    (hinv : (L.all fun t => L.contains t⁻¹) = true) : Subgroup (Perm (Fin 6)) where
  carrier := {t | t ∈ L}
  mul_mem' {s t} hs ht := by
    have := List.all_eq_true.mp (List.all_eq_true.mp hmul s hs) t ht
    simpa using this
  one_mem' := h1
  inv_mem' {t} ht := by
    have := List.all_eq_true.mp hinv t ht
    simpa using this

theorem mem_listSub {L : List (Perm (Fin 6))} {h1 hmul hinv} {t : Perm (Fin 6)} :
    t ∈ listSub L h1 hmul hinv ↔ t ∈ L := Iff.rfl

theorem card_listSub {L : List (Perm (Fin 6))} {h1 hmul hinv} (hL : L.Nodup) :
    Nat.card (listSub L h1 hmul hinv) = L.length := by
  classical
  have h : ((listSub L h1 hmul hinv : Subgroup (Perm (Fin 6))) : Set (Perm (Fin 6))) =
      (L.toFinset : Set (Perm (Fin 6))) := by
    ext t
    simp [← mem_listSub (h1 := h1) (hmul := hmul) (hinv := hinv)]
  show Nat.card ↥((listSub L h1 hmul hinv : Set (Perm (Fin 6)))) = _
  rw [h, Nat.card_coe_set_eq, Set.ncard_coe_finset, List.toFinset_card_of_nodup hL]

theorem Wlist_closed : (1 : Perm (Fin 6)) ∈ Wlist ∧
    (Wlist.all fun s => Wlist.all fun t => Wlist.contains (s * t)) = true ∧
    (Wlist.all fun t => Wlist.contains t⁻¹) = true ∧ Wlist.Nodup ∧ Wlist.length = 16 := by
  decide +kernel

theorem Vlist_closed : (1 : Perm (Fin 6)) ∈ Vlist ∧
    (Vlist.all fun s => Vlist.all fun t => Vlist.contains (s * t)) = true ∧
    (Vlist.all fun t => Vlist.contains t⁻¹) = true ∧ Vlist.Nodup ∧ Vlist.length = 8 := by
  decide +kernel

theorem V0list_closed : (1 : Perm (Fin 6)) ∈ V0list ∧
    (V0list.all fun s => V0list.all fun t => V0list.contains (s * t)) = true ∧
    (V0list.all fun t => V0list.contains t⁻¹) = true ∧ V0list.Nodup ∧ V0list.length = 4 := by
  decide +kernel

theorem Clist_closed : (1 : Perm (Fin 6)) ∈ Clist ∧
    (Clist.all fun s => Clist.all fun t => Clist.contains (s * t)) = true ∧
    (Clist.all fun t => Clist.contains t⁻¹) = true ∧ Clist.Nodup ∧ Clist.length = 8 := by
  decide +kernel

@[expose] def Wsub : Subgroup (Perm (Fin 6)) :=
  listSub Wlist Wlist_closed.1 Wlist_closed.2.1 Wlist_closed.2.2.1

@[expose] def Vsub : Subgroup (Perm (Fin 6)) :=
  listSub Vlist Vlist_closed.1 Vlist_closed.2.1 Vlist_closed.2.2.1

@[expose] def V0sub : Subgroup (Perm (Fin 6)) :=
  listSub V0list V0list_closed.1 V0list_closed.2.1 V0list_closed.2.2.1

@[expose] def Csub : Subgroup (Perm (Fin 6)) :=
  listSub Clist Clist_closed.1 Clist_closed.2.1 Clist_closed.2.2.1

theorem card_Wsub : Nat.card Wsub = 16 := by
  rw [Wsub, card_listSub Wlist_closed.2.2.2.1, Wlist_closed.2.2.2.2]

theorem card_Vsub : Nat.card Vsub = 8 := by
  rw [Vsub, card_listSub Vlist_closed.2.2.2.1, Vlist_closed.2.2.2.2]

theorem card_V0sub : Nat.card V0sub = 4 := by
  rw [V0sub, card_listSub V0list_closed.2.2.2.1, V0list_closed.2.2.2.2]

theorem card_Csub : Nat.card Csub = 8 := by
  rw [Csub, card_listSub Clist_closed.2.2.2.1, Clist_closed.2.2.2.2]

theorem swap_fixlen : fixlen [s01] = 16 ∧ fixlen [s23] = 16 ∧ fixlen [s45] = 16 := by
  decide +kernel

theorem isSwap_of_mem {t : Perm (Fin 6)} (ht : t ∈ [s01, s23, s45]) : t.IsSwap := by
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at ht
  rcases ht with rfl | rfl | rfl
  · exact ⟨0, 1, by decide, rfl⟩
  · exact ⟨2, 3, by decide, rfl⟩
  · exact ⟨4, 5, by decide, rfl⟩

theorem one_not_mem_swaps : (1 : Perm (Fin 6)) ∉ [s01, s23, s45] := by decide

theorem Klist_ncard : {v : V5 | v ∈ Klist}.ncard = 4 := by
  classical
  have h : {v : V5 | v ∈ Klist} = (Klist.toFinset : Set V5) := by
    ext v
    simp
  rw [h, Set.ncard_coe_finset, List.toFinset_card_of_nodup Klist_facts.1]
  rfl

theorem evenfix_V0_le {t : Perm (Fin 6)} (ht : t ∈ V0list) (ht1 : t ≠ 1) :
    {v : V5 | (isEvenB v && veq (act t v) v) = true}.ncard ≤ 4 := by
  rw [← Klist_ncard]
  refine Set.ncard_le_ncard (fun v hv => ?_) (Set.toFinite _)
  have h1 := List.all_eq_true.mp V0list_evenfix t ht
  simp only [Bool.or_eq_true, beq_iff_eq, ht1, false_or] at h1
  have h2 := List.all_eq_true.mp h1 v (mem_allV v)
  simp only [Set.mem_ofPred_eq] at hv
  rw [hv] at h2
  simpa using h2

theorem Vlist_coset : (Vlist.all fun s => Vlist.all fun t => V0list.contains s ||
    V0list.contains t || V0list.contains (s⁻¹ * t)) = true := by
  decide +kernel

theorem Wlist_coset : (Wlist.all fun s => Wlist.all fun t => Vlist.contains s ||
    Vlist.contains t || Vlist.contains (s⁻¹ * t)) = true := by
  decide +kernel

theorem sign_odd {t : Perm (Fin 6)} (ht : t ∈ [s01, s23, s45, t135]) : Perm.sign t = -1 := by
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl
  · exact Perm.sign_swap (by decide)
  · exact Perm.sign_swap (by decide)
  · exact Perm.sign_swap (by decide)
  · rw [t135, s01, s23, s45, map_mul, map_mul, Perm.sign_swap (by decide),
      Perm.sign_swap (by decide), Perm.sign_swap (by decide)]
    rfl

theorem ehat4_odd : ¬ IsEven (ehat 4) := by
  rw [← isEvenB_iff]
  decide

end S6M

end Eight

end CFSG.ComponentClassification.GSThmB
