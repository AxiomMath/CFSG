module

public import Certificates.Data.Kernel.Kc3E16T
public import CFSG.Certificates.Kernel.Kc3E16KSound
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Data.Set.Card

public section

namespace CFSG.KC.Kc3K

open CFSG.KC.Enum

theorem trK_spec {g M : Nat} {app : Nat → Nat → Nat} {E PG : Nat → Nat} {o j : Nat}
    (h : trK g M app E PG o j = true) :
    (j + 1 < M → E j < E (j + 1)) ∧
    (E j = o ∨ (Nat.land (PG j) 65535 < M ∧ Nat.land (Nat.shiftRight (PG j) 16) 15 < g ∧
      Nat.shiftRight (PG (Nat.land (PG j) 65535)) 20 < Nat.shiftRight (PG j) 20 ∧
      E j = app (Nat.land (Nat.shiftRight (PG j) 16) 15) (E (Nat.land (PG j) 65535)))) := by
  simp only [trK, strictB_eqK, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun hj => ?_, ?_⟩
  · rcases h1 with h1 | h1
    · exact absurd hj h1
    · exact h1
  · rcases h2 with h2 | ⟨⟨⟨hp, ht⟩, hd⟩, he⟩
    · exact Or.inl h2
    · exact Or.inr ⟨hp, ht, hd, he⟩

theorem trK_sound {g M : Nat} {app : Nat → Nat → Nat} {E PG : Nat → Nat} {o : Nat}
    (h : ∀ j < M, trK g M app E PG o j = true) (S : Nat → Prop) (ho : S o)
    (happ : ∀ t < g, ∀ c, S c → S (app t c)) :
    (∀ j < M, S (E j)) ∧ ∀ i < M, ∀ j < M, E i = E j → i = j := by
  refine ⟨?_, ?_⟩
  · have key : ∀ d, ∀ j < M, Nat.shiftRight (PG j) 20 = d → S (E j) := by
      intro d
      induction d using Nat.strong_induction_on with
      | _ d ih =>
        intro j hj hd
        rcases (trK_spec (h j hj)).2 with h1 | ⟨hp, ht, hdep, he⟩
        · rw [h1]
          exact ho
        · rw [he]
          exact happ _ ht _ (ih _ (hd ▸ hdep) _ hp rfl)
    exact fun j hj => key _ j hj rfl
  · have hstrict : ∀ a b, a < b → b < M → E a < E b := by
      intro a b hab hb
      induction b with
      | zero => omega
      | succ b ih =>
        rcases Nat.lt_succ_iff_lt_or_eq.1 hab with h' | rfl
        · exact Nat.lt_trans (ih h' (by omega)) ((trK_spec (h b (by omega))).1 hb)
        · exact (trK_spec (h a (by omega))).1 hb
    intro i hi j hj e
    rcases Nat.lt_trichotomy i j with h' | h' | h'
    · exact absurd e (Nat.ne_of_lt (hstrict i j h' hj))
    · exact h'
    · exact absurd e.symm (Nat.ne_of_lt (hstrict j i h' hi))

theorem insK_eq (x : Nat) : ∀ l : List Nat, insK x l = l.orderedInsert (· ≤ ·) x
  | [] => (List.orderedInsert_nil _ x).symm
  | y :: l => by
    rw [List.orderedInsert_cons]
    change @Bool.rec (fun _ => List Nat) (y :: insK x l) (x :: y :: l) (Nat.ble x y) = _
    by_cases hxy : x ≤ y
    · rw [Nat.ble_eq_true_of_le hxy, if_pos hxy]
    · have hb : Nat.ble x y = false := by
        rcases Bool.eq_false_or_eq_true (Nat.ble x y) with hb | hb
        · exact absurd (Nat.le_of_ble_eq_true hb) hxy
        · exact hb
      rw [hb, if_neg hxy, insK_eq x l]

theorem sortK_eq : ∀ l : List Nat, sortK l = l.insertionSort (· ≤ ·)
  | [] => (List.insertionSort_nil _).symm
  | x :: l => by
    change insK x (sortK l) = _
    rw [insK_eq, sortK_eq l, List.insertionSort_cons]

theorem sortK_perm (l : List Nat) : (sortK l).Perm l := by
  rw [sortK_eq]
  exact List.perm_insertionSort _ l

theorem sortK_pairwise (l : List Nat) : (sortK l).Pairwise (· ≤ ·) := by
  rw [sortK_eq]
  exact List.pairwise_insertionSort _ l

theorem sortK_of_perm {l l' : List Nat} (h : l.Perm l') : sortK l = sortK l' :=
  List.Perm.eq_of_pairwise' (sortK_pairwise l) (sortK_pairwise l')
    ((sortK_perm l).trans (h.trans (sortK_perm l').symm))

theorem pg_packL {w m : Nat} (hm : m = 2 ^ w - 1) :
    ∀ (l : List Nat), (∀ x ∈ l, x < 2 ^ w) → ∀ i < l.length, pg w m (packL w l) i = l.getD i 0
  | [], _, i, hi => absurd hi (Nat.not_lt_zero _)
  | x :: l, hl, i, hi => by
    have hx : x < 2 ^ w := hl x List.mem_cons_self
    have hp : 0 < 2 ^ w := Nat.two_pow_pos w
    change Nat.land (Nat.shiftRight (packL w (x :: l)) (Nat.mul w i)) m = _
    rw [packL_cons, hm]
    change (x + 2 ^ w * packL w l) >>> (w * i) &&& 2 ^ w - 1 = _
    cases i with
    | zero =>
      rw [Nat.mul_zero, Nat.shiftRight_zero, Nat.and_two_pow_sub_one_eq_mod,
        Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx]
      rfl
    | succ i =>
      have e2 : (x + 2 ^ w * packL w l) >>> w = packL w l := by
        rw [Nat.shiftRight_eq_div_pow, Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt hx,
          Nat.zero_add]
      have e : (x + 2 ^ w * packL w l) >>> (w * (i + 1)) = packL w l >>> (w * i) := by
        rw [Nat.mul_succ, Nat.add_comm (w * i) w, Nat.shiftRight_add, e2]
      rw [e]
      have := pg_packL hm l (fun y hy => hl y (List.mem_cons_of_mem _ hy)) i
        (by simpa using hi)
      rw [List.getD_cons_succ, ← this, hm]
      rfl

theorem decL_packL {w m : Nat} (hm : m = 2 ^ w - 1) {l : List Nat} (hl : ∀ x ∈ l, x < 2 ^ w) :
    decL w m l.length (packL w l) = l := by
  apply List.ext_getElem (by simp [decL])
  intro i h1 h2
  simp only [decL, List.getElem_map, List.getElem_range]
  rw [pg_packL hm l hl i h2]
  simp [List.getD_eq_getElem?_getD, h2]

theorem elQ_spec {N e0 ng : Nat} {ky : Nat → Nat} {tg : Nat → Nat → Nat} {Q : Nat → Nat} {k : Nat}
    (h : elQ N e0 ng ky tg Q k = true) :
    (k + 1 < N → ky k < ky (k + 1)) ∧
    (k = e0 ∨ (Nat.land (Q k) 1023 < N ∧ Nat.land (Nat.shiftRight (Q k) 10) 3 < ng ∧
      tg (Nat.land (Nat.shiftRight (Q k) 10) 3) (Nat.land (Q k) 1023) = k ∧
      Nat.shiftRight (Q (Nat.land (Q k) 1023)) 12 < Nat.shiftRight (Q k) 12)) := by
  simp only [elQ, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun hk => ?_, ?_⟩
  · rcases h1 with h1 | h1
    · exact absurd hk h1
    · exact h1
  · rcases h2 with h2 | ⟨⟨⟨hp, hc⟩, ht⟩, hd⟩
    · exact Or.inl h2
    · exact Or.inr ⟨hp, hc, ht, hd⟩

theorem ivX_spec {w m : Nat} {TF : Nat → Nat} {B : List Nat} {vu vv : Nat → Nat} {i : Nat}
    (h : ivX w m TF B vu vv i = true) :
    (∀ b ∈ B, exK w m TF (vu i) (vv i) (exK w m TF (vu i) (vv i) b) = b) ∧
    ∃ b ∈ B, exK w m TF (vu i) (vv i) b ≠ b := by
  simp only [ivX, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, beq_iff_eq,
    bne_iff_ne, ne_eq] at h
  exact h

theorem fbK_spec {F : Nat → Nat} {L : List Nat} (h : fbK F L = true) :
    ∀ x ∈ L, (L.filter fun y => F y == F x).length < 10 := by
  simpa [fbK, List.all_eq_true] using h

theorem clsK_spec {M : Nat} {pr : Nat → Nat → Nat} {L : List Nat} (h : clsK M pr L = true) :
    L.Nodup ∧ (∀ x ∈ L, x < M) ∧ ∀ i ∈ L, ∀ j ∈ L, i ≠ j → pr i j ∈ L := by
  unfold clsK at h
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq,
    List.contains_iff_mem] at h
  obtain ⟨⟨hc, hlt⟩, hall⟩ := h
  refine ⟨(chainLt_sorted L hc).imp (fun h => h.ne), hlt, fun i hi j hj hij => ?_⟩
  rcases hall i hi j hj with h1 | h1
  · exact absurd h1 hij
  · exact h1

theorem fixE_spec {FL : Nat → List Nat} {FM : Nat → Nat} {i : Nat} {L : List Nat}
    (hnd : (FL i).Nodup) :
    (fixE FL FM (i :: L)).Nodup ∧ ∀ p, p ∈ fixE FL FM (i :: L) ↔
      p ∈ FL i ∧ ∀ j ∈ L, (FM j).testBit p = true := by
  have e : fixE FL FM (i :: L) = sortK ((FL i).filter fun p => L.all fun j => (FM j).testBit p) :=
    rfl
  rw [e]
  refine ⟨(sortK_perm _).nodup_iff.2 (hnd.filter _), fun p => ?_⟩
  rw [(sortK_perm _).mem_iff, List.mem_filter, List.all_eq_true]

section E

variable {w m M : Nat} {TF : Nat → Nat} {B : List Nat} {vu vv : Nat → Nat}

theorem cjEK_spec {SL : List Nat} {y : Nat} {PI : List Nat}
    (h : cjEK w m TF B vu vv SL y PI = true) :
    PI.length = 16 ∧ PI.getD 0 0 = 0 ∧ ∀ u, 0 < u → u < 16 →
      0 < PI.getD u 0 ∧ PI.getD u 0 < 16 ∧ ∀ b ∈ B,
        pg w m (TF y) (ivA w m TF vu vv (SL.getD u 0) b) =
          ivA w m TF vu vv (SL.getD (PI.getD u 0) 0) (pg w m (TF y) b) := by
  unfold cjEK at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    decide_eq_true_eq] at h
  obtain ⟨⟨hlen, h0⟩, hall⟩ := h
  refine ⟨hlen, h0, fun u hu0 hu => ?_⟩
  rcases hall u hu with h1 | ⟨⟨h1, h2⟩, h3⟩
  · omega
  · exact ⟨h1, h2, fun b hb => h3 b hb⟩

theorem clEK_spec {SL : List Nat} {y : Nat} {CL : List Nat} {e : Nat}
    (h : clEK w m M TF B vu vv SL y CL e = true) :
    ∀ u, 0 < u → u < 16 → CL.getD u 0 < M ∧ e.testBit (CL.getD u 0) = true ∧ ∀ b ∈ B,
      pg w m (TF y) (ivA w m TF vu vv (SL.getD u 0) b) =
        ivA w m TF vu vv (CL.getD u 0) (pg w m (TF y) b) := by
  unfold clEK at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    decide_eq_true_eq] at h
  intro u hu0 hu
  rcases h u hu with h1 | ⟨⟨h1, h2⟩, h3⟩
  · omega
  · exact ⟨h1, h2, fun b hb => h3 b hb⟩

end E

theorem ndK_of_nodup : ∀ (l : List Nat) (acc : Nat), l.Nodup → (∀ x ∈ l, acc.testBit x = false) →
    ndK l acc = true
  | [], _, _, _ => rfl
  | x :: l, acc, hnd, hacc => by
    have e : ndK (x :: l) acc = (!(acc.testBit x) && ndK l (acc ||| (1 <<< x))) := rfl
    rw [e, Bool.and_eq_true, Bool.not_eq_true']
    obtain ⟨hx, hnd⟩ := List.nodup_cons.1 hnd
    refine ⟨hacc x List.mem_cons_self, ndK_of_nodup l _ hnd fun y hy => ?_⟩
    rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow, hacc y (List.mem_cons_of_mem _ hy)]
    have : y ≠ x := fun e => hx (e ▸ hy)
    simp [Ne.symm this]

section Span

variable {G : Type} [Group G] {E : Subgroup G}

theorem span_step (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hsq : ∀ x ∈ E, x * x = 1)
    {A : List G} (hnd : A.Nodup) (hA : ∀ a ∈ A, a ∈ E ∧ a ≠ 1)
    (hcl : ∀ a ∈ A, ∀ a' ∈ A, a ≠ a' → a * a' ∈ A) {b : G} (hb : b ∈ E) (hb1 : b ≠ 1)
    (hbA : b ∉ A) :
    (A ++ b :: A.map (b * ·)).Nodup ∧ (∀ a ∈ A ++ b :: A.map (b * ·), a ∈ E ∧ a ≠ 1) ∧
      (∀ a ∈ A ++ b :: A.map (b * ·), ∀ a' ∈ A ++ b :: A.map (b * ·), a ≠ a' →
        a * a' ∈ A ++ b :: A.map (b * ·)) := by
  have hba : ∀ a ∈ A, b * a ∉ A := by
    intro a ha hm
    by_cases e : b * a = a
    · exact hb1 (by simpa using e)
    · have h1 := hcl _ hm a ha e
      have h2 : b * a * a = b := by rw [mul_assoc, hsq a (hA a ha).1, mul_one]
      rw [h2] at h1
      exact hbA h1
  have m1 : ∀ z ∈ A, z ∈ A ++ b :: A.map (b * ·) := fun z hz => List.mem_append_left _ hz
  have m2 : b ∈ A ++ b :: A.map (b * ·) := List.mem_append_right _ List.mem_cons_self
  have m3 : ∀ z ∈ A, b * z ∈ A ++ b :: A.map (b * ·) := fun z hz =>
    List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_map_of_mem hz))
  have hmem : ∀ x, x ∈ A ++ b :: A.map (b * ·) → x ∈ A ∨ x = b ∨ ∃ a ∈ A, x = b * a := by
    intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · exact Or.inl hx
    · rcases List.mem_cons.1 hx with rfl | hx
      · exact Or.inr (Or.inl rfl)
      · obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hx
        exact Or.inr (Or.inr ⟨a, ha, rfl⟩)
  refine ⟨?_, ?_, ?_⟩
  · refine List.nodup_append.2 ⟨hnd, List.nodup_cons.2 ⟨fun hm => ?_, ?_⟩, ?_⟩
    · obtain ⟨a, ha, e⟩ := List.mem_map.1 hm
      exact (hA a ha).2 (by simpa using e)
    · exact hnd.map (fun x y e => mul_left_cancel e)
    · intro x hx y hy e
      subst e
      rcases List.mem_cons.1 hy with rfl | hy
      · exact hbA hx
      · obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hy
        exact hba a ha hx
  · intro x hx
    rcases hmem x hx with hx | rfl | ⟨a, ha, rfl⟩
    · exact hA x hx
    · exact ⟨hb, hb1⟩
    · refine ⟨E.mul_mem hb (hA a ha).1, fun e => hbA ?_⟩
      have : b = a := by
        calc b = b * (a * a) := by rw [hsq a (hA a ha).1, mul_one]
          _ = b * a * a := by rw [mul_assoc]
          _ = a := by rw [e, one_mul]
      rw [this]
      exact ha
  · intro x hx y hy hxy
    have hxE : x ∈ E := by
      rcases hmem x hx with hx | rfl | ⟨a, ha, rfl⟩
      · exact (hA x hx).1
      · exact hb
      · exact E.mul_mem hb (hA a ha).1
    rcases hmem x hx with hx' | rfl | ⟨a, ha, rfl⟩ <;>
      rcases hmem y hy with hy' | rfl | ⟨a', ha', rfl⟩
    · exact m1 _ (hcl x hx' y hy' hxy)
    · rw [hcomm x hxE y hb]
      exact m3 x hx'
    · have e : x * (b * a') = b * (x * a') := by
        calc x * (b * a') = (x * b) * a' := by rw [mul_assoc]
          _ = (b * x) * a' := by rw [hcomm x hxE b hb]
          _ = b * (x * a') := by rw [mul_assoc]
      rw [e]
      by_cases hxa : x = a'
      · rw [hxa, hsq a' (hA a' ha').1, mul_one]
        exact m2
      · exact m3 _ (hcl x hx' a' ha' hxa)
    · exact m3 y hy'
    · exact absurd rfl hxy
    · rw [← mul_assoc, hsq _ hb, one_mul]
      exact m1 a' ha'
    · have e : b * a * y = b * (a * y) := mul_assoc _ _ _
      rw [e]
      by_cases hay : a = y
      · rw [hay, hsq y (hA y hy').1, mul_one]
        exact m2
      · exact m3 _ (hcl a ha y hy' hay)
    · have e : y * a * y = a := by
        calc y * a * y = y * (a * y) := by rw [mul_assoc]
          _ = y * (y * a) := by rw [hcomm a (hA a ha).1 y hb]
          _ = a := by rw [← mul_assoc, hsq y hb, one_mul]
      rw [e]
      exact m1 a ha
    · have e : b * a * (b * a') = a * a' := by
        calc b * a * (b * a') = b * (a * b) * a' := by simp only [mul_assoc]
          _ = b * (b * a) * a' := by rw [hcomm a (hA a ha).1 b hb]
          _ = a * a' := by rw [← mul_assoc, hsq b hb, one_mul]
      rw [e]
      have haa : a ≠ a' := fun h => hxy (by rw [h])
      exact m1 _ (hcl a ha a' ha' haa)

theorem exists_not_mem (hcard : Nat.card E = 16) {A : List G} (hA : A.length < 15) :
    ∃ x ∈ E, x ≠ 1 ∧ x ∉ A := by
  classical
  by_contra hne0
  have hne : ∀ x ∈ E, x ≠ 1 → x ∈ A := fun x hx h1 => by
    by_contra hxA
    exact hne0 ⟨x, hx, h1, hxA⟩
  have hsub : (E : Set G) ⊆ ↑(1 :: A).toFinset := by
    intro x hx
    rw [Finset.mem_coe, List.mem_toFinset]
    by_cases h1 : x = 1
    · rw [h1]
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (hne x hx h1)
  have h1 : Nat.card E = (E : Set G).ncard := Nat.card_coe_set_eq (E : Set G)
  have h2 := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
  rw [Set.ncard_coe_finset] at h2
  have h3 := List.toFinset_card_le (1 :: A)
  rw [List.length_cons] at h3
  omega

theorem mem_of_length (hcard : Nat.card E = 16) {A : List G} (hnd : A.Nodup)
    (hA : ∀ a ∈ A, a ∈ E ∧ a ≠ 1) (hlen : A.length = 15) : ∀ x ∈ E, x ≠ 1 → x ∈ A := by
  classical
  intro x hx hx1
  by_contra hxA
  have hnd' : (1 :: x :: A).Nodup := by
    refine List.nodup_cons.2 ⟨fun hm => ?_, List.nodup_cons.2 ⟨hxA, hnd⟩⟩
    rcases List.mem_cons.1 hm with h | h
    · exact hx1 h.symm
    · exact (hA 1 h).2 rfl
  have hsub : (↑(1 :: x :: A).toFinset : Set G) ⊆ (E : Set G) := by
    intro y hy
    rw [Finset.mem_coe, List.mem_toFinset] at hy
    rcases List.mem_cons.1 hy with rfl | hy
    · exact E.one_mem
    · rcases List.mem_cons.1 hy with rfl | hy
      · exact hx
      · exact (hA y hy).1
  have hfin : (E : Set G).Finite :=
    Set.finite_coe_iff.1 (Nat.finite_of_card_ne_zero (by
      change Nat.card E ≠ 0
      rw [hcard]
      decide))
  have h1 : Nat.card E = (E : Set G).ncard := Nat.card_coe_set_eq (E : Set G)
  have h2 := Set.ncard_le_ncard hsub hfin
  rw [Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd'] at h2
  simp only [List.length_cons, hlen] at h2
  omega

end Span

theorem extS_map {G : Type} [Group G] {E : Subgroup G} {M : Nat} {elt : Nat → G}
    {pr : Nat → Nat → Nat} (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hpr : ∀ i < M, ∀ j < M, i ≠ j → elt i * elt j = elt j * elt i →
      pr i j < M ∧ elt (pr i j) = elt i * elt j)
    {L : List Nat} (hL : ∀ x ∈ L, x < M ∧ elt x ∈ E) {i : Nat} (hi : i < M) (hiE : elt i ∈ E)
    (hiL : elt i ∉ L.map elt) :
    (∀ x ∈ extS pr L i, x < M ∧ elt x ∈ E) ∧
      (extS pr L i).map elt = L.map elt ++ elt i :: (L.map elt).map (elt i * ·) := by
  have hp : ∀ x ∈ L, pr i x < M ∧ elt (pr i x) = elt i * elt x := fun x hx =>
    hpr i hi x (hL x hx).1 (fun e => hiL (e ▸ List.mem_map_of_mem hx))
      (hcomm _ hiE _ (hL x hx).2)
  refine ⟨fun x hx => ?_, ?_⟩
  · rcases List.mem_append.1 hx with hx | hx
    · exact hL x hx
    · rcases List.mem_cons.1 hx with rfl | hx
      · exact ⟨hi, hiE⟩
      · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
        refine ⟨(hp y hy).1, ?_⟩
        rw [(hp y hy).2]
        exact E.mul_mem hiE (hL y hy).2
  · rw [extS, List.map_append, List.map_cons, List.map_map, List.map_map]
    congr 2
    exact List.map_congr_left fun x hx => (hp x hx).2

theorem cmpK_sound {G : Type} [Group G] {R : Subgroup G} {M : Nat} {elt : Nat → G}
    {pr : Nat → Nat → Nat} {NB : Nat → List Nat} {NM : Nat → Nat} {EM : List Nat}
    (hlist : ∀ x ∈ R, x * x = 1 → x ≠ 1 → ∃ k < M, elt k = x)
    (hinj : ∀ k < M, ∀ k' < M, elt k = elt k' → k = k')
    (hpr : ∀ i < M, ∀ j < M, i ≠ j → elt i * elt j = elt j * elt i →
      pr i j < M ∧ elt (pr i j) = elt i * elt j)
    (hnbr : ∀ i < M, ∀ j < M, i ≠ j → elt i * elt j = elt j * elt i → j ∈ NB i)
    (hnm : ∀ i < M, ∀ j ∈ NB i, (NM i).testBit j = true)
    (h : ∀ i < M, cmpK M pr NB NM EM i = true) :
    ∀ E : Subgroup G, E ≤ R → (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) → (∀ x ∈ E, x * x = 1) →
      Nat.card E = 16 → ∃ e ∈ EM, ∀ x ∈ E, x ≠ 1 → ∃ k < M, elt k = x ∧ e.testBit k = true := by
  classical
  intro E hER hcomm hsq hcard
  obtain ⟨P, hP⟩ : ∃ P : List G → ℕ → Prop,
      ∀ A k, P A k ↔ k < M ∧ elt k ∈ E ∧ elt k ≠ 1 ∧ elt k ∉ A := ⟨_, fun _ _ => Iff.rfl⟩
  have hex : ∀ A : List G, A.length < 15 → ∃ k, P A k := by
    intro A hA
    obtain ⟨x, hx, hx1, hxA⟩ := exists_not_mem hcard hA
    obtain ⟨k, hk, rfl⟩ := hlist x (hER hx) (hsq x hx) hx1
    exact ⟨k, (hP _ _).2 ⟨hk, hx, hx1, hxA⟩⟩
  have hmono : ∀ A A' : List G, (∀ a ∈ A, a ∈ A') → ∀ k, P A' k → P A k := by
    intro A A' hAA k hk
    obtain ⟨a, b, c, d⟩ := (hP _ _).1 hk
    exact (hP _ _).2 ⟨a, b, c, fun hm => d (hAA _ hm)⟩
  have step : ∀ L : List ℕ, (∀ x ∈ L, x < M ∧ elt x ∈ E) → (L.map elt).Nodup →
      (∀ a ∈ L.map elt, a ∈ E ∧ a ≠ 1) →
      (∀ a ∈ L.map elt, ∀ a' ∈ L.map elt, a ≠ a' → a * a' ∈ L.map elt) →
      ∀ i, P (L.map elt) i →
      (∀ x ∈ extS pr L i, x < M ∧ elt x ∈ E) ∧ ((extS pr L i).map elt).Nodup ∧
        (∀ a ∈ (extS pr L i).map elt, a ∈ E ∧ a ≠ 1) ∧
        (∀ a ∈ (extS pr L i).map elt, ∀ a' ∈ (extS pr L i).map elt, a ≠ a' →
          a * a' ∈ (extS pr L i).map elt) ∧
        ((extS pr L i).map elt).length = 2 * (L.map elt).length + 1 := by
    intro L hL hnd hA hcl i hi
    obtain ⟨hiM, hiE, hi1, hiA⟩ := (hP _ _).1 hi
    obtain ⟨h1, h2⟩ := extS_map hcomm hpr hL hiM hiE hiA
    rw [h2]
    obtain ⟨s1, s2, s3⟩ := span_step hcomm hsq hnd hA hcl hiE hi1 hiA
    refine ⟨h1, s1, s2, s3, ?_⟩
    simp only [List.length_append, List.length_cons, List.length_map]
    omega
  have hsub : ∀ (L : List ℕ) (i : ℕ), (∀ a ∈ L.map elt, a ∈ (extS pr L i).map elt) ∧
      elt i ∈ (extS pr L i).map elt := fun L i =>
    ⟨fun a ha => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ha
      exact List.mem_map_of_mem (List.mem_append_left _ hx),
     List.mem_map_of_mem (List.mem_append_right _ List.mem_cons_self)⟩
  have hex1 := hex [] (by simp)
  have hP1 : P [] (Nat.find hex1) := Nat.find_spec hex1
  set i1 := Nat.find hex1 with hi1d
  obtain ⟨a1, b1, c1, d1, l1⟩ := step [] (by simp) List.nodup_nil (by simp) (by simp) i1
    (by rw [List.map_nil]; exact hP1)
  set L1 := extS pr [] i1
  have hex2 := hex (L1.map elt) (by rw [l1]; simp)
  have hP2 : P (L1.map elt) (Nat.find hex2) := Nat.find_spec hex2
  set i2 := Nat.find hex2 with hi2d
  obtain ⟨a2, b2, c2, d2, l2⟩ := step L1 a1 b1 c1 d1 i2 hP2
  set L2 := extS pr L1 i2
  have hex3 := hex (L2.map elt) (by rw [l2, l1]; simp)
  have hP3 : P (L2.map elt) (Nat.find hex3) := Nat.find_spec hex3
  set i3 := Nat.find hex3 with hi3d
  obtain ⟨a3, b3, c3, d3, l3⟩ := step L2 a2 b2 c2 d2 i3 hP3
  set L3 := extS pr L2 i3
  have hex4 := hex (L3.map elt) (by rw [l3, l2, l1]; simp)
  have hP4 : P (L3.map elt) (Nat.find hex4) := Nat.find_spec hex4
  set i4 := Nat.find hex4 with hi4d
  obtain ⟨a4, b4, c4, -, l4⟩ := step L3 a3 b3 c3 d3 i4 hP4
  have hl4 : ((extS pr L3 i4).map elt).length = 15 := by rw [l4, l3, l2, l1]; simp
  have q1 := (hP _ _).1 hP1
  have q2 := (hP _ _).1 hP2
  have q3 := (hP _ _).1 hP3
  have q4 := (hP _ _).1 hP4
  have h12 : i1 < i2 := by
    have hle : i1 ≤ i2 := Nat.find_min' hex1 (hmono [] _ (by simp) _ hP2)
    have hne : i1 ≠ i2 := fun e => q2.2.2.2 (by rw [← e]; exact (hsub [] i1).2)
    omega
  have h23 : i2 < i3 := by
    have hle : i2 ≤ i3 := Nat.find_min' hex2 (hmono _ _ (hsub L1 i2).1 _ hP3)
    have hne : i2 ≠ i3 := fun e => q3.2.2.2 (by rw [← e]; exact (hsub L1 i2).2)
    omega
  have h34 : i3 < i4 := by
    have hle : i3 ≤ i4 := Nat.find_min' hex3 (hmono _ _ (hsub L2 i3).1 _ hP4)
    have hne : i3 ≠ i4 := fun e => q4.2.2.2 (by rw [← e]; exact (hsub L2 i3).2)
    omega
  have nb : ∀ i j, P [] i → P [] j → i < j → j ∈ NB i ∧ (NM i).testBit j = true := by
    intro i j hi hj hij
    obtain ⟨hiM, hiE, -⟩ := (hP _ _).1 hi
    obtain ⟨hjM, hjE, -⟩ := (hP _ _).1 hj
    have hm := hnbr i hiM j hjM (Nat.ne_of_lt hij) (hcomm _ hiE _ hjE)
    exact ⟨hm, hnm i hiM j hm⟩
  have p2 : P [] i2 := hmono _ _ (by simp) _ hP2
  have p3 : P [] i3 := hmono _ _ (by simp) _ hP3
  have p4 : P [] i4 := hmono _ _ (by simp) _ hP4
  have hc := h i1 q1.1
  unfold cmpK at hc
  rw [List.all_eq_true] at hc
  have hc2 := hc i2 (nb _ _ hP1 p2 h12).1
  simp only [h12, decide_true, Bool.not_true, Bool.false_or, List.all_eq_true] at hc2
  have hc3 := hc2 i3 (nb _ _ p2 p3 h23).1
  simp only [h23, (nb _ _ hP1 p3 (h12.trans h23)).2, decide_true, Bool.and_self, Bool.not_true,
    Bool.false_or, List.all_eq_true] at hc3
  have hspan := hc3 i4 (nb _ _ p3 p4 h34).1
  simp only [h34, (nb _ _ hP1 p4 (h12.trans (h23.trans h34))).2,
    (nb _ _ p2 p4 (h23.trans h34)).2, decide_true, Bool.and_self, Bool.not_true,
    Bool.false_or] at hspan
  have e : spanL pr i1 i2 i3 i4 = extS pr L3 i4 := rfl
  have hall : ((extS pr L3 i4).all fun x => decide (x < M)) = true :=
    List.all_eq_true.2 fun x hx => decide_eq_true (a4 x hx).1
  have hndk : ndK (extS pr L3 i4) 0 = true :=
    ndK_of_nodup _ 0 (List.Nodup.of_map elt b4) (fun _ _ => Nat.zero_testBit _)
  unfold spanK at hspan
  rw [e, hall, hndk] at hspan
  simp only [Bool.and_self, Bool.not_true, Bool.false_or, List.any_eq_true] at hspan
  obtain ⟨m, hm, hall'⟩ := hspan
  refine ⟨m, hm, fun x hx hx1 => ?_⟩
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 (mem_of_length hcard b4 c4 hl4 x hx hx1)
  exact ⟨k, (a4 k hk).1, rfl, List.all_eq_true.1 hall' k hk⟩

end CFSG.KC.Kc3K

end
