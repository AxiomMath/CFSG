module

public import Certificates.Data.Kernel.WordsS
public import CFSG.Certificates.Kernel.Spor.Mat3Sound
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaWordSound

public section

namespace CFSG.KS.WordsS

open CFSG.KC.WordsS CFSG.KC.Ord CFSG.KS.Mat3 CFSG.AGLEmbedding.R3

theorem strictL_eq (y : Nat) (k : Nat → List Nat) : strictL y k = k y := by
  cases y <;> rfl

theorem cond_lt (b : Bool) : cond b 1 0 < 2 ^ 1 := by
  cases b <;> decide

theorem plane3_cons (r x : Nat) (xs : List Nat) :
    plane3 r (x :: xs) = 2 ^ 1 * plane3 r xs + cond (Nat.beq (x % 3) r) 1 0 := by
  rw [plane3]
  change cond (Nat.beq (x % 3) r) 1 0 + plane3 r xs <<< 1 = _
  rw [Nat.shiftLeft_eq, Nat.add_comm, Nat.mul_comm]

theorem plane3_testBit (r : Nat) :
    ∀ (A : List Nat) (u : Nat),
      (plane3 r A).testBit u = (decide (u < A.length) && Nat.beq (A.getD u 0 % 3) r)
  | [], u => by simp [plane3]
  | x :: xs, u => by
    rw [plane3_cons, Nat.testBit_two_pow_mul_add _ (cond_lt _)]
    rcases u with _ | u
    · have h0 : 0 < (x :: xs).length := by simp
      rw [if_pos (by omega), List.getD_cons_zero, decide_eq_true h0, Bool.true_and]
      cases Nat.beq (x % 3) r <;> rfl
    · rw [if_neg (by omega), Nat.add_sub_cancel, plane3_testBit r xs u]
      simp only [List.getD_cons_succ, List.length_cons, Nat.add_lt_add_iff_right]

theorem plane3_lt (r : Nat) (A : List Nat) : plane3 r A < 2 ^ A.length :=
  Nat.lt_pow_two_of_testBit _ fun u hu => by
    rw [plane3_testBit]
    simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
    exact Or.inl (by omega)

theorem pk3_testBit {N : Nat} {A : List Nat} (hA : A.length ≤ N) (u : Nat) :
    (pk3 N A).testBit u = if u < N then (plane3 1 A).testBit u else (plane3 2 A).testBit (u - N) := by
  have h1 : plane3 1 A < 2 ^ N :=
    Nat.lt_of_lt_of_le (plane3_lt 1 A) (Nat.pow_le_pow_right (by omega) hA)
  have e : pk3 N A = 2 ^ N * plane3 2 A + plane3 1 A := by
    change plane3 1 A + plane3 2 A <<< N = _
    rw [Nat.shiftLeft_eq, Nat.add_comm, Nat.mul_comm]
  rw [e, Nat.testBit_two_pow_mul_add _ h1]

theorem bv_mod (x : Nat) : bv (Nat.beq (x % 3) 1) (Nat.beq (x % 3) 2) = (x : ZMod 3) := by
  rw [← ZMod.natCast_mod x 3]
  have h : x % 3 < 3 := Nat.mod_lt _ (by norm_num)
  generalize x % 3 = y at h ⊢
  rcases (by omega : y = 0 ∨ y = 1 ∨ y = 2) with rfl | rfl | rfl <;> decide

theorem pk3_sound {d N : Nat} (hN : N = d * d) {A : List Nat} (hA : A.length ≤ N) :
    Canon3 N (pk3 N A) ∧ mat3 d N (pk3 N A) = toMatL 3 d A := by
  have hb := pk3_testBit hA
  refine ⟨⟨?_, fun t ht => ?_⟩, ?_⟩
  · have e : pk3 N A = 2 ^ N * plane3 2 A + plane3 1 A := by
      change plane3 1 A + plane3 2 A <<< N = _
      rw [Nat.shiftLeft_eq, Nat.add_comm, Nat.mul_comm]
    have h1 : plane3 1 A < 2 ^ N :=
      Nat.lt_of_lt_of_le (plane3_lt 1 A) (Nat.pow_le_pow_right (by omega) hA)
    have h2 : plane3 2 A < 2 ^ N :=
      Nat.lt_of_lt_of_le (plane3_lt 2 A) (Nat.pow_le_pow_right (by omega) hA)
    rw [e, Nat.pow_add]
    have := Nat.mul_le_mul_left (2 ^ N) (Nat.succ_le_of_lt h2)
    rw [Nat.mul_succ] at this
    omega
  · rw [hb, if_neg (by omega), Nat.add_sub_cancel_left, plane3_testBit]
    rw [hb] at ht
    by_cases htN : t < N
    · rw [if_pos htN, plane3_testBit] at ht
      simp only [Bool.and_eq_true, decide_eq_true_eq, Nat.beq_eq_true_eq] at ht
      simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
      right
      cases h : (A.getD t 0 % 3).beq 2
      · rfl
      · have h1 := Nat.eq_of_beq_eq_true h
        have h2 := Nat.eq_of_beq_eq_true ht.2
        omega
    · simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
      exact Or.inl (by omega)
  · funext i j
    have hidx : d * i.val + j.val < N := hN ▸ idx_lt3 i.isLt j.isLt
    unfold mat3 toMatL
    rw [hb, hb, if_pos hidx, if_neg (by omega), Nat.add_sub_cancel_left, plane3_testBit,
      plane3_testBit]
    by_cases hl : d * i.val + j.val < A.length
    · rw [decide_eq_true hl, Bool.true_and, Bool.true_and, bv_mod]
    · rw [decide_eq_false hl, Bool.false_and, Bool.false_and, List.getD_eq_default _ _ (by omega)]
      simp [bv]

@[expose] def Rel3 (d N : Nat) (M : List Nat) (X : Nat) : Prop :=
  Canon3 N X ∧ mat3 d N X = toMatL 3 d M

theorem step3_cons (d N LO CI RM A A2 X : Nat) (Xs : List Nat) :
    step3 d N LO CI RM A A2 (X :: Xs) =
      X :: mul3s d N LO CI RM A X :: mul3s d N LO CI RM A2 X :: step3 d N LO CI RM A A2 Xs := by
  change strictL X (fun x => strictL (mul3s d N LO CI RM A x) fun y =>
    strictL (mul3s d N LO CI RM A2 x) fun z => x :: y :: z :: step3 d N LO CI RM A A2 Xs) = _
  rw [strictL_eq, strictL_eq, strictL_eq]

theorem forall₂_step3 {d f N LO RM CI ONE UP : Nat} (hc : consts3OK d f N LO RM CI ONE UP = true)
    {A : List Nat} {PA PA2 : Nat} (hA : Rel3 d N A PA)
    (hA2 : Canon3 N PA2 ∧ mat3 d N PA2 = toMatL 3 d A * toMatL 3 d A) :
    ∀ {Ms : List (List Nat)} {Xs : List Nat}, List.Forall₂ (Rel3 d N) Ms Xs →
      List.Forall₂ (Rel3 d N)
        (Ms.flatMap fun M => (List.range 3).map fun a => mmulL 3 d (mpowL 3 d A a) M)
        (step3 d N LO CI RM PA PA2 Xs)
  | [], [], List.Forall₂.nil => by
    change List.Forall₂ _ [] []
    exact List.Forall₂.nil
  | M :: Ms, X :: Xs, List.Forall₂.cons hMX hrest => by
    rw [List.flatMap_cons, step3_cons]
    have e3 : (List.range 3).map (fun a => mmulL 3 d (mpowL 3 d A a) M) =
        [mmulL 3 d (mpowL 3 d A 0) M, mmulL 3 d (mpowL 3 d A 1) M,
          mmulL 3 d (mpowL 3 d A 2) M] := rfl
    rw [e3, List.cons_append, List.cons_append, List.cons_append, List.nil_append]
    obtain ⟨hX, hXm⟩ := hMX
    have h1 := mul3s_sound hc hA.1 hX
    have h2 := mul3s_sound hc hA2.1 hX
    refine List.Forall₂.cons ⟨hX, ?_⟩ (List.Forall₂.cons ⟨h1.1, ?_⟩
      (List.Forall₂.cons ⟨h2.1, ?_⟩ (forall₂_step3 hc hA hA2 hrest)))
    · rw [toMatL_mmulL, toMatL_mpowL, pow_zero, one_mul, hXm]
    · rw [h1.2, toMatL_mmulL, toMatL_mpowL, pow_one, hA.2, hXm]
    · rw [h2.2, toMatL_mmulL, toMatL_mpowL, pow_two, hA2.2, hXm]

theorem wordsS_cons (d N LO CI RM ONE A : Nat) (As : List Nat) :
    wordsS d N LO CI RM ONE (A :: As) =
      step3 d N LO CI RM A (mul3s d N LO CI RM A A) (wordsS d N LO CI RM ONE As) := by
  change strictL A (fun a => strictL (mul3s d N LO CI RM a a) fun a2 =>
    step3 d N LO CI RM a a2 (wordsS d N LO CI RM ONE As)) = _
  rw [strictL_eq, strictL_eq]

theorem forall₂_wordsS {d f N LO RM CI ONE UP : Nat} (hc : consts3OK d f N LO RM CI ONE UP = true) :
    ∀ (As : List (List Nat)), (∀ A ∈ As, A.length ≤ N) →
      List.Forall₂ (Rel3 d N) (wordsL 3 d As) (wordsS d N LO CI RM ONE (As.map (pk3 N)))
  | [], _ => by
    have h := one3_sound hc
    refine List.Forall₂.cons ⟨h.1, ?_⟩ List.Forall₂.nil
    rw [h.2, toMatL_midL]
  | A :: As, hA => by
    have hN := (consts3_facts hc).2.1
    have hPA := pk3_sound hN (hA A List.mem_cons_self)
    have hPA2 := mul3s_sound hc hPA.1 hPA.1
    rw [List.map_cons, wordsS_cons, wordsL]
    exact forall₂_step3 hc hPA ⟨hPA2.1, by rw [hPA2.2, hPA.2]⟩
      (forall₂_wordsS hc As fun B hB => hA B (List.mem_cons_of_mem _ hB))

theorem foldl_code (p : Nat) : ∀ (A : List Nat) (acc : Nat),
    A.foldl (fun a x => a * p + x) acc = acc * p ^ A.length + A.foldl (fun a x => a * p + x) 0
  | [], acc => by simp
  | x :: A, acc => by
    rw [List.foldl_cons, List.foldl_cons, foldl_code p A (acc * p + x), foldl_code p A (0 * p + x),
      List.length_cons, pow_succ]
    ring

theorem foldl_code_lt (p : Nat) : ∀ (A : List Nat), (∀ x ∈ A, x < p) →
    A.foldl (fun a x => a * p + x) 0 < p ^ A.length
  | [], _ => by simp
  | x :: A, hA => by
    rw [List.foldl_cons, foldl_code, List.length_cons, pow_succ]
    have h1 := foldl_code_lt p A fun y hy => hA y (List.mem_cons_of_mem _ hy)
    have h2 : x + 1 ≤ p := hA x List.mem_cons_self
    have := Nat.mul_le_mul_right (p ^ A.length) h2
    rw [Nat.add_mul, Nat.one_mul] at this
    nlinarith

theorem div_mod_aux {x y a b q : Nat} (ha : a < q) (hb : b < q) (h : x * q + a = y * q + b) :
    x = y ∧ a = b := by
  rcases lt_trichotomy x y with hxy | rfl | hxy
  · have : (x + 1) * q ≤ y * q := Nat.mul_le_mul_right q hxy
    nlinarith
  · exact ⟨rfl, by omega⟩
  · have : (y + 1) * q ≤ x * q := Nat.mul_le_mul_right q hxy
    nlinarith

theorem codeL_inj (p : Nat) : ∀ (A B : List Nat), A.length = B.length → (∀ x ∈ A, x < p) →
    (∀ x ∈ B, x < p) → codeL p A = codeL p B → A = B
  | [], [], _, _, _, _ => rfl
  | x :: A, y :: B, hl, hA, hB, h => by
    have hl' : A.length = B.length := by simpa using hl
    unfold codeL at h
    rw [List.foldl_cons, List.foldl_cons, foldl_code, foldl_code p B, ← hl'] at h
    have hcA := foldl_code_lt p A fun z hz => hA z (List.mem_cons_of_mem _ hz)
    have hcB := foldl_code_lt p B fun z hz => hB z (List.mem_cons_of_mem _ hz)
    rw [← hl'] at hcB
    simp only [Nat.zero_mul, Nat.zero_add] at h
    obtain ⟨rfl, hc⟩ := div_mod_aux hcA hcB h
    rw [codeL_inj p A B hl' (fun z hz => hA z (List.mem_cons_of_mem _ hz))
      (fun z hz => hB z (List.mem_cons_of_mem _ hz)) hc]

theorem exists_of_forall₂ {α β : Type} {R : α → β → Prop} :
    ∀ {l1 : List α} {l2 : List β}, List.Forall₂ R l1 l2 → ∀ a ∈ l1, ∃ b ∈ l2, R a b
  | [], [], List.Forall₂.nil, _, ha => by simp at ha
  | a :: l1, b :: l2, List.Forall₂.cons hab hr, a', ha' => by
    rcases List.mem_cons.1 ha' with rfl | ha'
    · exact ⟨b, List.mem_cons_self, hab⟩
    · obtain ⟨b', hb', h⟩ := exists_of_forall₂ hr a' ha'
      exact ⟨b', List.mem_cons_of_mem _ hb', h⟩

theorem nodup_of_forall₂ {α β : Type} {R : α → β → Prop}
    (hR : ∀ a b b', R a b → R a b' → b = b') :
    ∀ {l1 : List α} {l2 : List β}, List.Forall₂ R l1 l2 → l2.Nodup → l1.Nodup
  | [], [], List.Forall₂.nil, _ => List.nodup_nil
  | a :: l1, b :: l2, List.Forall₂.cons hab hr, hnd => by
    rw [List.nodup_cons] at hnd ⊢
    refine ⟨fun ha => ?_, nodup_of_forall₂ hR hr hnd.2⟩
    obtain ⟨b', hb', hab'⟩ := exists_of_forall₂ hr a ha
    exact hnd.1 (hR a b' b hab' hab ▸ hb')

theorem nodup_codes_of_wordsS {d f N LO RM CI ONE UP : Nat} {key : Nat → Nat}
    {As : List (List Nat)} (h : wNodupS d f N LO RM CI ONE UP key As = true) :
    ((wordsL 3 d As).map (codeL 3)).Nodup := by
  unfold wNodupS at h
  simp only [Bool.and_eq_true, List.all_eq_true, Nat.ble_eq] at h
  obtain ⟨⟨hc, hlen⟩, hb⟩ := h
  have hN := (consts3_facts hc).2.1
  have hF := forall₂_wordsS hc As hlen
  have hspec := wordsL_spec 3 d (by norm_num) As
  have hS := CFSG.Decide.nodup_of_bitsetNodup key hb
  have hnd := nodup_of_forall₂ (fun M X Y hX hY => mat3_inj hN hX.1 hY.1 (hX.2.trans hY.2.symm))
    hF hS
  refine hnd.map_on fun A hA B hB hAB => ?_
  exact codeL_inj 3 A B ((hspec A hA).1.trans (hspec B hB).1.symm) (hspec A hA).2 (hspec B hB).2 hAB

theorem length_wordsL (p n : Nat) : ∀ As : List (List Nat), (wordsL p n As).length = p ^ As.length
  | [] => by simp [wordsL]
  | A :: As => by
    rw [wordsL, List.length_flatMap, List.length_cons, pow_succ, ← length_wordsL p n As]
    simp

end CFSG.KS.WordsS

end
