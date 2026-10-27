module

public import Certificates.Data.Kernel.SmithEKX
public import CFSG.Certificates.Kernel.SmithEK.MSound
public import CFSG.Certificates.Kernel.SmithEK.OSound

public section

namespace CFSG.SmithE.K

open CFSG.KC.Misc.O73

theorem ixAll_iff (n : Nat) (p : Nat → Bool) : ixAll n p = true ↔ ∀ k < n, p k = true :=
  recAll_iff p n

theorem ixBit_eq (c r : Nat) : ixBit c r = c.testBit r := by
  change Nat.beq ((c >>> r) &&& 1) 1 = _
  rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (c / 2 ^ r) with h | h <;> rw [h] <;> rfl

theorem ixGet_eq : ∀ (D : List Nat) (k : Nat), ixGet D k = D.getD k 0
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | x :: D, k + 1 => by
    change ixGet D k = _
    rw [ixGet_eq D k]
    rfl

theorem recAllRev_iff (p : Nat → Bool) (m : Nat) : ∀ n : Nat,
    Nat.rec (motive := fun _ => Bool) true (fun k acc => p (m - k) && acc) n = true ↔
      ∀ k < n, p (m - k) = true
  | 0 => ⟨fun _ k hk => absurd hk (Nat.not_lt_zero k), fun _ => rfl⟩
  | n + 1 => by
    change (p (m - n) && Nat.rec (motive := fun _ => Bool) true
      (fun k acc => p (m - k) && acc) n) = true ↔ _
    rw [Bool.and_eq_true, recAllRev_iff p m n]
    constructor
    · rintro ⟨h1, h2⟩ k hk
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
      · exact h2 k hk
      · exact h1
    · intro h
      exact ⟨h n (by omega), fun k hk => h k (by omega)⟩

theorem ixComm_iff (s t : Nat) :
    ixComm s t = true ↔ ∀ k < 21, at' 5 s (at' 5 t k) = at' 5 t (at' 5 s k) := by
  have e := recAllRev_iff (fun k => Nat.beq (at' 5 s (at' 5 t k)) (at' 5 t (at' 5 s k))) 20 21
  change Nat.rec (motive := fun _ => Bool) true (fun k acc =>
    Nat.beq (at' 5 s (at' 5 t (20 - k))) (at' 5 t (at' 5 s (20 - k))) && acc) 21 = true ↔ _
  rw [e]
  constructor
  · intro h k hk
    have := h (20 - k) (by omega)
    rw [show 20 - (20 - k) = k by omega] at this
    exact Nat.eq_of_beq_eq_true this
  · intro h k hk
    rw [h (20 - k) (by omega)]
    exact Nat.beq_refl _

@[expose] noncomputable def ixAmatN (CP s a : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun j acc => Nat.xor acc (bif a.testBit j then at' 9 CP (at' 5 s j) else 0))

theorem ixPlane_testBit (j a : Nat) (ha : a < 512) : (ixPlane j).testBit a = a.testBit j := by
  have key : ∀ n, (Nat.rec (motive := fun _ => Nat) 0
      (fun b acc => Nat.lor acc (bif ixBit b j then Nat.shiftLeft 1 b else 0)) n).testBit a =
      (decide (a < n) && a.testBit j) := by
    intro n
    induction n with
    | zero =>
      change (0 : Nat).testBit a = (decide (a < 0) && a.testBit j)
      simp
    | succ n ih =>
      change ((Nat.rec (motive := fun _ => Nat) 0
        (fun b acc => Nat.lor acc (bif ixBit b j then Nat.shiftLeft 1 b else 0)) n) |||
        (bif ixBit n j then Nat.shiftLeft 1 n else 0)).testBit a = _
      rw [Nat.testBit_or, ih, ixBit_eq]
      by_cases han : a = n
      · subst han
        cases h : a.testBit j <;> simp [h, Nat.one_shiftLeft, Nat.testBit_two_pow]
      · have hne : (bif n.testBit j then Nat.shiftLeft 1 n else 0).testBit a = false := by
          cases n.testBit j
          · simp
          · change (1 <<< n).testBit a = false
            rw [Nat.one_shiftLeft, Nat.testBit_two_pow]
            exact decide_eq_false (Ne.symm han)
        rw [hne, Bool.or_false]
        by_cases hlt : a < n
        · simp [hlt, show a < n + 1 by omega]
        · simp [hlt, show ¬ a < n + 1 by omega]
  exact (key 512).trans (by simp [ha])

theorem ixOutN_testBit (CP s r a : Nat) (ha : a < 512) : ∀ n,
    (Nat.rec (motive := fun _ => Nat) 0
      (fun j acc => Nat.xor acc (bif ixBit (at' 9 CP (at' 5 s j)) r then ixPlane j else 0))
      n).testBit a = (ixAmatN CP s a n).testBit r
  | 0 => by
    change (0 : Nat).testBit a = (0 : Nat).testBit r
    simp
  | n + 1 => by
    change ((Nat.rec (motive := fun _ => Nat) 0
      (fun j acc => Nat.xor acc (bif ixBit (at' 9 CP (at' 5 s j)) r then ixPlane j else 0)) n) ^^^
      (bif ixBit (at' 9 CP (at' 5 s n)) r then ixPlane n else 0)).testBit a =
      ((ixAmatN CP s a n) ^^^ (bif a.testBit n then at' 9 CP (at' 5 s n) else 0)).testBit r
    rw [Nat.testBit_xor, Nat.testBit_xor, ixOutN_testBit CP s r a ha n, ixBit_eq]
    cases h1 : (at' 9 CP (at' 5 s n)).testBit r <;> cases h2 : a.testBit n <;>
      simp [ixPlane_testBit n a ha, h1, h2]

set_option exponentiation.threshold 600 in
theorem ixFix_testBit {CP s a : Nat} (hc : ∀ j < 9, at' 9 CP (at' 5 s j) < 512) (ha : a < 512) :
    (ixFix CP s).testBit a = decide (ixAmatN CP s a 9 = a) := by
  have hlt : ∀ n ≤ 9, ixAmatN CP s a n < 512 := by
    intro n hn
    induction n with
    | zero =>
      change (0 : Nat) < 512
      decide
    | succ n ih =>
      change (ixAmatN CP s a n) ^^^ (bif a.testBit n then at' 9 CP (at' 5 s n) else 0) < 2 ^ 9
      refine Nat.xor_lt_two_pow (n := 9) (ih (by omega)) ?_
      cases a.testBit n
      · simp
      · exact hc n (by omega)
  have hor : (Nat.rec (motive := fun _ => Nat) 0
      (fun r acc => Nat.lor acc (Nat.xor (ixPlane r) (ixOut CP s r))) 9).testBit a = true ↔
      ∃ r < 9, a.testBit r ≠ (ixAmatN CP s a 9).testBit r := by
    have key : ∀ n, (Nat.rec (motive := fun _ => Nat) 0
        (fun r acc => Nat.lor acc (Nat.xor (ixPlane r) (ixOut CP s r))) n).testBit a = true ↔
        ∃ r < n, (Nat.xor (ixPlane r) (ixOut CP s r)).testBit a = true := by
      intro n
      induction n with
      | zero =>
        change (0 : Nat).testBit a = true ↔ _
        simp
      | succ n ih =>
        change ((Nat.rec (motive := fun _ => Nat) 0
          (fun r acc => Nat.lor acc (Nat.xor (ixPlane r) (ixOut CP s r))) n) |||
          (Nat.xor (ixPlane n) (ixOut CP s n))).testBit a = true ↔ _
        rw [Nat.testBit_or, Bool.or_eq_true, ih]
        constructor
        · rintro (⟨r, hr, h⟩ | h)
          · exact ⟨r, by omega, h⟩
          · exact ⟨n, by omega, h⟩
        · rintro ⟨r, hr, h⟩
          rcases Nat.lt_succ_iff_lt_or_eq.1 hr with hr | rfl
          · exact Or.inl ⟨r, hr, h⟩
          · exact Or.inr h
    rw [key]
    refine exists_congr fun r => and_congr_right fun _ => ?_
    change ((ixPlane r) ^^^ (ixOut CP s r)).testBit a = true ↔ _
    rw [Nat.testBit_xor, ixPlane_testBit r a ha]
    change (a.testBit r ^^ (Nat.rec (motive := fun _ => Nat) 0 (fun j acc => Nat.xor acc
      (bif ixBit (at' 9 CP (at' 5 s j)) r then ixPlane j else 0)) 9).testBit a) = true ↔ _
    rw [ixOutN_testBit CP s r a ha 9]
    cases a.testBit r <;> cases (ixAmatN CP s a 9).testBit r <;> simp
  change (((1 <<< 512) - 1) ^^^ (Nat.rec (motive := fun _ => Nat) 0
    (fun r acc => Nat.lor acc (Nat.xor (ixPlane r) (ixOut CP s r))) 9)).testBit a = _
  rw [Nat.testBit_xor, Nat.one_shiftLeft, Nat.testBit_two_pow_sub_one, decide_eq_true ha, Bool.true_xor]
  apply Bool.eq_iff_iff.2
  rw [Bool.not_eq_true', ← Bool.not_eq_true, hor, decide_eq_true_iff]
  constructor
  · intro h
    refine Nat.eq_of_testBit_eq fun r => ?_
    by_cases hr : r < 9
    · exact Classical.byContradiction fun hne => h ⟨r, hr, Ne.symm hne⟩
    · have h9 : 2 ^ 9 ≤ 2 ^ r := Nat.pow_le_pow_right (by decide) (by omega)
      rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (hlt 9 (Nat.le_refl 9)) h9),
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le ha h9)]
  · rintro h ⟨r, -, hr⟩
    exact hr (by rw [h])

theorem cntB_mono {n m : Nat} (h : n ≤ m) (x : Nat) : cntB n x ≤ cntB m x := by
  unfold cntB
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [List.range_add, List.countP_append]
  omega

theorem cntK_of_le {n : Nat} : ∀ (f x : Nat), x < 2 ^ n → f ≤ cntB n x → cntK f x = f
  | 0, _, _, _ => rfl
  | f + 1, x, hn, h => by
    rw [cntK_succ]
    have hx : x ≠ 0 := by
      rintro rfl
      unfold cntB at h
      simp at h
    have hlt : x &&& (x - 1) < 2 ^ n := Nat.lt_of_le_of_lt Nat.and_le_left hn
    rw [cntB_land_pred hx hn] at h
    rw [show (x == 0) = false from beq_eq_false_iff_ne.2 hx, cond_false,
      cntK_of_le f _ hlt (by omega)]

theorem cntB_le_of_cntK {m x : Nat} (h : Nat.ble (cntK (m + 1) x) m = true) (n : Nat) :
    cntB n x ≤ m := by
  have hle := Nat.le_of_ble_eq_true h
  have hx : x < 2 ^ (max n x) :=
    Nat.lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by decide) (Nat.le_max_right _ _))
  refine Nat.le_trans (cntB_mono (Nat.le_max_left n x) x) ?_
  refine Classical.byContradiction fun hc => ?_
  rw [cntK_of_le (m + 1) x hx (by omega)] at hle
  omega

theorem ixRow_spec {i e : Nat} : ∀ (D : List Nat) (j0 : Nat),
    List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
      (fun d _ ih j =>
        (bif ixComm (ixS e) (ixS d) then
            ixBit (ixC e) j && (Nat.beq i j ||
              (Nat.ble (cntK 17 (Nat.land (ixF e) (ixF d))) 16 &&
                Nat.ble (cntK 28 (Nat.land (ixC e) (ixC d))) 27))
          else !ixBit (ixC e) j) && ih (Nat.succ j)) D j0 = true →
    ∀ j < D.length,
      (bif ixComm (ixS e) (ixS (D.getD j 0)) then
          ixBit (ixC e) (j0 + j) && (Nat.beq i (j0 + j) ||
            (Nat.ble (cntK 17 (Nat.land (ixF e) (ixF (D.getD j 0)))) 16 &&
              Nat.ble (cntK 28 (Nat.land (ixC e) (ixC (D.getD j 0)))) 27))
        else !ixBit (ixC e) (j0 + j)) = true
  | [], _, _, j, hj => absurd hj (by simp)
  | d :: D, j0, h, j, hj => by
    rw [Bool.and_eq_true] at h
    cases j with
    | zero => simpa using h.1
    | succ j =>
      have := ixRow_spec D (j0 + 1) h.2 j (by simpa using hj)
      rw [show j0 + (j + 1) = j0 + 1 + j by omega]
      simpa using this

theorem ixChunk_spec {CP a n : Nat} {D : List Nat} (h : ixChunk CP D a n = true) {k : Nat}
    (hk : k < n) :
    ixF (D.getD (a + k) 0) = ixFix CP (ixS (D.getD (a + k) 0)) ∧
      Nat.ble (cntK 65 (ixF (D.getD (a + k) 0))) 64 = true ∧
      ixRow (a + k) (D.getD (a + k) 0) D = true := by
  unfold ixChunk at h
  have h' := (recAll_iff _ n).1 h k hk
  simp only [ixGet_eq, Bool.and_eq_true] at h'
  obtain ⟨⟨h1, h2⟩, h3⟩ := h'
  exact ⟨Nat.eq_of_beq_eq_true h1, h2, h3⟩

end CFSG.SmithE.K
