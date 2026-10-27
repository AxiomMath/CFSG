module

public import Certificates.Data.Kernel.U6.Dom
public import CFSG.Certificates.Kernel.U6SoundTables

public section

namespace CFSG.KC.U6

open CFSG.KLie.CT CFSG.Sporadic.Th.Native CFSG.Fischer.Native

@[expose] def rootFlagsG (nz pr : ℕ → ℕ) (pts : Array ℕ) (c : ℕ) : Flags :=
  Array.ofFn (n := 693) fun p =>
    let v := pts[p.val]!
    nz v == 2 || (nz v == 6 && pr v == c)

@[expose] def domOKG (nz pr : ℕ → ℕ) (k : ℕ) (pts pos : Array ℕ) : Bool :=
  let F := rootFlagsG nz pr pts k
  let T := tvTabsG pts pos
  (List.range 693).all fun q => F[q]! ||
    (List.range 693).any fun x => F[x]! && ap T[q]! x == x

namespace D3146

open CFSG.KC.Loop

theorem orB_iff' {a b : Bool} : CFSG.KLie.CT.orB a b = true ↔ a = true ∨ b = true := by
  cases a <;> simp [CFSG.KLie.CT.orB]

theorem andB_iff' {a b : Bool} : CFSG.KLie.CT.andB a b = true ↔ a = true ∧ b = true := by
  cases a <;> simp [CFSG.KLie.CT.andB]

theorem anyN_iff' {m : ℕ} {f : ℕ → Bool} : anyN m f = true ↔ ∃ i < m, f i = true := by
  induction m with
  | zero => exact ⟨fun h => absurd h Bool.false_ne_true, fun ⟨i, hi, _⟩ => absurd hi (Nat.not_lt_zero i)⟩
  | succ m ih =>
    change CFSG.KLie.CT.orB (f m) (anyN m f) = true ↔ _
    rw [orB_iff', ih]
    constructor
    · rintro (h | ⟨i, hi, h⟩)
      · exact ⟨m, Nat.lt_succ_self m, h⟩
      · exact ⟨i, Nat.lt_succ_of_lt hi, h⟩
    · rintro ⟨i, hi, h⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact Or.inr ⟨i, hi, h⟩
      · exact Or.inl h

@[expose] def rootC (nz pr : ℕ → ℕ) (c v : ℕ) : Bool := nz v == 2 || (nz v == 6 && pr v == c)

theorem rootC_eq (nz pr : ℕ → ℕ) (c v : ℕ) :
    CFSG.KLie.CT.orB (Nat.beq (nz v) (nat_lit 2)) (CFSG.KLie.CT.andB (Nat.beq (nz v) (nat_lit 6)) (Nat.beq (pr v) c)) = rootC nz pr c v := by
  apply Bool.eq_iff_iff.2
  rw [orB_iff', andB_iff', Nat.beq_eq, Nat.beq_eq, Nat.beq_eq]
  simp [rootC]

theorem testBit_mask (nz pr : ℕ → ℕ) (UP c : ℕ) : ∀ N p,
    (Nat.rec (motive := fun _ => ℕ) (nat_lit 0)
      (fun p acc => strictN acc fun acc => (fun v =>
        nIf(CFSG.KLie.CT.orB (Nat.beq (nz v) (nat_lit 2)) (CFSG.KLie.CT.andB (Nat.beq (nz v) (nat_lit 6)) (Nat.beq (pr v) c)),
          Nat.lor acc (pw2 p), acc)) (up UP p)) N : ℕ).testBit p =
      (decide (p < N) && rootC nz pr c (up UP p))
  | 0, p => by simp
  | N + 1, p => by
    change (strictN _ fun acc => _).testBit p = _
    rw [Snd.strictN_eq]
    dsimp only
    rw [rootC_eq]
    have ih := testBit_mask nz pr UP c N p
    cases hc : rootC nz pr c (up UP N)
    · change (Nat.rec (motive := fun _ => ℕ) 0 _ N : ℕ).testBit p = _
      rw [ih]
      by_cases hp : p = N
      · subst hp
        simp [hc]
      · by_cases hpN : p < N
        · simp [hpN, show p < N + 1 by omega]
        · simp [hpN, show ¬ p < N + 1 by omega]
    · change ((Nat.rec (motive := fun _ => ℕ) 0 _ N : ℕ) ||| 1 <<< N).testBit p = _
      rw [Nat.testBit_or, ih, Nat.one_shiftLeft, Nat.testBit_two_pow]
      by_cases hp : p = N
      · subst hp
        simp [hc]
      · by_cases hpN : p < N
        · simp [hpN, show p < N + 1 by omega, Ne.symm hp]
        · simp [hpN, show ¬ p < N + 1 by omega, Ne.symm hp]

theorem bit_testBit (X i : ℕ) : bit X i = X.testBit i := by
  change Nat.beq ((X >>> i) &&& 1) 1 = _
  rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (X / 2 ^ i) with h | h
  · rw [h]
    rfl
  · rw [h]
    rfl

theorem bit_mask {nz pr : ℕ → ℕ} {UP c p : ℕ} (hp : p < 693) :
    bit (rootMaskK nz pr UP c) p = rootC nz pr c (up UP p) := by
  rw [bit_testBit]
  have e := testBit_mask nz pr UP c 693 p
  have hp' : decide (p < 693) = true := decide_eq_true hp
  rw [hp', Bool.true_and] at e
  exact e

end D3146

open D3146 in
theorem sound3146 {UP POS POSN MVT : Nat} {R : Nat → Nat} {nz pr : ℕ → ℕ} {c : ℕ}
    {pts pos : Array ℕ} (hu : decA UP 12 693 = pts) (hp : decA POS 10 4096 = pos)
    (h : TabsOK UP POS POSN MVT R) (hk : check3146 nz pr UP R c = true) :
    domOKG nz pr c pts pos = true := by
  have ht := tables_sound hu hp h
  unfold check3146 at hk
  rw [Snd.strictB_eq] at hk
  have hd := Snd.allBelow_spec hk (by norm_num)
  have hF : ∀ p < 693, (rootFlagsG nz pr pts c)[p]! = bit (rootMaskK nz pr UP c) p := by
    intro p hp'
    rw [bit_mask hp', rootFlagsG, getElem!_pos _ p (by simpa using hp'), Array.getElem_ofFn]
    have hup : pts[p]! = up UP p := by rw [← hu, Snd.decA_get UP 12 693 p hp']; rfl
    simp only [hup, rootC]
  unfold domOKG
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, List.any_eq_true,
    Bool.and_eq_true, beq_iff_eq]
  intro q hq
  have h1 := hd q hq
  dsimp only at h1
  rw [orB_iff', Snd.strictB_eq, anyN_iff'] at h1
  rcases h1 with h1 | ⟨x, hx, h1⟩
  · exact Or.inl ((hF q hq).trans h1)
  · rw [andB_iff', Snd.beq_iff] at h1
    refine Or.inr ⟨x, hx, (hF x hx).trans h1.1, ?_⟩
    rw [(ht q hq).2.2 x hx, h1.2]

end CFSG.KC.U6

end
