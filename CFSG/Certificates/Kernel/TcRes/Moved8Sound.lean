module

public import CFSG.Certificates.Kernel.TcRes.TransSound
public import Certificates.Data.Kernel.TcRes.C2Moved
public import CFSG.Certificates.Kernel.TcRes.PlaneSound

public section

namespace CFSG.KC.TcRes

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.TcRes.TK

section Squash16

@[expose] def spread16 (b : ℕ) : ℕ :=
  Nat.add (Nat.mod b 2) (Nat.add (Nat.mul (Nat.mod (Nat.div b 2) 2) 65536)
    (Nat.add (Nat.mul (Nat.mod (Nat.div b 4) 2) 4294967296)
      (Nat.mul (Nat.mod (Nat.div b 8) 2) 281474976710656)))

theorem gather16B : allLt 16 (fun b => allLt 4 fun k =>
    Nat.beq (Nat.mod (Nat.div (Nat.land (Nat.shiftRight (Nat.mul (spread16 b) 281483566907400) 48)
      15) (Nat.pow 2 k)) 2) (Nat.mod (Nat.div (spread16 b) (Nat.pow 2 (Nat.mul 16 k))) 2)) = true := by
  decide +kernel

theorem spread16_eq : allLt 2 (fun f0 => allLt 2 fun f1 => allLt 2 fun f2 => allLt 2 fun f3 =>
    Nat.beq (spread16 (Nat.add f0 (Nat.add (Nat.mul 2 f1) (Nat.add (Nat.mul 4 f2) (Nat.mul 8 f3)))))
    (Nat.add f0 (Nat.add (Nat.mul 65536 f1) (Nat.add (Nat.mul 4294967296 f2)
      (Nat.mul 281474976710656 f3))))) = true := by
  decide +kernel

theorem gather16 {b k : ℕ} (hb : b < 16) (hk : k < 4) :
    (((spread16 b * 281483566907400) >>> 48) &&& 15).testBit k =
      (spread16 b).testBit (16 * k) := by
  have h := Lane.allLt_iff.1 (Lane.allLt_iff.1 gather16B b hb) k hk
  rw [Lane.beq_eq_true] at h
  simp only [Lane.nmod, Lane.ndiv, Lane.nland, Lane.nshr, Lane.nmul, Lane.npow] at h
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq, h]

theorem gather16_lt (y : ℕ) : ((y * 281483566907400) >>> 48) &&& 15 < 2 ^ 4 :=
  lt_of_le_of_lt Nat.and_le_right (by norm_num)

theorem testBit_gather16 {y : ℕ} (hy : y < 2 ^ 64) (hl : ∀ k < 4, fld y 16 k ≤ 1) {k : ℕ}
    (hk : k < 4) : (((y * 281483566907400) >>> 48) &&& 15).testBit k = y.testBit (16 * k) := by
  have e := Lane.eq_sum_lanes 16 4 y hy
  norm_num [Finset.sum_range_succ] at e
  have l0 := hl 0 (by norm_num)
  have l1 := hl 1 (by norm_num)
  have l2 := hl 2 (by norm_num)
  have l3 := hl 3 (by norm_num)
  have hs := Lane.allLt_iff.1 (Lane.allLt_iff.1 (Lane.allLt_iff.1 (Lane.allLt_iff.1 spread16_eq _
    (by omega : fld y 16 0 < 2)) _ (by omega : fld y 16 1 < 2)) _ (by omega : fld y 16 2 < 2))
    _ (by omega : fld y 16 3 < 2)
  rw [Lane.beq_eq_true] at hs
  have h := gather16 (b := Nat.add (fld y 16 0) (Nat.add (Nat.mul 2 (fld y 16 1))
    (Nat.add (Nat.mul 4 (fld y 16 2)) (Nat.mul 8 (fld y 16 3)))))
    (by simp only [Lane.nadd, Lane.nmul]; omega) hk
  have hS : Nat.add (fld y 16 0) (Nat.add (Nat.mul 65536 (fld y 16 1))
      (Nat.add (Nat.mul 4294967296 (fld y 16 2)) (Nat.mul 281474976710656 (fld y 16 3)))) = y := by
    simp only [Lane.nadd, Lane.nmul]
    omega
  rw [hs, hS] at h
  exact h

theorem squash16_rec {x : ℕ} (hl : ∀ k < 240, fld x 16 k ≤ 1) : ∀ n ≤ 60, ∀ j,
    (Nat.rec (motive := fun _ => ℕ) 0
      (fun i ih => strictN ih fun a => Nat.lor a (Nat.shiftLeft
        (Nat.land (Nat.shiftRight (Nat.mul (fld x 64 i) 281483566907400) 48) 15)
          (Nat.mul 4 i))) n).testBit j = (decide (j < 4 * n) && x.testBit (16 * j)) := by
  intro n
  induction n with
  | zero => intro _ j; simp
  | succ n ih =>
    intro hn j
    change (strictN (Nat.rec (motive := fun _ => ℕ) 0
      (fun i ih => strictN ih fun a => Nat.lor a (Nat.shiftLeft
        (Nat.land (Nat.shiftRight (Nat.mul (fld x 64 i) 281483566907400) 48) 15)
          (Nat.mul 4 i))) n) fun a => Nat.lor a (Nat.shiftLeft
        (Nat.land (Nat.shiftRight (Nat.mul (fld x 64 n) 281483566907400) 48) 15)
          (Nat.mul 4 n))).testBit j = _
    rw [Lane.strictN_eq, Lane.nlor, Nat.testBit_or, ih (by omega) j]
    simp only [Lane.nshl, Lane.nmul, Lane.nland, Lane.nshr]
    rw [Nat.testBit_shiftLeft]
    have hy : fld x 64 n < 2 ^ 64 := Lane.fld_lt _ _ _
    have hyl : ∀ k < 4, fld (fld x 64 n) 16 k ≤ 1 := fun k hk => by
      have e := Lane.fld_fld x 16 4 n k hk
      rw [show (16 * 4 : ℕ) = 64 from rfl] at e
      rw [e]
      exact hl _ (by omega)
    by_cases h1 : j < 4 * n
    · have : ¬ 4 * n ≤ j := by omega
      simp [h1, this, show j < 4 * (n + 1) by omega]
    · by_cases h2 : j < 4 * (n + 1)
      · have hk : j - 4 * n < 4 := by omega
        have hg := testBit_gather16 hy hyl hk
        have e2 := Lane.testBit_fld x 64 n (16 * (j - 4 * n))
        rw [decide_eq_true (by omega : 16 * (j - 4 * n) < 64), Bool.true_and] at e2
        have e3 : 64 * n + 16 * (j - 4 * n) = 16 * j := by omega
        rw [e3] at e2
        simp only [h1, decide_false, Bool.false_and, Bool.false_or, ge_iff_le,
          show 4 * n ≤ j by omega, decide_true, Bool.true_and]
        rw [hg, e2, decide_eq_true h2, Bool.true_and]
      · have hb : (((fld x 64 n * 281483566907400) >>> 48) &&& 15).testBit (j - 4 * n) = false :=
          Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (gather16_lt _)
            (Nat.pow_le_pow_right (by norm_num) (by omega)))
        simp [h1, h2, hb]

theorem testBit_squash16 {x : ℕ} (hl : ∀ k < 240, fld x 16 k ≤ 1) (j : ℕ) :
    (squash16 x).testBit j = (decide (j < 240) && x.testBit (16 * j)) :=
  squash16_rec hl 60 le_rfl j

end Squash16

section Tables

variable
  {vec : ℕ → Fin Tag.E8.rank → ℤ} {adj : ℕ → ℕ → Bool} {neg : ℕ → ℕ} {RTs : ℕ → ℕ}

theorem low16_testBit {d : ℕ} (hd : d < 240) : LOW16.testBit (16 * d) = true := by
  rw [low16_eq, testBit_lsum (fun _ _ => le_refl _)]
  exact ⟨hd, rfl⟩

theorem low16_fld (k : ℕ) : fld LOW16 16 k ≤ 1 := by
  change fld (lowW 16 240) 16 k ≤ 1
  rcases lt_or_ge k 240 with h | h
  · have := Lane.fld_mul_low (w := 16) (K := 240) (c := 1) (by norm_num) (by norm_num) h
    rw [one_mul] at this
    rw [this]
  ·
    rw [Lane.fld_eq_zero_of_lt 16 240 _ (Lane.low_lt (by norm_num) 240) h]
    omega

theorem andRec_spec (f : ℕ → ℕ) : ∀ n, (∀ k, fld (Nat.rec (motive := fun _ => ℕ) LOW16
    (fun m ih => strictN ih fun a => Nat.land a (f m)) n) 16 k ≤ 1) ∧
    ∀ d < 240, (Nat.rec (motive := fun _ => ℕ) LOW16
      (fun m ih => strictN ih fun a => Nat.land a (f m)) n).testBit (16 * d) = true ↔
      ∀ m < n, (f m).testBit (16 * d) = true := by
  intro n
  induction n with
  | zero => exact ⟨low16_fld, fun d hd => ⟨fun _ m hm => absurd hm (Nat.not_lt_zero _),
      fun _ => low16_testBit hd⟩⟩
  | succ n ih =>
    change (∀ k, fld (strictN (Nat.rec (motive := fun _ => ℕ) LOW16
      (fun m ih => strictN ih fun a => Nat.land a (f m)) n) fun a => Nat.land a (f n)) 16 k ≤ 1) ∧
      ∀ d < 240, (strictN (Nat.rec (motive := fun _ => ℕ) LOW16
      (fun m ih => strictN ih fun a => Nat.land a (f m)) n) fun a => Nat.land a (f n)).testBit
        (16 * d) = true ↔ ∀ m < n + 1, (f m).testBit (16 * d) = true
    rw [Lane.strictN_eq, Lane.nland]
    refine ⟨fun k => ?_, fun d hd => ?_⟩
    · rw [Lane.fld_land]
      exact Nat.and_le_left.trans (ih.1 k)
    · rw [Nat.testBit_and, Bool.and_eq_true, ih.2 d hd]
      constructor
      · rintro ⟨h1, h2⟩ m hm
        rcases Nat.lt_succ_iff_lt_or_eq.1 hm with hm | rfl
        · exact h1 m hm
        · exact h2
      · intro h
        exact ⟨fun m hm => h m (by omega), h n (by omega)⟩

theorem testBit4_lane {y d : ℕ} : y.testBit (16 * d + 4) = (fld y 16 d).testBit 4 := by
  rw [Lane.testBit_fld]
  simp

theorem bit4_add9 : ∀ Q < 16, (Q + 9).testBit 4 = decide (7 ≤ Q) := by decide

theorem bit4_sub : ∀ a < 16, ∀ b < 16, (a + 16 - b).testBit 4 = decide (b ≤ a) := by decide

theorem pos8_iff {V POS g : ℕ} (hvec : vec = vecOf 8 V) (h : pos8OK V POS g = true) :
    bit POS g = true ↔ ∀ m, 0 ≤ vec g m := by
  have e : bit POS g = allLt 8 (fun m => Nat.ble 7 (fld (fld V 128 g) 16 m)) := by
    simp only [pos8OK, Lane.strictB_eq] at h
    have key : ∀ a b : Bool, Bool.rec (motive := fun _ => Bool) (CFSG.TcRes.TK.notB b) b a = true → b = a := by
      decide
    exact key _ _ h
  rw [e, Lane.allLt_iff, hvec]
  simp only [Lane.ble_eq_true, vecOf, Nat.reduceMul]
  constructor
  · intro h m
    have := h m m.2
    omega
  · intro h m hm
    have := h ⟨m, hm⟩
    dsimp only at this
    omega

theorem dec8_iff (hD : DatumRaw Tag.E8 240 vec (fun g v => fld (RTs g) 8 v) adj neg)
    {V Y POS DEC : ℕ} {QS MVS : ℕ → ℕ} (hvec : vec = vecOf 8 V)
    (hVl : ∀ i < 240, ∀ m < 8, fld (fld V 128 i) 16 m < 16)
    (hYc : ∀ g < 240, ∀ m : Fin Tag.E8.rank, (fld (fld Y 256 g) 16 (7 - m) : ℤ) -
      fld (fld Y 256 g) 16 (15 - m) = ∑ k, Tag.E8.symmetrizedCartan m k * vec g k)
    (hYl : ∀ g < 240, ∀ j, fld (fld Y 256 g) 16 j ≤ 3) (hQb : ∀ m < 8, QS m < 2 ^ (16 * 240))
    (hq : ∀ i < 240, qOK QS V i = true) (hmv : ∀ x < 240, mvOK QS Y MVS x = true)
    (hpos : ∀ g < 240, pos8OK V POS g = true) (hdec : ∀ g < 240, dec8OK QS MVS V POS DEC g = true)
    {g d : ℕ} (hg : g < 240) (hd : d < 240) :
    bit (fld DEC 240 g) d = true ↔ bit POS d = true ∧ iform (vec g) (vec d) = 1 ∧
      bit POS (fld (RTs d) 8 g) = true := by
  have hQ : ∀ m < 8, QS m = lsum (fun i => fld (fld V 128 i) 16 m) := by
    intro m hm
    have hb : ∀ i < 240, fld (fld V 128 i) 16 m < 2 ^ 16 := fun i hi => by
      have := hVl i hi m hm
      omega
    rw [Lane.eq_sum_lanes 16 240 (QS m) (hQb m hm), Lane.eq_sum_lanes 16 240 (lsum _) (lsum_lt hb)]
    refine Finset.sum_congr rfl fun i hi => ?_
    have := hq i (Finset.mem_range.1 hi)
    simp only [qOK, Lane.strictB_eq, Lane.allLt_iff, Lane.beq_eq_true] at this
    rw [this m hm, fld_lsum hb, if_pos (Finset.mem_range.1 hi)]
  have h := hdec g hg
  simp only [dec8OK, Lane.strictB_eq, Lane.andB_eq_true, Lane.beq_eq_true] at h
  obtain ⟨-, hrow⟩ := h
  set P := posL QS with hP
  set G := Nat.rec (motive := fun _ => ℕ) LOW16
    (fun m ih => strictN ih fun a => Nat.land a (Nat.land (Nat.shiftRight (Nat.sub (Nat.mul
      (Nat.add (fld (fld V 128 g) 16 m) 16) LOW16) (QS m)) 4) LOW16)) 8 with hG
  have hPs := andRec_spec (fun m => Nat.land (Nat.shiftRight (Nat.add (QS m) (Nat.mul 9 LOW16)) 4)
    LOW16) 8
  have hGs := andRec_spec (fun m => Nat.land (Nat.shiftRight (Nat.sub (Nat.mul
      (Nat.add (fld (fld V 128 g) 16 m) 16) LOW16) (QS m)) 4) LOW16) 8
  have hmf := mv_fld hD hvec hVl hYc hYl hQb hq hmv hg 3
  have hPd : P.testBit (16 * d) = true ↔ ∀ m, 0 ≤ vec d m := by
    rw [hP, show posL QS = Nat.rec (motive := fun _ => ℕ) LOW16 (fun m ih => strictN ih fun a =>
      Nat.land a (Nat.land (Nat.shiftRight (Nat.add (QS m) (Nat.mul 9 LOW16)) 4) LOW16)) 8 from rfl,
      hPs.2 d hd]
    have e : ∀ m < 8, (Nat.land (Nat.shiftRight (Nat.add (QS m) (Nat.mul 9 LOW16)) 4)
        LOW16).testBit (16 * d) = decide (7 ≤ fld (fld V 128 d) 16 m) := by
      intro m hm
      rw [Lane.nland, Nat.testBit_and, low16_testBit hd, Bool.and_true, Lane.nshr,
        Nat.testBit_shiftRight, show 4 + 16 * d = 16 * d + 4 by ring, testBit4_lane, Lane.nadd,
        Lane.nmul, hQ m hm, low16_eq, mul_lsum, lsum_add,
        fld_lsum (fun i hi => by have := hVl i hi m hm; omega), if_pos hd, mul_one,
        bit4_add9 _ (hVl d hd m hm)]
    constructor
    · intro h m
      have := h m m.2
      rw [e m m.2, decide_eq_true_eq] at this
      rw [hvec]
      simp only [vecOf, Nat.reduceMul]
      omega
    · intro h m hm
      rw [e m hm, decide_eq_true_eq]
      have := h ⟨m, hm⟩
      rw [hvec] at this
      simp only [vecOf, Nat.reduceMul] at this
      omega
  have hGd : G.testBit (16 * d) = true ↔ ∀ m, vec d m ≤ vec g m := by
    rw [hG, hGs.2 d hd]
    have e : ∀ m < 8, (Nat.land (Nat.shiftRight (Nat.sub (Nat.mul
        (Nat.add (fld (fld V 128 g) 16 m) 16) LOW16) (QS m)) 4) LOW16).testBit (16 * d) =
        decide (fld (fld V 128 d) 16 m ≤ fld (fld V 128 g) 16 m) := by
      intro m hm
      have hvg := hVl g hg m hm
      rw [Lane.nland, Nat.testBit_and, low16_testBit hd, Bool.and_true, Lane.nshr,
        Nat.testBit_shiftRight, show 4 + 16 * d = 16 * d + 4 by ring, testBit4_lane, Lane.nsub,
        Lane.nmul, Lane.nadd, hQ m hm, low16_eq, mul_lsum,
        lsum_sub (fun i hi => by have := hVl i hi m hm; omega),
        fld_lsum (fun i hi => by have := hVl i hi m hm; omega), if_pos hd, mul_one,
        bit4_sub _ hvg _ (hVl d hd m hm)]
    constructor
    · intro h m
      have := h m m.2
      rw [e m m.2, decide_eq_true_eq] at this
      rw [hvec]
      simp only [vecOf, Nat.reduceMul]
      omega
    · intro h m hm
      rw [e m hm, decide_eq_true_eq]
      have := h ⟨m, hm⟩
      rw [hvec] at this
      simp only [vecOf, Nat.reduceMul] at this
      omega
  have hMd : (mvf MVS g 3).testBit (16 * d) = true ↔ iform (vec g) (vec d) = 1 := by
    rw [hmf, testBit_lsum (fun i _ => by split_ifs <;> omega), iform_comm (vec g)]
    constructor
    · rintro ⟨-, h⟩
      split_ifs at h with h' <;> omega
    · intro h
      exact ⟨hd, by rw [if_pos (by omega)]⟩
  rw [hrow, Lane.bit_iff, testBit_squash16 (fun k _ => ?_), decide_eq_true hd, Bool.true_and,
    Lane.nland, Lane.nland, Nat.testBit_and, Nat.testBit_and, Bool.and_eq_true, Bool.and_eq_true]
  rotate_left
  · rw [Lane.nland, Lane.fld_land]
    exact Nat.and_le_left.trans (hPs.1 k)
  change P.testBit (16 * d) = true ∧ (mvf MVS g 3).testBit (16 * d) = true ∧
    G.testBit (16 * d) = true ↔ _
  rw [hPd, hMd, hGd, pos8_iff hvec (hpos d hd), pos8_iff hvec (hpos _ (hD.refl d hd g hg).1)]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, fun m => ?_⟩
    rw [(hD.refl d hd g hg).2, h2, one_smul, Pi.sub_apply]
    have := h3 m
    omega
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, fun m => ?_⟩
    have := h3 m
    rw [(hD.refl d hd g hg).2, h2, one_smul, Pi.sub_apply] at this
    omega

end Tables

section Walks

@[expose] def ent8 (rest i : ℕ) : ℕ := (rest >>> (16 * i)) &&& 255

theorem ent8_zero (rest : ℕ) : ent8 rest 0 = rest &&& 255 := by
  simp [ent8]

theorem ent8_succ (rest i : ℕ) : ent8 (Nat.shiftRight rest 16) i = ent8 rest (i + 1) := by
  simp only [ent8, Lane.nshr, ← Nat.shiftRight_add]
  congr 2
  ring

theorem olen_succ (ph : ℕ → ℕ) (psi f x s : ℕ) : olen ph psi (f + 1) x s =
    cond (bit psi (ph x)) s (olen ph psi f (ph x) (s + 1)) := by
  change strictN (ph x) (fun y => Bool.rec (motive := fun _ => ℕ) (olen ph psi f y (Nat.succ s)) s
    (bit psi y)) = _
  rw [Lane.strictN_eq]
  cases bit psi (ph x) <;> rfl

theorem olen8_spec (ph : ℕ → ℕ) (psi : ℕ) : ∀ f x s, 1 ≤ s → 0 < olen ph psi f x s →
    s ≤ olen ph psi f x s ∧ olen ph psi f x s < s + f ∧
    bit psi (ph^[olen ph psi f x s + 1 - s] x) = true ∧
    ∀ t, 0 < t → t < olen ph psi f x s + 1 - s → bit psi (ph^[t] x) = false := by
  intro f
  induction f with
  | zero => intro x s _ h; exact absurd h (lt_irrefl 0)
  | succ f ih =>
    intro x s hs h
    rw [olen_succ] at h ⊢
    cases hb : bit psi (ph x)
    · simp only [hb, cond_false] at h ⊢
      obtain ⟨h1, h2, h3, h4⟩ := ih (ph x) (s + 1) (by omega) h
      refine ⟨by omega, by omega, ?_, fun t ht0 ht => ?_⟩
      · have e : olen ph psi f (ph x) (s + 1) + 1 - s =
            (olen ph psi f (ph x) (s + 1) + 1 - (s + 1)) + 1 := by omega
        rw [e, Function.iterate_succ_apply]
        exact h3
      · rcases t with _ | t
        · omega
        · rcases t with _ | t
          · simpa using hb
          · rw [Function.iterate_succ_apply]
            exact h4 (t + 1) (by omega) (by omega)
    · simp only [hb, cond_true]
      refine ⟨le_refl _, by omega, ?_, fun t ht0 ht => by omega⟩
      rw [show s + 1 - s = 1 by omega]
      simpa using hb

@[expose] def TJoin (ADJ C rt x : ℕ) : Prop := Relation.ReflTransGen
  (fun a b => C.testBit a = true ∧ C.testBit b = true ∧ (fld ADJ 240 b).testBit a = true) rt x

theorem TJoin.mono {ADJ C C' rt x : ℕ} (hC : ∀ y, C.testBit y = true → C'.testBit y = true)
    (h : TJoin ADJ C rt x) : TJoin ADJ C' rt x := by
  unfold TJoin at h ⊢
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hab ih => exact ih.tail ⟨hC _ hab.1, hC _ hab.2.1, hab.2.2⟩

structure TInv8 (ADJ Φ C NB rt k : ℕ) : Prop where
  rt_mem : C.testBit rt = true
  mem : ∀ x, C.testBit x = true → Φ.testBit x = true ∧ TJoin ADJ C rt x
  nb : ∀ y, C.testBit y = true → ∀ x, (fld ADJ 240 y).testBit x = true → NB.testBit x = true
  card : ((Finset.range 256).filter (fun x => C.testBit x = true)).card = k
  lt : ∀ x, C.testBit x = true → x < 256

theorem treeM8_succ (ADJ Φ c rest C NB : ℕ) : treeM8 ADJ Φ (c + 1) rest C NB =
    Bool.rec (motive := fun _ => ℕ) (Nat.shiftLeft 1 240)
      (treeM8 ADJ Φ c (Nat.shiftRight rest 16) (Nat.lor C (Nat.shiftLeft 1 (Nat.land rest 255)))
        (Nat.lor NB (fld ADJ 240 (Nat.land rest 255))))
      (CFSG.TcRes.TK.andB (bit Φ (Nat.land rest 255)) (CFSG.TcRes.TK.andB (CFSG.TcRes.TK.notB (bit C (Nat.land rest 255)))
        (Bool.rec (motive := fun _ => Bool) (CFSG.TcRes.TK.andB (CFSG.TcRes.TK.notB (Nat.beq (Nat.land rest 255)
            (Nat.land (Nat.shiftRight rest 8) 255))) (CFSG.TcRes.TK.andB (bit C (Nat.land (Nat.shiftRight rest 8) 255))
            (bit (fld ADJ 240 (Nat.land rest 255)) (Nat.land (Nat.shiftRight rest 8) 255))))
          (Nat.beq (Nat.land rest 255) (Nat.land (Nat.shiftRight rest 8) 255)) (Nat.beq C 0)))) := by
  simp only [treeM8, Lane.strictN_eq]

theorem fail_not_lt : ¬ Nat.shiftLeft 1 240 < 2 ^ 240 := by decide

theorem walk_fin_card {C g : ℕ} (hg : g < 256) (hC : C.testBit g = false) :
    ((Finset.range 256).filter (fun x => (C ||| 1 <<< g).testBit x = true)).card =
      ((Finset.range 256).filter (fun x => C.testBit x = true)).card + 1 := by
  have e : (Finset.range 256).filter (fun x => (C ||| 1 <<< g).testBit x = true) =
      insert g ((Finset.range 256).filter (fun x => C.testBit x = true)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, testBit_or_pow,
      Bool.or_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨hx, h | h⟩
      · exact Or.inr ⟨hx, h⟩
      · exact Or.inl h
    · rintro (rfl | ⟨hx, h⟩)
      · exact ⟨hg, Or.inr rfl⟩
      · exact ⟨hx, Or.inl h⟩
  rw [e, Finset.card_insert_of_notMem]
  simp [hC]

theorem treeM8_walk (ADJ Φ : ℕ) : ∀ c rest C NB rt k, TInv8 ADJ Φ C NB rt k →
    treeM8 ADJ Φ c rest C NB < 2 ^ 240 →
    (∀ x, (treeM8 ADJ Φ c rest C NB).testBit x = true →
      Φ.testBit x = true ∧ TJoin ADJ (treeM8 ADJ Φ c rest C NB) rt x) ∧
    (treeM8 ADJ Φ c rest C NB).testBit rt = true ∧
    (∀ y, (treeM8 ADJ Φ c rest C NB).testBit y = true → ∀ x, (fld ADJ 240 y).testBit x = true →
      Φ.testBit x = true → (treeM8 ADJ Φ c rest C NB).testBit x = true) ∧
    ((Finset.range 256).filter (fun x => (treeM8 ADJ Φ c rest C NB).testBit x = true)).card =
      k + c ∧
    (∀ x, (treeM8 ADJ Φ c rest C NB).testBit x = true ↔ C.testBit x = true ∨ ∃ i < c, ent8 rest i = x) ∧
    (∀ i < c, C.testBit (ent8 rest i) = false) ∧
    (∀ i < c, ∀ j < c, ent8 rest i = ent8 rest j → i = j) := by
  intro c
  induction c with
  | zero =>
    intro rest C NB rt k hI h
    have key : CFSG.TcRes.TK.andB (Nat.blt 0 C) (Nat.beq (Nat.land (Nat.land NB Φ) C) (Nat.land NB Φ)) = true := by
      by_contra hne
      rw [Bool.not_eq_true] at hne
      have e : treeM8 ADJ Φ 0 rest C NB = Nat.shiftLeft 1 240 := by
        change strictN (Nat.land NB Φ) (fun A => Bool.rec (motive := fun _ => ℕ)
          (Nat.shiftLeft 1 240) C (CFSG.TcRes.TK.andB (Nat.blt 0 C) (Nat.beq (Nat.land A C) A))) = _
        rw [Lane.strictN_eq, hne]
      rw [e] at h
      exact fail_not_lt h
    have hR : treeM8 ADJ Φ 0 rest C NB = C := by
      change strictN (Nat.land NB Φ) (fun A => Bool.rec (motive := fun _ => ℕ)
        (Nat.shiftLeft 1 240) C (CFSG.TcRes.TK.andB (Nat.blt 0 C) (Nat.beq (Nat.land A C) A))) = _
      rw [Lane.strictN_eq, key]
    rw [Lane.andB_eq_true, Lane.beq_eq_true] at key
    rw [hR]
    refine ⟨hI.mem, hI.rt_mem, fun y hy x hx hΦ => ?_, by simp [hI.card], fun x => ?_,
      fun i hi => absurd hi (Nat.not_lt_zero _), fun i hi => absurd hi (Nat.not_lt_zero _)⟩
    · have hA : (Nat.land (Nat.land NB Φ) C).testBit x = true := by
        rw [key.2, Lane.nland, Nat.testBit_and, hI.nb y hy x hx, hΦ]
        rfl
      rw [Lane.nland, Nat.testBit_and, Bool.and_eq_true] at hA
      exact hA.2
    · constructor
      · exact Or.inl
      · rintro (h | ⟨i, hi, -⟩)
        · exact h
        · exact absurd hi (Nat.not_lt_zero _)
  | succ c ih =>
    intro rest C NB rt k hI h
    have hC0 : Nat.beq C 0 = false := by
      rw [Lane.beq_eq_false]
      intro h0
      have := hI.rt_mem
      rw [h0, Nat.zero_testBit] at this
      exact absurd this (by decide)
    rw [treeM8_succ, hC0] at h ⊢
    set g := Nat.land rest 255 with hg
    set pa := Nat.land (Nat.shiftRight rest 8) 255 with hpa
    cases hk : CFSG.TcRes.TK.andB (bit Φ g) (CFSG.TcRes.TK.andB (CFSG.TcRes.TK.notB (bit C g)) (Bool.rec (motive := fun _ => Bool)
        (CFSG.TcRes.TK.andB (CFSG.TcRes.TK.notB (Nat.beq g pa)) (CFSG.TcRes.TK.andB (bit C pa) (bit (fld ADJ 240 g) pa))) (Nat.beq g pa) false))
    · rw [hk] at h
      exact absurd h fail_not_lt
    · rw [hk] at h
      simp only [hk]
      simp only [Lane.andB_eq_true, Lane.notB_eq_true] at hk
      obtain ⟨hΦg, hCg, -, hCpa, hag⟩ := hk
      rw [Lane.bit_iff] at hΦg hCpa hag
      rw [← Bool.not_eq_true, Lane.bit_iff, Bool.not_eq_true] at hCg
      have hglt : g < 256 := lt_of_le_of_lt Nat.and_le_right (by norm_num)
      have hI' : TInv8 ADJ Φ (Nat.lor C (Nat.shiftLeft 1 g)) (Nat.lor NB (fld ADJ 240 g)) rt (k + 1) := by
        have hsub : ∀ y, C.testBit y = true → (Nat.lor C (Nat.shiftLeft 1 g)).testBit y = true :=
          fun y hy => by rw [Lane.nlor, Lane.nshl, testBit_or_pow, hy, Bool.true_or]
        refine ⟨hsub _ hI.rt_mem, fun x hx => ?_, fun y hy x hx => ?_, ?_, fun x hx => ?_⟩
        · rw [Lane.nlor, Lane.nshl, testBit_or_pow, Bool.or_eq_true, decide_eq_true_eq] at hx
          rcases hx with hx | rfl
          · exact ⟨(hI.mem x hx).1, (hI.mem x hx).2.mono hsub⟩
          · refine ⟨hΦg, Relation.ReflTransGen.tail ((hI.mem _ hCpa).2.mono hsub)
              ⟨hsub _ hCpa, ?_, hag⟩⟩
            rw [Lane.nlor, Lane.nshl, testBit_or_pow]
            simp
        · rw [Lane.nlor, Nat.testBit_or, Bool.or_eq_true]
          rw [Lane.nlor, Lane.nshl, testBit_or_pow, Bool.or_eq_true, decide_eq_true_eq] at hy
          rcases hy with hy | rfl
          · exact Or.inl (hI.nb y hy x hx)
          · exact Or.inr hx
        · rw [Lane.nlor, Lane.nshl, walk_fin_card hglt hCg, hI.card]
        · rw [Lane.nlor, Lane.nshl, testBit_or_pow, Bool.or_eq_true, decide_eq_true_eq] at hx
          rcases hx with hx | rfl
          · exact hI.lt x hx
          · exact hglt
      obtain ⟨r1, r2, r3, r4, r5, r6, r7⟩ := ih _ _ _ _ _ hI' h
      refine ⟨r1, r2, r3, by rw [r4]; ring, fun x => ?_, fun i hi => ?_, fun i hi j hj hij => ?_⟩
      · rw [r5, Lane.nlor, Lane.nshl, testBit_or_pow, Bool.or_eq_true, decide_eq_true_eq]
        simp only [ent8_succ]
        constructor
        · rintro ((hx | rfl) | ⟨i, hi, rfl⟩)
          · exact Or.inl hx
          · exact Or.inr ⟨0, by omega, ent8_zero rest⟩
          · exact Or.inr ⟨i + 1, by omega, rfl⟩
        · rintro (hx | ⟨i, hi, rfl⟩)
          · exact Or.inl (Or.inl hx)
          · rcases i with _ | i
            · exact Or.inl (Or.inr (ent8_zero rest))
            · exact Or.inr ⟨i, by omega, rfl⟩
      · rcases i with _ | i
        · rw [ent8_zero]
          exact hCg
        · have := r6 i (by omega)
          rw [ent8_succ, Lane.nlor, Lane.nshl, testBit_or_pow, Bool.or_eq_false_iff] at this
          exact this.1
      · have hne : ∀ i < c, ent8 rest (i + 1) ≠ g := fun i hi he => by
          have := r6 i hi
          rw [ent8_succ, he, Lane.nlor, Lane.nshl, testBit_or_pow] at this
          simp at this
        rcases i with _ | i <;> rcases j with _ | j
        · rfl
        · rw [ent8_zero] at hij
          exact absurd hij.symm (hne j (by omega))
        · rw [ent8_zero] at hij
          exact absurd hij (hne i (by omega))
        · have := r7 i (by omega) j (by omega) (by rw [ent8_succ, ent8_succ]; exact hij)
          omega

theorem treeM8_spec {ADJ Φ c rest R : ℕ} (hR : treeM8 ADJ Φ c rest 0 0 = R) (h : R < 2 ^ 240) :
    R.testBit (rest &&& 255) = true ∧
    (∀ x, R.testBit x = true → Φ.testBit x = true ∧ TJoin ADJ R (rest &&& 255) x) ∧
    (∀ y, R.testBit y = true → ∀ x, (fld ADJ 240 y).testBit x = true → Φ.testBit x = true →
      R.testBit x = true) ∧
    ((Finset.range 256).filter (fun x => R.testBit x = true)).card = c ∧
    (∀ x, R.testBit x = true ↔ ∃ i < c, ent8 rest i = x) ∧
    (∀ i < c, ∀ j < c, ent8 rest i = ent8 rest j → i = j) := by
  subst hR
  rcases c with _ | c
  · have e : treeM8 ADJ Φ 0 rest 0 0 = Nat.shiftLeft 1 240 := by
      change strictN (Nat.land 0 Φ) (fun A => Bool.rec (motive := fun _ => ℕ)
        (Nat.shiftLeft 1 240) 0 (CFSG.TcRes.TK.andB (Nat.blt 0 0) (Nat.beq (Nat.land A 0) A))) = _
      rw [Lane.strictN_eq]
      rfl
    rw [e] at h
    exact absurd h fail_not_lt
  rw [treeM8_succ] at h ⊢
  have hC0 : Nat.beq 0 0 = true := rfl
  rw [hC0] at h ⊢
  set g := Nat.land rest 255 with hg
  set pa := Nat.land (Nat.shiftRight rest 8) 255 with hpa
  cases hk : CFSG.TcRes.TK.andB (bit Φ g) (CFSG.TcRes.TK.andB (CFSG.TcRes.TK.notB (bit 0 g)) (Bool.rec (motive := fun _ => Bool)
      (CFSG.TcRes.TK.andB (CFSG.TcRes.TK.notB (Nat.beq g pa)) (CFSG.TcRes.TK.andB (bit 0 pa) (bit (fld ADJ 240 g) pa))) (Nat.beq g pa) true))
  · rw [hk] at h
    exact absurd h fail_not_lt
  · rw [hk] at h
    simp only [hk]
    simp only [Lane.andB_eq_true] at hk
    obtain ⟨hΦg, -, -⟩ := hk
    rw [Lane.bit_iff] at hΦg
    have hglt : g < 256 := lt_of_le_of_lt Nat.and_le_right (by norm_num)
    have e1 : Nat.lor 0 (Nat.shiftLeft 1 g) = 1 <<< g := by simp [Lane.nlor, Lane.nshl]
    have e2 : Nat.lor 0 (fld ADJ 240 g) = fld ADJ 240 g := by simp [Lane.nlor]
    rw [e1, e2] at h ⊢
    have hI : TInv8 ADJ Φ (1 <<< g) (fld ADJ 240 g) g 1 := by
      refine ⟨by rw [pow_testBit]; simp, fun x hx => ?_, fun y hy x hx => ?_, ?_, fun x hx => ?_⟩
      · rw [pow_testBit, decide_eq_true_eq] at hx
        subst hx
        exact ⟨hΦg, Relation.ReflTransGen.refl⟩
      · rw [pow_testBit, decide_eq_true_eq] at hy
        subst hy
        exact hx
      · have : (Finset.range 256).filter (fun x => (1 <<< g).testBit x = true) = {g} := by
          ext x
          simp only [Finset.mem_filter, Finset.mem_range, pow_testBit, decide_eq_true_eq,
            Finset.mem_singleton]
          constructor
          · exact fun h => h.2
          · rintro rfl
            exact ⟨hglt, rfl⟩
        rw [this, Finset.card_singleton]
      · rw [pow_testBit, decide_eq_true_eq] at hx
        rw [hx]
        exact hglt
    obtain ⟨r1, r2, r3, r4, r5, r6, r7⟩ := treeM8_walk ADJ Φ c _ _ _ g 1 hI h
    refine ⟨r2, r1, r3, by rw [r4]; ring, fun x => ?_, fun i hi j hj hij => ?_⟩
    · rw [r5, pow_testBit, decide_eq_true_eq]
      simp only [ent8_succ]
      constructor
      · rintro (rfl | ⟨i, hi, rfl⟩)
        · exact ⟨0, by omega, ent8_zero rest⟩
        · exact ⟨i + 1, by omega, rfl⟩
      · rintro ⟨i, hi, rfl⟩
        rcases i with _ | i
        · exact Or.inl (ent8_zero rest)
        · exact Or.inr ⟨i, by omega, rfl⟩
    · have hne : ∀ i < c, ent8 rest (i + 1) ≠ g := fun i hi he => by
        have := r6 i hi
        rw [ent8_succ, he, pow_testBit] at this
        simp at this
      rcases i with _ | i <;> rcases j with _ | j
      · rfl
      · rw [ent8_zero] at hij
        exact absurd hij.symm (hne j (by omega))
      · rw [ent8_zero] at hij
        exact absurd hij (hne i (by omega))
      · have := r7 i (by omega) j (by omega) (by rw [ent8_succ, ent8_succ]; exact hij)
        omega

theorem simpN8_eq (POS DEC psi : ℕ) : ∀ c rest acc, simpN8 POS DEC psi c rest acc =
    acc + ∑ i ∈ Finset.range c, if CFSG.TcRes.TK.andB (bit POS (ent8 rest i))
      (Nat.beq (Nat.land (fld DEC 240 (ent8 rest i)) psi) 0) = true then 1 else 0 := by
  intro c
  induction c with
  | zero => intro rest acc; rfl
  | succ c ih =>
    intro rest acc
    have e : simpN8 POS DEC psi (c + 1) rest acc = simpN8 POS DEC psi c (Nat.shiftRight rest 16)
        (Bool.rec (motive := fun _ => ℕ) acc (Nat.succ acc) (CFSG.TcRes.TK.andB (bit POS (Nat.land rest 255))
          (Nat.beq (Nat.land (fld DEC 240 (Nat.land rest 255)) psi) 0))) := by
      simp only [simpN8, Lane.strictN_eq]
    rw [e, ih, Finset.sum_range_succ']
    simp only [ent8_succ, ent8_zero]
    change _ = acc + (_ + if CFSG.TcRes.TK.andB (bit POS (Nat.land rest 255))
      (Nat.beq (Nat.land (fld DEC 240 (Nat.land rest 255)) psi) 0) = true then 1 else 0)
    cases CFSG.TcRes.TK.andB (bit POS (Nat.land rest 255)) (Nat.beq (Nat.land (fld DEC 240 (Nat.land rest 255)) psi) 0)
    · simp
    · simp only [if_true]
      change acc + 1 + _ = _
      ring

theorem code8_dec {e r c ks d : ℕ} (he : e < 16) (hr : r < 16) (hc : c < 256)
    (hd : d = Nat.add e (Nat.add (Nat.mul 16 r) (Nat.add (Nat.mul 256 c) (Nat.mul 65536 ks)))) :
    dE d = e ∧ dR d = r ∧ CFSG.TcRes.TK.dN d = c ∧ dKs d = ks := by
  subst hd
  have l15 : ∀ x, Nat.land x 15 = x % 16 := fun x => Nat.and_two_pow_sub_one_eq_mod x 4
  have l255 : ∀ x, Nat.land x 255 = x % 256 := fun x => Nat.and_two_pow_sub_one_eq_mod x 8
  simp only [dE, dR, CFSG.TcRes.TK.dN, dKs, l15, l255, Nat.shiftRight_eq_div_pow, Lane.nadd, Lane.nmul]
  norm_num
  refine ⟨by omega, by omega, by omega, by omega⟩

theorem land_eq_zero_iff (a b : ℕ) : Nat.land a b = 0 ↔ ∀ x, b.testBit x = true → a.testBit x = false := by
  constructor
  · intro h x hb
    have := congrArg (fun n => n.testBit x) h
    simp only [Lane.nland, Nat.testBit_and, hb, Bool.and_true, Nat.zero_testBit] at this
    exact this
  · intro h
    apply Nat.eq_of_testBit_eq
    intro x
    rw [Lane.nland, Nat.testBit_and, Nat.zero_testBit]
    cases hb : b.testBit x
    · simp
    · simp [h x hb]

end Walks

end CFSG.KC.TcRes

end
