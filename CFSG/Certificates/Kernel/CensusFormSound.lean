
module

public import Certificates.Data.Kernel.CensusForm
public import CFSG.Certificates.Kernel.XorSpanSound
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3CensusBase

public section

namespace CFSG.KC.CensusForm

open CFSG.KC.Enum CFSG.KC.XorSpan CFSG.ComponentClassification.AS81.Census CFSG.Fischer
  CFSG.PSL3Four.Native

theorem decodeV_xor (a b : Nat) : decodeV (a ^^^ b) = decodeV a + decodeV b := by
  funext i
  apply F4_eq_of_val
  change (a ^^^ b) / 4 ^ i.val % 4 =
    ((⟨⟨a / 4 ^ i.val % 4, Nat.mod_lt _ (by decide)⟩⟩ : F4).code ^^^
      (⟨⟨b / 4 ^ i.val % 4, Nat.mod_lt _ (by decide)⟩⟩ : F4).code).val
  rw [Fin.xor_val]
  change (a ^^^ b) / 4 ^ i.val % 4 = (a / 4 ^ i.val % 4 ^^^ b / 4 ^ i.val % 4) % 4
  have e4 : (4 : Nat) ^ i.val = 2 ^ (2 * i.val) := by rw [Nat.pow_mul]
  have e2 : (4 : Nat) = 2 ^ 2 := rfl
  rw [e4, ← Nat.shiftRight_eq_div_pow, ← Nat.shiftRight_eq_div_pow, ← Nat.shiftRight_eq_div_pow,
    Nat.shiftRight_xor_distrib, e2, Nat.xor_mod_two_pow]
  exact (Nat.mod_eq_of_lt (Nat.xor_lt_two_pow (Nat.mod_lt _ (by decide))
    (Nat.mod_lt _ (by decide)))).symm

theorem encodeV_add (v w : V₀) : encodeV (v + w) = encodeV v ^^^ encodeV w := by
  have h : decodeV (encodeV v ^^^ encodeV w) = v + w := by
    rw [decodeV_xor, decodeV_encodeV, decodeV_encodeV]
  rw [← h, encodeV_decodeV]
  exact Nat.xor_lt_two_pow (n := 12) (encodeV_lt v) (encodeV_lt w)

theorem applyC_lin (M : Array Nat) : Lin 12 (applyC M) := by
  intro a _ b _
  rw [applyC, decodeV_xor, ← toLin_apply, map_add, encodeV_add, toLin_apply, toLin_apply]
  rfl

theorem applyC_lt (M : Array Nat) (n : Nat) : applyC M n < 4096 := encodeV_lt _

theorem xsK_eq (F : Nat → Nat) (s : Nat) : ∀ n, xsK F s n = xsel F s.testBit n
  | 0 => rfl
  | n + 1 => by
    change Nat.xor (xsK F s n) (Bool.rec (motive := fun _ => Nat) 0 (F n)
      (Nat.beq fld(s, n, nat_lit 1) (nat_lit 1))) = _
    rw [xsK_eq F s n, CFSG.KS.Raw.Orb.nIf_eq, bit_eq_one_iff, xsel_succ]
    rfl

theorem xsel_pow_eq {s n : Nat} (hs : s < 2 ^ n) : xsel (fun b => 2 ^ b) s.testBit n = s :=
  eq_of_testBit_lt (xsel_lt fun k hk _ => Nat.pow_lt_pow_right (by omega) hk) hs fun k hk => by
    rw [testBit_xsel_pow]
    simp [hk]

theorem xsel_shift (c : Nat → Bool) : ∀ n,
    xsel (fun b => 2 ^ (6 + b)) c n = 64 * xsel (fun b => 2 ^ b) c n
  | 0 => rfl
  | n + 1 => by
    rw [xsel_succ, xsel_succ, xsel_shift c n]
    have e : ∀ x, 64 * x = x <<< 6 := fun x => by rw [Nat.shiftLeft_eq, Nat.mul_comm]
    rw [e, e, Nat.shiftLeft_xor_distrib]
    congr 1
    split
    · rw [Nat.shiftLeft_eq, ← Nat.pow_add, Nat.add_comm]
    · rfl

theorem mod_xor_div (v : Nat) : v % 64 ^^^ 64 * (v / 64) = v := by
  apply Nat.eq_of_testBit_eq
  intro i
  have e : (64 : Nat) = 2 ^ 6 := rfl
  rw [Nat.testBit_xor, e, Nat.testBit_mod_two_pow, Nat.testBit_two_pow_mul, Nat.testBit_div_two_pow]
  by_cases hi : i < 6
  · simp [hi, show ¬ i ≥ 6 by omega]
  · simp [hi, show i ≥ 6 by omega, show i - 6 + 6 = i by omega]

theorem img_eq {M : Array Nat} {BL TL TH : Nat} (h : tabK M BL TL TH = true) {v : Nat}
    (hv : v < 4096) : img TL TH v = applyC M v := by
  unfold tabK at h
  obtain ⟨hb, hs⟩ := (CFSG.KS.bAnd_iff _ _).1 h
  have hB : ∀ b < 12, fld(BL, Nat.mul 12 b, 4095) = applyC M (2 ^ b) := by
    intro b hb'
    have := Nat.eq_of_beq_eq_true (CFSG.KS.allN_spec hb b hb')
    rw [this]
    congr 1
    change 1 <<< b = 2 ^ b
    rw [Nat.shiftLeft_eq, Nat.one_mul]
  have hL : ∀ s < 64, fld(TL, Nat.mul 12 s, 4095) = applyC M s := by
    intro s hs'
    have t := Nat.eq_of_beq_eq_true ((CFSG.KS.bAnd_iff _ _).1 (CFSG.KS.allN_spec hs s hs')).1
    rw [t, xsK_eq]
    refine (xsel_congr (r' := fun b => applyC M (2 ^ b)) (fun b hb' _ => ?_)
      (fun _ _ => rfl)).trans ?_
    · exact hB b (by have : b < 6 := hb'; omega)
    · have := (applyC_lin M).map_xsel (r := fun b => 2 ^ b) (c := s.testBit) (n := 6)
        (fun k hk => Nat.pow_lt_pow_right (by omega) (by omega))
      rw [xsel_pow_eq (n := 6) hs'] at this
      exact this.symm
  have hH : ∀ s < 64, fld(TH, Nat.mul 12 s, 4095) = applyC M (64 * s) := by
    intro s hs'
    have t := Nat.eq_of_beq_eq_true ((CFSG.KS.bAnd_iff _ _).1 (CFSG.KS.allN_spec hs s hs')).2
    rw [t, xsK_eq]
    refine (xsel_congr (r' := fun b => applyC M (2 ^ (6 + b))) (fun b hb' _ => ?_)
      (fun _ _ => rfl)).trans ?_
    · exact hB (6 + b) (by have : b < 6 := hb'; omega)
    · have := (applyC_lin M).map_xsel (r := fun b => 2 ^ (6 + b)) (c := s.testBit) (n := 6)
        (fun k hk => Nat.pow_lt_pow_right (by omega) (by omega))
      rw [xsel_shift, xsel_pow_eq (n := 6) hs'] at this
      exact this.symm
  unfold img img2
  have h1 : Nat.land v 63 = v % 64 := Nat.and_two_pow_sub_one_eq_mod v 6
  have h2 : Nat.shiftRight v 6 = v / 64 := Nat.shiftRight_eq_div_pow v 6
  rw [h1, h2, hL _ (Nat.mod_lt _ (by omega)), hH _ (by omega)]
  have := applyC_lin M (v % 64) (by omega) (64 * (v / 64)) (by omega)
  rw [mod_xor_div] at this
  exact this.symm

theorem isomOK_of_isomK {M : Array Nat} {BL TL TH QT : Nat}
    (hpre : (M.size == 6 && allBelow 6 fun i => decide (M[i]! < 4096)) = true)
    (ht : tabK M BL TL TH = true) (hq : qtK QT = true) (hi : isomK QT TL TH = true) :
    isomOK M = true := by
  unfold isomOK
  rw [hpre, Bool.true_and, CFSG.ComponentClassification.PSL3Four.allBelow_eq_true]
  intro n hn
  have hqt := CFSG.KS.allN_spec hq
  have h := CFSG.KS.allN_spec hi n hn
  rw [CFSG.KS.Raw.Orb.strictB_eq, img_eq ht hn] at h
  obtain ⟨h1, h2⟩ := (CFSG.KS.bAnd_iff _ _).1 h
  have hy := applyC_lt M n
  have e1 := Nat.eq_of_beq_eq_true (hqt _ hy)
  have e2 := Nat.eq_of_beq_eq_true (hqt n hn)
  have e := Nat.eq_of_beq_eq_true h1
  rw [e1, e2] at e
  have hd : decodeV (applyC M n) = applyF M (decodeV n) := by
    rw [applyC, decodeV_encodeV]
  rw [hd] at e
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq, bne_iff_ne,
    ne_eq]
  refine ⟨F4_eq_of_val e, ?_⟩
  rw [CFSG.KS.Raw.Orb.bIf_eq] at h2
  by_cases hn0 : n = 0
  · exact Or.inl hn0
  · right
    intro hz
    have : Nat.beq n 0 = false := Bool.eq_false_iff.mpr fun e => hn0 (Nat.eq_of_beq_eq_true e)
    rw [this, hz] at h2
    simp at h2

theorem applyC_eq_zero {M : Array Nat} (h : isomOK M = true) {a : Nat} (ha : a < 4096)
    (h0 : applyC M a = 0) : a = 0 := by
  simp only [isomOK, Bool.and_eq_true, beq_iff_eq,
    CFSG.ComponentClassification.PSL3Four.allBelow_eq_true, decide_eq_true_eq, Bool.or_eq_true,
    bne_iff_ne, ne_eq] at h
  rcases (h.2 a ha).2 with e | e
  · exact e
  · exact absurd h0 e

theorem formStep_span {M : Array Nat} {BL TL TH Kh Kq : Nat} (ht : tabK M BL TL TH = true)
    (hiso : isomOK M = true) (Rh : Rref 6 12 4095 72 Kh) (Rq : Rref 6 12 4095 72 Kq)
    (hmap : mapsK 6 12 4095 72 (img TL TH) Kh Kq = true) :
    formStep M (spanTab 6 12 4095 Kh) = spanTab 6 12 4095 Kq := by
  have hmap' : mapsK 6 12 4095 72 (applyC M) Kh Kq = true := by
    apply CFSG.KS.Raw.Orb.allN_iff.2
    intro k hk
    rw [← img_eq ht (row_lt (K := Kh) rfl k)]
    exact CFSG.KS.allN_spec hmap k hk
  unfold formStep
  rw [spanTab_map rfl Rh Rq (applyC_lin M) (fun a ha h0 => applyC_eq_zero hiso ha h0) hmap']

theorem actTab_get (M : Array Nat) {n : Nat} (hn : n < 4096) : (actTab M)[n]! = applyC M n := by
  rw [actTab, getElem!_pos _ _ (by simpa using hn), Array.getElem_ofFn]

theorem map_actTab (M : Array Nat) (K : Nat) :
    (spanTab 6 12 4095 K).toList.map (fun n => (actTab M)[n]!) =
      (spanTab 6 12 4095 K).toList.map (applyC M) := by
  refine List.map_congr_left fun n hn => ?_
  obtain ⟨s, -, rfl⟩ := mem_spanList.1 (mem_spanTab.1 hn)
  exact actTab_get M (spanOf_lt (d := 6) (K := K) (show 4095 = 2 ^ 12 - 1 from rfl) s)

theorem formStepT_span {M : Array Nat} {BL TL TH Kh Kq : Nat} (ht : tabK M BL TL TH = true)
    (hiso : isomOK M = true) (Rh : Rref 6 12 4095 72 Kh) (Rq : Rref 6 12 4095 72 Kq)
    (hmap : mapsK 6 12 4095 72 (img TL TH) Kh Kq = true) :
    formStepT (actTab M) (spanTab 6 12 4095 Kh) = spanTab 6 12 4095 Kq := by
  rw [← formStep_span ht hiso Rh Rq hmap]
  unfold formStepT formStep
  rw [map_actTab]

theorem mapsK_of_formStepT {M : Array Nat} {BL TL TH K : Nat} (ht : tabK M BL TL TH = true)
    (R : Rref 6 12 4095 72 K)
    (h : formStepT (actTab M) (spanTab 6 12 4095 K) = spanTab 6 12 4095 K) :
    mapsK 6 12 4095 72 (img TL TH) K K = true := by
  have hlist : ((spanTab 6 12 4095 K).toList.map (applyC M)).mergeSort (· ≤ ·) =
      (spanTab 6 12 4095 K).toList := by
    have := congrArg Array.toList h
    unfold formStepT at this
    rw [List.toList_toArray, map_actTab] at this
    exact this
  have hm := mapsK_of_map R hlist
  apply CFSG.KS.Raw.Orb.allN_iff.2
  intro k hk
  rw [img_eq ht (row_lt (K := K) rfl k)]
  exact CFSG.KS.allN_spec hm k hk

theorem foldl_insert_arr (a : Array Tab) (j : Nat) (m : Std.HashMap Tab Nat) (t : Tab) :
    (a.foldl (fun m t => m.insert t j) m).get? t = if t ∈ a then some j else m.get? t := by
  have hl : ∀ (l : List Tab) (m : Std.HashMap Tab Nat),
      (l.foldl (fun m t => m.insert t j) m).get? t = if t ∈ l then some j else m.get? t := by
    intro l
    induction l with
    | nil => intro m; simp
    | cons x l ih =>
      intro m
      rw [List.foldl_cons, ih, Std.HashMap.get?_insert]
      by_cases hx : t ∈ l
      · simp [hx]
      · by_cases e : x = t
        · subst e
          simp [hx]
        · have : (x == t) = false := beq_false_of_ne e
          simp [hx, this, Ne.symm e]
  rw [← Array.foldl_toList, hl]
  simp only [Array.mem_toList_iff]

theorem foldl_insert_get (A : Nat → Array Tab) (n : Nat)
    (hdisj : ∀ j < n, ∀ j' < n, ∀ t ∈ A j, t ∈ A j' → j = j') :
    ∀ j < n, ∀ t ∈ A j, ((List.range n).foldl (fun m j => (A j).foldl (fun m t => m.insert t j) m)
      ({} : Std.HashMap Tab Nat)).get? t = some j := by
  intro j0 hj0 t ht0
  have key : ∀ n' ≤ n, ∀ j < n', t ∈ A j → ((List.range n').foldl
      (fun m j => (A j).foldl (fun m t => m.insert t j) m) ({} : Std.HashMap Tab Nat)).get? t =
      some j := by
    intro n' hn'
    induction n' with
    | zero => intro j hj; omega
    | succ n' ih =>
      intro j hj ht
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, foldl_insert_arr]
      by_cases hn : t ∈ A n'
      · simp only [hn, ↓reduceIte]
        rw [hdisj j (by omega) n' (by omega) t ht hn]
      · simp only [hn, ↓reduceIte]
        refine ih (by omega) j ?_ ht
        rcases Nat.lt_or_ge j n' with h | h
        · exact h
        · exact absurd (show j = n' by omega ▸ ht) hn
  exact key n le_rfl j0 hj0 ht0

end CFSG.KC.CensusForm

end
