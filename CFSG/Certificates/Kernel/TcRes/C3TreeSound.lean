module

public import CFSG.Certificates.Kernel.TcRes.MaskSound
public import Certificates.Data.Kernel.TcRes.C3

public section

namespace CFSG.KC.TcRes

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.TcRes.TK CFSG.KC.TcRes.Lane

@[expose] def tkey (e : ℕ) : ℕ := e &&& 65535

def TRec (MVS PGs LF : ℕ → ℕ) (PW ZL a0 b0 e : ℕ) : Prop :=
  fld ZL 16 (tkey e >>> 8) = 1 ∧ (bmask MVS PW ZL (tkey e >>> 8)).testBit (16 * (e &&& 255)) = true ∧
    trecOK PGs LF a0 b0 e (tkey e >>> 8) (e &&& 255) = true

theorem tkey_shr_lt (e : ℕ) : tkey e >>> 8 < 256 := by
  have h : tkey e < 2 ^ 16 := by
    change e &&& (2 ^ 16 - 1) < 2 ^ 16
    rw [Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_lt _ (by norm_num)
  rw [Nat.shiftRight_eq_div_pow]
  have : (256 : ℕ) = 2 ^ 16 / 2 ^ 8 := by norm_num
  omega

theorem tWalk_succ (MVS PGs LF : ℕ → ℕ) (PW ZL a0 b0 c rest prev ca cm : ℕ) :
    tWalk MVS PGs LF PW ZL a0 b0 (c + 1) rest prev ca cm =
      CFSG.TcRes.TK.andB (Nat.blt prev (tkey (fld rest 40 0)))
      (CFSG.TcRes.TK.andB (Nat.beq (fld ZL 16 (tkey (fld rest 40 0) >>> 8)) 1)
      (CFSG.TcRes.TK.andB (bit (Bool.rec (motive := fun _ => ℕ) (bmask MVS PW ZL (tkey (fld rest 40 0) >>> 8)) cm
          (Nat.beq (tkey (fld rest 40 0) >>> 8) ca)) (16 * (fld rest 40 0 &&& 255)))
      (CFSG.TcRes.TK.andB (trecOK PGs LF a0 b0 (fld rest 40 0) (tkey (fld rest 40 0) >>> 8) (fld rest 40 0 &&& 255))
        (tWalk MVS PGs LF PW ZL a0 b0 c (rest >>> 40) (tkey (fld rest 40 0))
          (tkey (fld rest 40 0) >>> 8)
          (Bool.rec (motive := fun _ => ℕ) (bmask MVS PW ZL (tkey (fld rest 40 0) >>> 8)) cm
            (Nat.beq (tkey (fld rest 40 0) >>> 8) ca)))))) := by
  have e1 : fld rest 40 0 = rest &&& M40 := by
    change rest >>> (40 * 0) &&& ((1 <<< 40) - 1) = _
    rfl
  simp only [tWalk, strictB_eq, tkey, e1]
  rfl

theorem tWalk_spec (MVS PGs LF : ℕ → ℕ) (PW ZL a0 b0 : ℕ) : ∀ c rest prev ca cm,
    (ca < 256 → cm = bmask MVS PW ZL ca) →
    tWalk MVS PGs LF PW ZL a0 b0 c rest prev ca cm = true →
    (0 < c → prev < tkey (fld rest 40 0)) ∧
    (∀ s, s + 1 < c → tkey (fld rest 40 s) < tkey (fld rest 40 (s + 1))) ∧
    ∀ s < c, TRec MVS PGs LF PW ZL a0 b0 (fld rest 40 s) := by
  intro c
  induction c with
  | zero =>
    intro rest prev ca cm _ _
    exact ⟨fun h => absurd h (Nat.lt_irrefl 0), fun s hs => by omega, fun s hs => by omega⟩
  | succ c ih =>
    intro rest prev ca cm hcm h
    rw [tWalk_succ] at h
    simp only [andB_eq_true, blt_eq_true, beq_eq_true] at h
    obtain ⟨h1, h2, h3, h4, hw⟩ := h
    have hm : Bool.rec (motive := fun _ => ℕ) (bmask MVS PW ZL (tkey (fld rest 40 0) >>> 8)) cm
        (Nat.beq (tkey (fld rest 40 0) >>> 8) ca) = bmask MVS PW ZL (tkey (fld rest 40 0) >>> 8) := by
      cases hb : Nat.beq (tkey (fld rest 40 0) >>> 8) ca
      · rfl
      · have := beq_eq_true.1 hb
        rw [← this] at hcm
        exact hcm (tkey_shr_lt _)
    rw [hm] at h3 hw
    obtain ⟨i1, i2, i3⟩ := ih _ _ _ _ (fun _ => rfl) hw
    have hsh : ∀ s, fld (rest >>> 40) 40 s = fld rest 40 (s + 1) := fun s => by
      have := fld_shr rest 40 1 s
      rw [mul_one, add_comm] at this
      exact this
    refine ⟨fun _ => h1, fun s hs => ?_, fun s hs => ?_⟩
    · rcases s with _ | s
      · have := i1 (by omega)
        rw [hsh] at this
        exact this
      · have := i2 s (by omega)
        rw [hsh, hsh] at this
        exact this
    · rcases s with _ | s
      · exact ⟨h2, (bit_iff).1 h3, h4⟩
      · have := i3 s (by omega)
        rw [hsh] at this
        exact this

theorem trec_eq (LF : ℕ → ℕ) {L s : ℕ} (hs : s < 64) : trec LF (64 * L + s) = fld (LF L) 40 s := by
  have h1 : (64 * L + s) >>> 6 = L := by
    rw [Nat.shiftRight_eq_div_pow]
    omega
  have h2 : (64 * L + s) &&& 63 = s := by
    rw [(by norm_num : (63 : ℕ) = 2 ^ 6 - 1), Nat.and_two_pow_sub_one_eq_mod]
    omega
  change LF ((64 * L + s) >>> 6) >>> (((64 * L + s) &&& 63) * 40) &&& M40 = _
  rw [h1, h2, mul_comm]
  rfl

theorem tree_of_leaves {MVS PGs LF : ℕ → ℕ} {PW ZL a0 b0 : ℕ}
    (hleaf : ∀ L < 120, tleaf MVS PGs LF PW ZL a0 b0 L = true) :
    (∀ p q, p < q → q < 7680 → tkey (trec LF p) < tkey (trec LF q)) ∧
    ∀ p < 7680, TRec MVS PGs LF PW ZL a0 b0 (trec LF p) := by
  have hw : ∀ L < 120, _ := fun L hL =>
    tWalk_spec MVS PGs LF PW ZL a0 b0 64 (LF L) (tprev LF L) 256 0 (fun h => absurd h (by omega))
      (hleaf L hL)
  have hp : ∀ p, p = 64 * (p / 64) + p % 64 := fun p => (Nat.div_add_mod p 64).symm
  have hsucc : ∀ p, p + 1 < 7680 → tkey (trec LF p) < tkey (trec LF (p + 1)) := by
    intro p hp1
    rcases (by omega : p % 64 < 63 ∨ p % 64 = 63) with h | h
    · have e1 := trec_eq LF (L := p / 64) (s := p % 64) (by omega)
      have e2 := trec_eq LF (L := p / 64) (s := p % 64 + 1) (by omega)
      rw [← hp p] at e1
      rw [(by omega : 64 * (p / 64) + (p % 64 + 1) = p + 1)] at e2
      rw [e1, e2]
      exact (hw (p / 64) (by omega)).2.1 _ (by omega)
    · have e1 := trec_eq LF (L := p / 64) (s := 63) (by omega)
      have e2 := trec_eq LF (L := p / 64 + 1) (s := 0) (by omega)
      rw [(by omega : 64 * (p / 64) + 63 = p)] at e1
      rw [(by omega : 64 * (p / 64 + 1) + 0 = p + 1)] at e2
      have h0 := (hw (p / 64 + 1) (by omega)).1 (by norm_num)
      rw [← e2] at h0
      have htp : tprev LF (p / 64 + 1) = tkey (trec LF p) := by
        change trec LF (p / 64 * 64 + 63) &&& 65535 = _
        rw [(by omega : p / 64 * 64 + 63 = p)]
        rfl
      rw [htp] at h0
      exact h0
  refine ⟨fun p q hpq hq => ?_, fun p hp1 => ?_⟩
  · induction q with
    | zero => omega
    | succ q ih =>
      rcases (by omega : p = q ∨ p < q) with rfl | h
      · exact hsucc p hq
      · exact lt_trans (ih h (by omega)) (hsucc q hq)
  · have e := trec_eq LF (L := p / 64) (s := p % 64) (by omega)
    rw [← hp p] at e
    rw [e]
    exact (hw (p / 64) (by omega)).2.2 _ (by omega)

@[expose] def Adm (vec : ℕ → Fin Tag.E8.rank → ℤ) (PW a b : ℕ) : Prop :=
  a < 240 ∧ b < 240 ∧ iform (vec a) (vec (fld PW 8 a)) = 0 ∧ iform (vec b) (vec (fld PW 8 b)) = 0 ∧
    iform (vec b) (vec a) = -1 ∧ iform (vec b) (vec (fld PW 8 a)) = 0

theorem lsum_land {f g : ℕ → ℕ} (hf : ∀ i < 240, f i ≤ 1) (hg : ∀ i < 240, g i ≤ 1) {Z : ℕ}
    (hZ : ∀ i < 240, fld Z 16 i = g i) : lsum f &&& Z = lsum (fun i => f i * g i) := by
  have hfg : ∀ i < 240, f i * g i < 2 ^ 16 := fun i hi => by
    have h1 := hf i hi
    have h2 := hg i hi
    have : f i * g i ≤ 1 * 1 := Nat.mul_le_mul h1 h2
    omega
  apply Nat.eq_of_testBit_eq
  intro n
  have e1 := testBit_fld (lsum f &&& Z) 16 (n / 16) (n % 16)
  have e2 := testBit_fld (lsum fun i => f i * g i) 16 (n / 16) (n % 16)
  have hn : 16 * (n / 16) + n % 16 = n := Nat.div_add_mod n 16
  have hlt : decide (n % 16 < 16) = true := decide_eq_true (Nat.mod_lt _ (by norm_num))
  rw [hn, hlt, Bool.true_and] at e1 e2
  rw [← e1, ← e2, fld_land, fld_lsum (fun i hi => by have := hf i hi; omega), fld_lsum hfg]
  split_ifs with hi
  · rw [hZ _ hi]
    have := hf _ hi
    have := hg _ hi
    rcases (by omega : f (n / 16) = 0 ∨ f (n / 16) = 1) with h | h <;>
      rcases (by omega : g (n / 16) = 0 ∨ g (n / 16) = 1) with h' | h' <;> simp [h, h']
  · simp

theorem pop240_lsum {g : ℕ → ℕ} (hg : ∀ i < 240, g i ≤ 1) :
    pop240 (lsum g) = ∑ i ∈ Finset.range 240, g i := by
  have hg' : ∀ i < 240, g i < 2 ^ 16 := fun i hi => by have := hg i hi; omega
  have h1 : ∀ i < 240, (fun _ => 1 : ℕ → ℕ) i < 2 ^ 16 := fun _ _ => by norm_num
  have hx := lsum_lt hg'
  have hy := lsum_lt h1
  have hxl : ∀ i, fld (lsum g) 16 i ≤ 1 := fun i => by
    rw [fld_lsum hg']
    split_ifs with h
    · exact hg i h
    · exact zero_le_one
  have hyl : ∀ i, fld (lsum fun _ => 1) 16 i ≤ 1 := fun i => by
    rw [fld_lsum h1]
    split_ifs <;> norm_num
  have e : pop240 (lsum g) = fld (lsum g * lsum fun _ => 1) 16 239 := by
    rw [← low16_eq]
    rfl
  rw [e, fld_mul 16 240 240 _ _ hx hy
    (fun k => lt_of_le_of_lt (conv_le 16 240 _ _ 1 1 hx hxl hyl k) (by norm_num))]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := Finset.mem_range.1 hi
  rw [fld_lsum hg', fld_lsum h1, if_pos (by omega), if_pos (by omega), mul_one]

section Pairs

variable {vec : ℕ → Fin Tag.E8.rank → ℤ} {MVS : ℕ → ℕ} {PW ZL : ℕ}

theorem mvf_ind (hmvf : ∀ x < 240, ∀ f : ℕ, mvf MVS x f =
      lsum (fun i => if iform (vec i) (vec x) + 2 = f then 1 else 0)) {x : ℕ} (hx : x < 240)
    (f : ℕ) (c : ℤ) (hc : c + 2 = f) :
    mvf MVS x f = lsum (fun i => if iform (vec i) (vec x) = c then 1 else 0) := by
  rw [hmvf x hx f]
  refine lsum_congr fun i _ => ?_
  rw [← hc]
  split_ifs with p q q <;> first | rfl | omega

theorem zl_lane (hmvf : ∀ x < 240, ∀ f : ℕ, mvf MVS x f =
      lsum (fun i => if iform (vec i) (vec x) + 2 = f then 1 else 0))
    (hPW : ∀ g < 240, fld PW 8 g < 240) (hzl : zlOK MVS PW ZL = true) {b : ℕ} (hb : b < 240) :
    fld ZL 16 b = if iform (vec b) (vec (fld PW 8 b)) = 0 then 1 else 0 := by
  have h : fld ZL 16 b = fld (mvf MVS (fld PW 8 b) 2) 16 b := beq_eq_true.1 (Lane.allLt_iff.1 hzl b hb)
  rw [h, mvf_ind hmvf (hPW b hb) 2 0 (by norm_num), fld_lsum (fun i _ => by split_ifs <;> norm_num),
    if_pos hb]

theorem bmask_eq (hmvf : ∀ x < 240, ∀ f : ℕ, mvf MVS x f =
      lsum (fun i => if iform (vec i) (vec x) + 2 = f then 1 else 0))
    (hPW : ∀ g < 240, fld PW 8 g < 240) (hzl : zlOK MVS PW ZL = true) {a : ℕ} (ha : a < 240) :
    bmask MVS PW ZL a = lsum (fun i => (if iform (vec i) (vec a) = -1 then 1 else 0) *
      ((if iform (vec i) (vec (fld PW 8 a)) = 0 then 1 else 0) *
        (if iform (vec i) (vec (fld PW 8 i)) = 0 then 1 else 0))) := by
  have e : bmask MVS PW ZL a = mvf MVS a 1 &&& (mvf MVS (fld PW 8 a) 2 &&& ZL) := rfl
  have b01 : ∀ (P : ℕ → Prop) [DecidablePred P], ∀ i < 240, (if P i then 1 else 0) ≤ 1 :=
    fun P _ i _ => by split_ifs <;> norm_num
  have hz := lsum_land (b01 _) (b01 _) (Z := ZL) (fun i hi => zl_lane hmvf hPW hzl hi)
    (f := fun i => if iform (vec i) (vec (fld PW 8 a)) = 0 then 1 else 0)
  have hp : ∀ i < 240, (if iform (vec i) (vec (fld PW 8 a)) = 0 then 1 else 0) *
      (if iform (vec i) (vec (fld PW 8 i)) = 0 then 1 else 0) ≤ 1 := fun i _ => by
    split_ifs <;> norm_num
  rw [e, mvf_ind hmvf ha 1 (-1) (by norm_num), mvf_ind hmvf (hPW a ha) 2 0 (by norm_num), hz,
    lsum_land (b01 _) hp (fun i hi => by
      rw [fld_lsum (fun i hi => by have := hp i hi; omega), if_pos hi])]

open Classical in
theorem adm_card (hmvf : ∀ x < 240, ∀ f : ℕ, mvf MVS x f =
      lsum (fun i => if iform (vec i) (vec x) + 2 = f then 1 else 0))
    (hPW : ∀ g < 240, fld PW 8 g < 240) (hzl : zlOK MVS PW ZL = true)
    (hcnt : cntOK MVS PW ZL = true) :
    ((Finset.range 240 ×ˢ Finset.range 240).filter (fun q => Adm vec PW q.1 q.2)).card = 7680 := by
  have h0 : sumLt 240 (fun a => fld ZL 16 a * pop240 (bmask MVS PW ZL a)) = 7680 :=
    beq_eq_true.1 hcnt
  rw [sumLt_eq] at h0
  rw [← h0, Finset.card_filter, Finset.sum_product]
  refine Finset.sum_congr rfl fun a ha => ?_
  have ha' := Finset.mem_range.1 ha
  rw [zl_lane hmvf hPW hzl ha', bmask_eq hmvf hPW hzl ha',
    pop240_lsum (fun i _ => by split_ifs <;> norm_num), Finset.mul_sum]
  refine Finset.sum_congr rfl fun b hb => ?_
  have hb' := Finset.mem_range.1 hb
  by_cases p1 : iform (vec a) (vec (fld PW 8 a)) = 0 <;>
    by_cases p2 : iform (vec b) (vec (fld PW 8 b)) = 0 <;>
    by_cases p3 : iform (vec b) (vec a) = -1 <;>
    by_cases p4 : iform (vec b) (vec (fld PW 8 a)) = 0 <;>
    simp [Adm, ha', hb', p1, p2, p3, p4]

end Pairs

@[expose] noncomputable def wapp (PGs : ℕ → ℕ) : List ℕ → ℕ → ℕ
  | [], x => x
  | k :: ks, x => fld (PGs k) 8 (wapp PGs ks x)

theorem wapp_lt {PGs : ℕ → ℕ} (hPG : ∀ k < 3, ∀ g < 240, fld (PGs k) 8 g < 240) {x : ℕ}
    (hx : x < 240) : ∀ ks : List ℕ, (∀ k ∈ ks, k < 3) → wapp PGs ks x < 240
  | [], _ => hx
  | k :: ks, h => hPG k (h k (by simp)) _ (wapp_lt hPG hx ks fun k' hk' => h k' (by simp [hk']))

theorem shr8_land (e : ℕ) : (e >>> 8) &&& 255 = tkey e >>> 8 := by
  have e1 : (255 : ℕ) = 2 ^ 8 - 1 := by norm_num
  have e2 : (65535 : ℕ) = 2 ^ 16 - 1 := by norm_num
  have p8 : (2 : ℕ) ^ 8 = 256 := by norm_num
  have p16 : (2 : ℕ) ^ 16 = 65536 := by norm_num
  unfold tkey
  rw [e1, e2, Nat.and_two_pow_sub_one_eq_mod, Nat.and_two_pow_sub_one_eq_mod,
    Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, p8, p16]
  omega

theorem tkey_eq (e : ℕ) : tkey e = 256 * (tkey e >>> 8) + (e &&& 255) := by
  have e1 : (255 : ℕ) = 2 ^ 8 - 1 := by norm_num
  have e2 : (65535 : ℕ) = 2 ^ 16 - 1 := by norm_num
  have p8 : (2 : ℕ) ^ 8 = 256 := by norm_num
  have p16 : (2 : ℕ) ^ 16 = 65536 := by norm_num
  unfold tkey
  rw [e1, e2, Nat.and_two_pow_sub_one_eq_mod, Nat.and_two_pow_sub_one_eq_mod,
    Nat.shiftRight_eq_div_pow, p8, p16]
  omega

theorem tparOK_iff (PGs : ℕ → ℕ) (a b d k pe : ℕ) : tparOK PGs a b d k pe = true ↔
    ((pe >>> 16) &&& 63) + 1 = d ∧ k < 3 ∧ fld (PGs k) 8 ((pe >>> 8) &&& 255) = a ∧
      fld (PGs k) 8 (pe &&& 255) = b := by
  unfold tparOK
  rw [strictB_eq]
  change CFSG.TcRes.TK.andB (Nat.beq (((pe >>> 16) &&& 63) + 1) d) (CFSG.TcRes.TK.andB (Nat.blt k 3)
    (CFSG.TcRes.TK.andB (Nat.beq (fld (PGs k) 8 ((pe >>> 8) &&& 255)) a)
      (Nat.beq (fld (PGs k) 8 (pe &&& 255)) b))) = true ↔ _
  simp only [andB_eq_true, beq_eq_true, blt_eq_true]

theorem trecOK_iff (PGs LF : ℕ → ℕ) (a0 b0 e a b : ℕ) : trecOK PGs LF a0 b0 e a b = true ↔
    ((e >>> 16) &&& 63 = 0 ∧ a = a0 ∧ b = b0) ∨ ((e >>> 16) &&& 63 ≠ 0 ∧
      (e >>> 22) &&& 8191 < 7680 ∧
      tparOK PGs a b ((e >>> 16) &&& 63) (e >>> 35) (trec LF ((e >>> 22) &&& 8191)) = true) := by
  unfold trecOK
  rw [strictB_eq, strictB_eq]
  change Bool.rec (motive := fun _ => Bool)
    (CFSG.TcRes.TK.andB (Nat.blt ((e >>> 22) &&& 8191) 7680)
      (strictB (trec LF ((e >>> 22) &&& 8191)) (tparOK PGs a b ((e >>> 16) &&& 63) (e >>> 35))))
    (CFSG.TcRes.TK.andB (Nat.beq a a0) (Nat.beq b b0)) (Nat.beq ((e >>> 16) &&& 63) 0) = true ↔ _
  rw [strictB_eq]
  cases h : Nat.beq ((e >>> 16) &&& 63) 0
  · have h' := beq_eq_false.1 h
    simp only [andB_eq_true, beq_eq_true, blt_eq_true, h', false_and, ne_eq, not_false_eq_true,
      true_and, false_or]
  · have h' := beq_eq_true.1 h
    simp only [andB_eq_true, beq_eq_true, h', true_and, ne_eq, not_true_eq_false, false_and,
      or_false]

theorem rec_reach {MVS PGs LF : ℕ → ℕ} {PW ZL a0 b0 : ℕ}
    (hleaf : ∀ L < 120, tleaf MVS PGs LF PW ZL a0 b0 L = true) : ∀ d p, p < 7680 →
    (trec LF p >>> 16) &&& 63 = d → ∃ ks : List ℕ, (∀ k ∈ ks, k < 3) ∧
      tkey (trec LF p) >>> 8 = wapp PGs ks a0 ∧ trec LF p &&& 255 = wapp PGs ks b0 := by
  intro d
  induction d with
  | zero =>
    intro p hp hd
    rcases (trecOK_iff _ _ _ _ _ _ _).1 ((tree_of_leaves hleaf).2 p hp).2.2 with
      ⟨_, h1, h2⟩ | ⟨h0, _⟩
    · exact ⟨[], by simp, h1, h2⟩
    · exact absurd hd h0
  | succ d ih =>
    intro p hp hd
    rcases (trecOK_iff _ _ _ _ _ _ _).1 ((tree_of_leaves hleaf).2 p hp).2.2 with
      ⟨h0, _⟩ | ⟨_, hP, hpar⟩
    · rw [hd] at h0
      exact absurd h0 (by omega)
    · rw [hd, tparOK_iff] at hpar
      obtain ⟨hd', hk, ha, hb⟩ := hpar
      obtain ⟨ks, hks, hka, hkb⟩ := ih _ hP (by omega)
      refine ⟨(trec LF p >>> 35) :: ks, fun k hk' => ?_, ?_, ?_⟩
      · rcases List.mem_cons.1 hk' with rfl | h
        · exact hk
        · exact hks k h
      · rw [← ha, shr8_land, hka]
        rfl
      · rw [← hb, hkb]
        rfl

open Classical in
theorem adm_reach {vec : ℕ → Fin Tag.E8.rank → ℤ} {MVS PGs LF : ℕ → ℕ} {PW ZL a0 b0 : ℕ}
    (hmvf : ∀ x < 240, ∀ f : ℕ, mvf MVS x f =
      lsum (fun i => if iform (vec i) (vec x) + 2 = f then 1 else 0))
    (hPW : ∀ g < 240, fld PW 8 g < 240) (hPG : ∀ k < 3, ∀ g < 240, fld (PGs k) 8 g < 240)
    (ha0 : a0 < 240) (hb0 : b0 < 240) (hzl : zlOK MVS PW ZL = true)
    (hcnt : cntOK MVS PW ZL = true) (hleaf : ∀ L < 120, tleaf MVS PGs LF PW ZL a0 b0 L = true)
    {a b : ℕ} (hab : Adm vec PW a b) :
    ∃ ks : List ℕ, (∀ k ∈ ks, k < 3) ∧ a = wapp PGs ks a0 ∧ b = wapp PGs ks b0 := by
  obtain ⟨S, hS⟩ : ∃ S : Finset (ℕ × ℕ),
    S = (Finset.range 240 ×ˢ Finset.range 240).filter (fun q => Adm vec PW q.1 q.2) := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r : ℕ → ℕ × ℕ, r = fun p => (tkey (trec LF p) >>> 8, trec LF p &&& 255) :=
    ⟨_, rfl⟩
  have hT := tree_of_leaves hleaf
  have hmem : ∀ p < 7680, r p ∈ S := by
    intro p hp
    have hrr := rec_reach hleaf ((trec LF p >>> 16) &&& 63) p hp rfl
    obtain ⟨ks, hks, hka, hkb⟩ := hrr
    have hra : tkey (trec LF p) >>> 8 < 240 := hka ▸ wapp_lt hPG ha0 ks hks
    have hTp := hT.2 p hp
    obtain ⟨hz, hbm, _⟩ := hTp
    rw [hr]
    rw [zl_lane hmvf hPW hzl hra] at hz
    rw [bmask_eq hmvf hPW hzl hra, testBit_lsum (fun i _ => by split_ifs <;> norm_num)] at hbm
    obtain ⟨hrb, hb1⟩ := hbm
    rw [hS, Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]
    refine ⟨⟨hra, hrb⟩, hra, hrb, ?_, ?_, ?_, ?_⟩
    · by_contra h
      rw [if_neg h] at hz
      exact absurd hz (by norm_num)
    all_goals
      by_contra h
      rw [if_neg h] at hb1 <;> simp at hb1
  have hinj : Set.InjOn r (Finset.range 7680 : Set ℕ) := by
    intro p hp q hq hpq
    have hp' := Finset.mem_range.1 hp
    have hq' := Finset.mem_range.1 hq
    have hk : tkey (trec LF p) = tkey (trec LF q) := by
      rw [tkey_eq (trec LF p), tkey_eq (trec LF q)]
      have h1 := congrArg Prod.fst hpq
      have h2 := congrArg Prod.snd hpq
      rw [hr] at h1 h2
      exact congrArg₂ (fun x y => 256 * x + y) h1 h2
    rcases lt_trichotomy p q with h | h | h
    · exact absurd hk (ne_of_lt (hT.1 p q h hq'))
    · exact h
    · exact absurd hk (ne_of_gt (hT.1 q p h hp'))
  have himg : (Finset.range 7680).image r = S := by
    refine Finset.eq_of_subset_of_card_le (fun q hq => ?_) ?_
    · have hq' := Finset.mem_image.1 hq
      obtain ⟨p, hp, hpq⟩ := hq'
      rw [← hpq]
      exact hmem p (Finset.mem_range.1 hp)
    · rw [Finset.card_image_of_injOn hinj, Finset.card_range, hS, adm_card hmvf hPW hzl hcnt]
  have habS : (a, b) ∈ S := by
    rw [hS, Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]
    exact ⟨⟨hab.1, hab.2.1⟩, hab⟩
  rw [← himg] at habS
  have habI := Finset.mem_image.1 habS
  obtain ⟨p, hp, hpe⟩ := habI
  rw [hr] at hpe
  have hrr := rec_reach hleaf ((trec LF p >>> 16) &&& 63) p (Finset.mem_range.1 hp) rfl
  obtain ⟨ks, hks, hka, hkb⟩ := hrr
  refine ⟨ks, hks, ?_, ?_⟩
  · rw [← hka]
    exact (congrArg Prod.fst hpe).symm
  · rw [← hkb]
    exact (congrArg Prod.snd hpe).symm

theorem iform_expand
    (a b : Fin Tag.E8.rank → ℤ) (u w : Fin Tag.E8.rank → Fin Tag.E8.rank → ℤ) :
    iform (∑ m, a m • u m) (∑ n, b n • w n) = ∑ m, ∑ n, a m * b n * iform (u m) (w n) := by
  rw [iform_finset_sum_left]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [iform_finset_sum_right]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [iform_smul_left, iform_smul_right]
  ring

theorem gen_spec
    {vec : ℕ → Fin Tag.E8.rank → ℤ} {adj : ℕ → ℕ → Bool} {neg : ℕ → ℕ}
    {yc RTs : ℕ → ℕ} {V X Y NEG PAR PW t PG : ℕ}
    (hD : DatumRaw Tag.E8 240 vec (fun g v => fld (RTs g) 8 v) adj neg)
    (hroot : ∀ i < 240, rootOK 8 240 8 yc RTs V X Y NEG PAR i = true)
    (hX : ∀ v < 240, ∀ g < 240, (CFSG.TcRes.TK.dP 8 (fld X 256 v * fld Y 256 g) : ℤ) -
      dQ 8 (fld X 256 v * fld Y 256 g) = iform (vec v) (vec g))
    (hgen : genOK RTs X Y PAR PW t PG = true) :
    ∃ ψ : AddMonoid.End (Fin Tag.E8.rank → ℤ), (∀ x y, iform (ψ x) (ψ y) = iform x y) ∧
      (∀ g < 240, fld PG 8 g < 240 ∧ vec (fld PG 8 g) = ψ (vec g)) ∧
      ∀ g < 240, fld PG 8 (fld PW 8 g) = fld PW 8 (fld PG 8 g) := by
  have h8 : Tag.E8.rank = 8 := rfl
  obtain ⟨hiso, hpw, hcomm⟩ : isoOK X Y t = true ∧ pw8OK RTs t PAR PG = true ∧
      commOK PW PG = true := by
    have h := hgen
    simp only [genOK, andB_eq_true] at h
    exact ⟨h.1, h.2.1, h.2.2⟩
  have hI : ∀ a < 8, fld t 8 a < 240 ∧ ∀ b < 8,
      ipK8 X Y (fld t 8 a) (fld t 8 b) = ipK8 X Y a b := by
    intro a ha
    have h := Lane.allLt_iff.1 hiso a ha
    rw [strictB_eq, andB_eq_true, blt_eq_true] at h
    exact ⟨h.1, fun b hb => beq_eq_true.1 (Lane.allLt_iff.1 h.2 b hb)⟩
  have hform : ∀ m n : Fin Tag.E8.rank, iform (vec (fld t 8 m)) (vec (fld t 8 n)) =
      iform (vec m) (vec n) := by
    intro m n
    have hm : (m : ℕ) < 8 := m.2
    have hn : (n : ℕ) < 8 := n.2
    obtain ⟨htm, hmn⟩ := hI m hm
    have htn := (hI n hn).1
    have e1 := ipK8_int (hX _ htm _ htn) (iform_root_bound hD htm htn).1
    have e2 := ipK8_int (hX m (by omega) n (by omega)) (iform_root_bound hD (by omega) (by omega)).1
    rw [hmn n hn] at e1
    omega
  let ψ : AddMonoid.End (Fin Tag.E8.rank → ℤ) :=
    { toFun := fun x => ∑ m, x m • vec (fld t 8 m)
      map_zero' := by simp
      map_add' := fun x y => by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib] }
  have hψ : ∀ x, ψ x = ∑ m, x m • vec (fld t 8 m) := fun _ => rfl
  have hx : ∀ x : Fin Tag.E8.rank → ℤ, x = ∑ m, x m • vec m := by
    intro x
    funext k
    simp only [hD.simple, Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite,
      mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have hiso' : ∀ x y, iform (ψ x) (ψ y) = iform x y := by
    intro x y
    conv_rhs => rw [hx x, hx y]
    rw [hψ, hψ, iform_expand, iform_expand]
    simp only [hform]
  have hψm : ∀ m : Fin Tag.E8.rank, ψ (vec m) = vec (fld t 8 m) := by
    intro m
    rw [hψ, hD.simple]
    simp only [Pi.single_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ,
      if_true]
  refine ⟨ψ, hiso', pw8_spec hD hroot hpw ψ hiso' hψm fun m hm => (hI m hm).1, fun g hg => ?_⟩
  exact beq_eq_true.1 (Lane.allLt_iff.1 hcomm g hg)

end CFSG.KC.TcRes

end
