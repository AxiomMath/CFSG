module

public import Certificates.Data.Kernel.HOrb
public import CFSG.Certificates.Kernel.LceSTabSound
import CFSG.Certificates.Kernel.LceSP.Main
import Mathlib.Tactic.Group
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.Certificates.HO

open CFSG.KC CFSG.KC.LceS CFSG.KC.HOrb CFSG.Certificates.LCE

open CFSG.Certificates.LceP in
private theorem hwalk_spec {G : Type*} [Group G] (gen : ℕ → G) (H : Subgroup G) {blk : ℕ → ℕ}
    {rep : ℕ → G} {s W ft nf n : ℕ} {a : G} (hrefs : RefsOK gen H blk rep nf) (hft : n ≤ ft) :
    ∀ k ≤ n, ∀ R st, WI gen H rep s W ft a (n - k) st →
      WI gen H rep s W ft a n (hwalk blk nf k R st)
  | 0, _, R, st, hI => by
    change WI gen H rep s W ft a n st
    simpa using hI
  | k + 1, hk, R, st, hI => by
    change WI gen H rep s W ft a n (CFSG.KC.Loop.strictN (refStep blk nf (Nat.land R 4294967295) st)
      (hwalk blk nf k (Nat.shiftRight R 32)))
    rw [CFSG.Certificates.LceP.strictN_eq]
    apply hwalk_spec gen H hrefs hft k (by omega)
    rw [show n - k = n - (k + 1) + 1 by omega]
    exact WI_ref gen H hI (by omega) hrefs

open CFSG.Certificates.LceP in
theorem walkTo_sound {G : Type*} [Group G] (gen : ℕ → G) (H : Subgroup G)
    {blk WT RT ST : ℕ → ℕ} {INV INV8 L nC m Hs nR nS nf S0 S1 : ℕ} {Cs : List ℕ}
    (h : factsOk blk WT RT ST INV INV8 L nC m Hs nR nS nf S0 S1 Cs = true)
    (hRT : ∀ r < nR, bval gen (wWord (RT r)) (wLen (RT r)) = 1)
    (hST : ∀ j < nS, bval gen (wWord (ST j)) (wLen (ST j)) ∈ H) :
    ∃ rep : ℕ → G, rep 0 = 1 ∧ ∀ w x R y, x < 2 ^ 20 → walkTo blk nf w x R y = true →
      rep x * bval gen (wWord w) (wLen w) * (rep y)⁻¹ ∈ H := by
  unfold factsOk at h
  obtain ⟨hinv, h⟩ := (andB_iff _ _).1 h
  obtain ⟨hwords, h⟩ := (andB_iff _ _).1 h
  obtain ⟨hhints, h⟩ := (andB_iff _ _).1 h
  obtain ⟨hm, h⟩ := (andB_iff _ _).1 h
  obtain ⟨hper, h⟩ := (andB_iff _ _).1 h
  obtain ⟨hnorm, h⟩ := (andB_iff _ _).1 h
  obtain ⟨hnC, h⟩ := (andB_iff _ _).1 h
  obtain ⟨hnf, h⟩ := (andB_iff _ _).1 h
  obtain ⟨hS0, h⟩ := (andB_iff _ _).1 h
  obtain ⟨hS1, hrun⟩ := (andB_iff _ _).1 h
  have hnC' : nC ≤ 1048576 := Nat.le_of_ble_eq_true hnC
  have hnf' : nf < 4294967296 := blt_true hnf
  have hm' : 0 < m := blt_true hm
  have hS0' : S0 = mkS 0 1 := Nat.eq_of_beq_eq_true hS0
  have hS1' : S1 = mkS nf nC := Nat.eq_of_beq_eq_true hS1
  have hrun' := Nat.eq_of_beq_eq_true hrun
  have hWT : ∀ k < 65536, WOK gen H (WT k) := by
    intro k hk
    rw [wtPer_spec hper k hk]
    obtain ⟨h2, h3⟩ := words_spec gen hinv hwords hhints hRT (relsNorm_spec hnorm) _
      (Nat.mod_lt _ hm')
    refine ⟨h2, fun hk3 => (Subgroup.closure_le H).2 ?_ (h3 hk3)⟩
    rintro _ ⟨j, hj, rfl⟩
    exact hST j hj
  have hG0 : FGood gen H ⊤ blk INV nC S0 := by
    rw [hS0']
    exact FGood_mkS gen H ⊤ (by norm_num) le_rfl (fun _ => FInv_zero gen H ⊤ blk INV nC 1)
  have hG1 := runFacts_good gen H ⊤ hinv hWT (fun _ _ => Subgroup.mem_top _) Cs S0 hG0
  rw [hrun', hS1'] at hG1
  have hF : ∃ rep : ℕ → G, rep 0 = 1 ∧ ∀ rep' : ℕ → G, (∀ k < nC, rep' k = rep k) →
      RefsOK gen H blk rep' nf := by
    rcases hG1 with h0 | ⟨-, hF⟩
    · rw [mkS_eq nC hnf'] at h0
      have h0' : nf = 0 := by omega
      subst h0'
      exact ⟨fun _ => 1, rfl, fun _ _ h hh => absurd hh (Nat.not_lt_zero h)⟩
    rw [sI_eq, sN_eq, mkS_eq nC hnf'] at hF
    have e1 : (nf + nC * 4294967296) % 4294967296 = nf := by omega
    have e2 : (nf + nC * 4294967296) / 4294967296 = nC := by omega
    rw [e1, e2] at hF
    obtain ⟨hrecs, rep, hrep0, -, hfacts⟩ := hF
    exact ⟨rep, hrep0, fun rep' hag h hh =>
      ⟨hfacts rep' hag h hh, (lv_fic gen blk hinv (hrecs h hh)).1⟩⟩
  obtain ⟨rep, hrep0, hrefs⟩ := hF
  refine ⟨fun y => rep (y % 1048576), by simpa using hrep0, fun w x R y hx hw => ?_⟩
  have hR := hrefs (fun y => rep (y % 1048576)) (fun k hk => by
    simp only [Nat.mod_eq_of_lt (show k < 1048576 by omega)])
  have h0 : WI gen H (fun y => rep (y % 1048576)) x (wWord w) (wLen w) 1 (wLen w - wLen w)
      (wStart x (wWord w)) := by
    rw [Nat.sub_self]
    right
    refine ⟨x, hx, ?_, ?_⟩
    · unfold wStart
      rw [lor20 _ hx, pow_zero, Nat.div_one]
      ring
    · refine ⟨fun _ => Or.inl (Nat.zero_le _), fun _ => ?_⟩
      rw [bv_zero, mul_one, mul_inv_cancel]
      exact H.one_mem
  have hn := hwalk_spec gen H hR le_rfl (wLen w) le_rfl R _ h0
  have hw' : hwalk blk nf (wLen w) R (wStart x (wWord w)) = y + 1048576 :=
    Nat.eq_of_beq_eq_true hw
  rw [hw'] at hn
  rcases hn with hd | ⟨cur, hcur, hst, hX⟩
  · omega
  · have hc : cur = y % 1048576 := by omega
    have hX' := hX.2 (Or.inl le_rfl)
    rw [hc] at hX'
    simp only [Nat.mod_mod] at hX'
    exact hX'

theorem wLet_eq (W i : ℕ) : wLet W i = W / 256 ^ i % 256 := by
  change W >>> (8 * i) &&& 255 = _
  have h : (255 : ℕ) = 2 ^ 8 - 1 := by norm_num
  rw [h, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, pow_mul]
  norm_num

theorem byte_eq (W i : ℕ) : CFSG.KC.HOrb.byte W i = W / 256 ^ i % 256 := wLet_eq W i

theorem two_pow_eight_mul (k : ℕ) : 2 ^ (8 * k) = 256 ^ k := by
  rw [pow_mul]
  norm_num

theorem byte_add_high {W B i n : ℕ} (hi : i < n) :
    (W + B * 256 ^ n) / 256 ^ i % 256 = W / 256 ^ i % 256 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hi
  have e : B * 256 ^ (i + d + 1) = 256 ^ i * (256 * (B * 256 ^ d)) := by ring
  rw [e, Nat.add_mul_div_left _ _ (by positivity), Nat.add_mul_mod_self_left]

theorem byte_concat {A B p i : ℕ} (hA : A < 256 ^ p) :
    (A + B * 256 ^ p) / 256 ^ i % 256 =
      if i < p then A / 256 ^ i % 256 else B / 256 ^ (i - p) % 256 := by
  split_ifs with hi
  · exact byte_add_high hi
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_lt hi)
    have e : (A + B * 256 ^ p) / 256 ^ (p + j) = B / 256 ^ j := by
      rw [pow_add, ← Nat.div_div_eq_div_mul, Nat.mul_comm B, Nat.add_mul_div_left _ _ (by positivity),
        Nat.div_eq_of_lt hA, Nat.zero_add]
    rw [e, Nat.add_sub_cancel_left]

theorem bval_eq {G : Type*} [Group G] (gen : ℕ → G) (W n : ℕ) :
    bval gen W n = ((List.range n).map fun i => letV gen (W / 256 ^ i % 256)).prod := by
  simp only [bval, wLet_eq]

theorem bval_concat {G : Type*} [Group G] (gen : ℕ → G) {A B p q : ℕ} (hA : A < 256 ^ p) :
    bval gen (A + B * 256 ^ p) (p + q) = bval gen A p * bval gen B q := by
  rw [bval_eq, bval_eq, bval_eq, List.range_add, List.map_append, List.prod_append, List.map_map]
  congr 2
  · apply List.map_congr_left
    intro i hi
    rw [List.mem_range] at hi
    rw [byte_concat hA]
    simp only [hi, ↓reduceIte]
  · apply List.map_congr_left
    intro j _
    have hj : ¬p + j < p := by omega
    simp only [Function.comp_apply, byte_concat hA, hj, ↓reduceIte, Nat.add_sub_cancel_left]

theorem bval_zero {G : Type*} [Group G] (gen : ℕ → G) (W : ℕ) : bval gen W 0 = 1 := by
  simp [bval]

theorem bval_one {G : Type*} [Group G] (gen : ℕ → G) {c : ℕ} (hc : c < 256) :
    bval gen c 1 = letV gen c := by
  simp [bval_eq, Nat.mod_eq_of_lt hc]

theorem bval_congr {G : Type*} [Group G] (gen : ℕ → G) {W W' n : ℕ}
    (h : ∀ i < n, W / 256 ^ i % 256 = W' / 256 ^ i % 256) : bval gen W n = bval gen W' n := by
  rw [bval_eq, bval_eq]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [h i (List.mem_range.mp hi)]

@[expose] def byteFold (f : ℕ → ℕ) (k : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0 (fun j acc => acc ||| (f j <<< (8 * j))) k

theorem byteFold_spec (f : ℕ → ℕ) (hf : ∀ j, f j < 256) :
    ∀ k, byteFold f k < 256 ^ k ∧ ∀ i < k, byteFold f k / 256 ^ i % 256 = f i
  | 0 => ⟨by simp [byteFold], fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | k + 1 => by
    obtain ⟨hlt, hb⟩ := byteFold_spec f hf k
    have hlt2 : byteFold f k < 2 ^ (8 * k) := by rw [two_pow_eight_mul]; exact hlt
    have e : byteFold f (k + 1) = byteFold f k + f k * 256 ^ k := by
      change byteFold f k ||| (f k <<< (8 * k)) = _
      rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt hlt2, Nat.shiftLeft_eq,
        two_pow_eight_mul, Nat.add_comm]
    rw [e]
    refine ⟨?_, fun i hi => ?_⟩
    · have := hf k
      calc byteFold f k + f k * 256 ^ k < 256 ^ k + f k * 256 ^ k := by omega
        _ = (f k + 1) * 256 ^ k := by ring
        _ ≤ 256 * 256 ^ k := Nat.mul_le_mul_right _ (by omega)
        _ = 256 ^ (k + 1) := by ring
    · rw [byte_concat hlt]
      split_ifs with h
      · exact hb i h
      · have : i = k := by omega
        subst this
        simp [Nat.mod_eq_of_lt (hf i)]

theorem bval_byteFold {G : Type*} [Group G] (gen : ℕ → G) (f : ℕ → ℕ) (hf : ∀ j, f j < 256)
    (k : ℕ) : bval gen (byteFold f k) k = ((List.range k).map fun i => letV gen (f i)).prod := by
  rw [bval_eq]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [(byteFold_spec f hf k).2 i (List.mem_range.mp hi)]

set_option maxRecDepth 100000 in
theorem xor_one_cases : ∀ c < 256, c ^^^ 1 = if c % 2 = 0 then c + 1 else c - 1 := by decide

theorem letV_xor_one {G : Type*} [Group G] (gen : ℕ → G) {c : ℕ} (hc : c < 254) :
    letV gen (c ^^^ 1) = (letV gen c)⁻¹ := by
  rw [xor_one_cases c (by omega)]
  unfold letV
  split_ifs <;> first | omega | (simp_all; congr 1; omega)

theorem map_range_rev {α : Type*} (g : ℕ → α) :
    ∀ n, (List.range n).map (fun k => g (n - 1 - k)) = ((List.range n).map g).reverse
  | 0 => rfl
  | n + 1 => by
    conv_lhs => rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    conv_rhs => rw [List.range_succ, List.map_append, List.reverse_append]
    rw [← map_range_rev g n]
    simp only [Function.comp_def, List.map_cons, List.map_nil, List.reverse_cons,
      List.reverse_nil, List.nil_append, List.singleton_append]
    congr 1
    apply List.map_congr_left
    intro k _
    congr 1
    omega

theorem andB_eq (a b : Bool) : CFSG.KC.andB a b = (a && b) := by cases a <;> rfl

theorem lettersBelow_iff (W n b : ℕ) :
    lettersBelow W n b = true ↔ ∀ i < n, wLet W i < b := by
  induction n with
  | zero => simp [lettersBelow]
  | succ n ih =>
    change andB (lettersBelow W n b) (Nat.blt (wLet W n) b) = true ↔ _
    rw [andB_eq, Bool.and_eq_true, ih, Nat.blt_eq]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | rfl
      · exact h1 i h
      · exact h2
    · intro h
      exact ⟨fun i hi => h i (by omega), h n (by omega)⟩

theorem entOK_iff (e b n : ℕ) : entOK e b n = true ↔
    wWord e < 2 ^ (8 * wLen e) ∧ wLen e ≤ n ∧ ∀ i < wLen e, wLet (wWord e) i < b := by
  change andB (Nat.blt _ _) (andB (Nat.ble _ _) _) = true ↔ _
  rw [andB_eq, andB_eq, Bool.and_eq_true, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq,
    lettersBelow_iff]
  change wWord e < 1 <<< (8 * wLen e) ∧ _ ↔ _
  rw [Nat.shiftLeft_eq, Nat.one_mul]

theorem wLen_mk (n X : ℕ) (hn : n < 1024) : wLen (4 * n + X <<< 12) = n := by
  change (4 * n + X <<< 12) >>> 2 &&& 1023 = n
  have h : (1023 : ℕ) = 2 ^ 10 - 1 := by norm_num
  rw [h, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  norm_num
  omega

theorem wWord_mk (n X : ℕ) (hn : n < 1024) : wWord (4 * n + X <<< 12) = X := by
  change (4 * n + X <<< 12) >>> 12 = X
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  norm_num
  omega

theorem bval_withSent {G : Type*} [Group G] (gen : ℕ → G) (e : ℕ) :
    bval gen (wWord (withSent e)) (wLen (withSent e)) = bval gen (wWord e) (wLen e) := by
  have hs : withSent e = e + 4096 * 256 ^ wLen e := by
    change e + 1 <<< (12 + 8 * wLen e) = _
    rw [Nat.shiftLeft_eq, Nat.one_mul, pow_add, two_pow_eight_mul]
    norm_num
  have hL : wLen (withSent e) = wLen e := by
    rw [hs]
    change (e + 4096 * 256 ^ wLen e) >>> 2 &&& 1023 = e >>> 2 &&& 1023
    have h : (1023 : ℕ) = 2 ^ 10 - 1 := by norm_num
    rw [h, Nat.and_two_pow_sub_one_eq_mod, Nat.and_two_pow_sub_one_eq_mod,
      Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
    norm_num
    omega
  have hW : wWord (withSent e) = wWord e + 1 * 256 ^ wLen e := by
    rw [hs]
    change (e + 4096 * 256 ^ wLen e) >>> 12 = e >>> 12 + _
    rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
    norm_num
    omega
  rw [hL, hW]
  exact bval_congr gen fun i hi => byte_add_high hi

theorem invW_eq (W n : ℕ) :
    CFSG.KC.HOrb.invW W n = byteFold (fun k => CFSG.KC.HOrb.byte W (n - 1 - k) ^^^ 1) n := rfl

theorem byte_xor_lt (W k : ℕ) : CFSG.KC.HOrb.byte W k ^^^ 1 < 256 := by
  rw [byte_eq]
  have := Nat.mod_lt (W / 256 ^ k) (by norm_num : 0 < 256)
  have h := xor_one_cases (W / 256 ^ k % 256) this
  split_ifs at h <;> omega

theorem invEnt_eq (e : ℕ) : invEnt e = 4 * wLen e + CFSG.KC.HOrb.invW (wWord e) (wLen e) <<< 12 :=
  rfl

theorem bval_invW {G : Type*} [Group G] (gen : ℕ → G) {W n : ℕ}
    (hl : ∀ i < n, wLet W i < 254) :
    bval gen (CFSG.KC.HOrb.invW W n) n = (bval gen W n)⁻¹ := by
  rw [invW_eq, bval_byteFold gen (fun k => CFSG.KC.HOrb.byte W (n - 1 - k) ^^^ 1)
    (fun k => byte_xor_lt W _), bval, List.prod_inv_reverse, List.map_map]
  change _ = ((List.range n).map fun i => (letV gen (wLet W i))⁻¹).reverse.prod
  rw [← map_range_rev (fun i => (letV gen (wLet W i))⁻¹) n]
  congr 1
  apply List.map_congr_left
  intro k hk
  have hk' := List.mem_range.mp hk
  rw [← letV_xor_one gen (hl _ (by omega))]
  rfl

theorem bval_invEnt {G : Type*} [Group G] (gen : ℕ → G) {e : ℕ}
    (he : entOK e (nat_lit 254) (nat_lit 1023) = true) :
    entOK (invEnt e) (nat_lit 254) (nat_lit 1023) = true ∧ wLen (invEnt e) = wLen e ∧
      bval gen (wWord (invEnt e)) (wLen (invEnt e)) = (bval gen (wWord e) (wLen e))⁻¹ := by
  obtain ⟨-, hn, hl⟩ := (entOK_iff _ _ _).mp he
  have hn : wLen e ≤ 1023 := hn
  have hl : ∀ i < wLen e, wLet (wWord e) i < 254 := hl
  have hn' : wLen e < 1024 := by omega
  have hL : wLen (invEnt e) = wLen e := by rw [invEnt_eq, wLen_mk _ _ hn']
  have hW : wWord (invEnt e) = CFSG.KC.HOrb.invW (wWord e) (wLen e) := by
    rw [invEnt_eq, wWord_mk _ _ hn']
  have hspec := byteFold_spec (fun k => CFSG.KC.HOrb.byte (wWord e) (wLen e - 1 - k) ^^^ 1)
    (fun k => byte_xor_lt (wWord e) _) (wLen e)
  refine ⟨?_, hL, ?_⟩
  · rw [entOK_iff, hL, hW, invW_eq, two_pow_eight_mul]
    refine ⟨hspec.1, hn, fun i hi => ?_⟩
    change _ < 254
    rw [wLet_eq, hspec.2 i hi, byte_eq]
    have h1 := hl (wLen e - 1 - i) (by omega)
    rw [wLet_eq] at h1
    have h2 := xor_one_cases _ (Nat.mod_lt (wWord e / 256 ^ (wLen e - 1 - i)) (by norm_num))
    split_ifs at h2 <;> omega
  · rw [hL, hW]
    exact bval_invW gen hl

theorem bval_commEnt {G : Type*} [Group G] (gen : ℕ → G) {e : ℕ}
    (he : entOK e (nat_lit 254) (nat_lit 510) = true) :
    bval gen (wWord (commEnt e)) (wLen (commEnt e)) =
      (gen 0)⁻¹ * (bval gen (wWord e) (wLen e))⁻¹ * gen 0 * bval gen (wWord e) (wLen e) := by
  obtain ⟨hWlt, hn, hl⟩ := (entOK_iff _ _ _).mp he
  have hn : wLen e ≤ 510 := hn
  have hl : ∀ i < wLen e, wLet (wWord e) i < 254 := hl
  set n := wLen e
  set W := wWord e
  set V := CFSG.KC.HOrb.invW W n
  have hV : V < 256 ^ n := (byteFold_spec (fun k => CFSG.KC.HOrb.byte W (n - 1 - k) ^^^ 1)
    (fun k => byte_xor_lt W _) n).1
  have hW : W < 256 ^ n := by rwa [two_pow_eight_mul] at hWlt
  have hX : 1 ||| (V <<< 8 ||| W <<< (8 * (n + 2))) = 1 + (V + (0 + W * 256 ^ 1) * 256 ^ n) * 256 ^ 1 := by
    have h1 : V <<< 8 < 2 ^ (8 * (n + 2)) := by
      rw [Nat.shiftLeft_eq, two_pow_eight_mul]
      calc V * 2 ^ 8 < 256 ^ n * 256 := by omega
        _ ≤ 256 ^ (n + 2) := by rw [pow_add]; omega
    rw [Nat.or_comm (V <<< 8), ← Nat.shiftLeft_add_eq_or_of_lt h1]
    have h2 : (1 : ℕ) < 2 ^ 8 := by norm_num
    have e8 : W <<< (8 * (n + 2)) + V <<< 8 = (W * 256 ^ (n + 1) + V) <<< 8 := by
      rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.shiftLeft_eq, two_pow_eight_mul]
      ring
    rw [e8, Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt h2, Nat.shiftLeft_eq]
    ring
  have hc : commEnt e = 4 * (2 * n + 2) + (1 ||| (V <<< 8 ||| W <<< (8 * (n + 2)))) <<< 12 := by
    change 4 * (2 * n + 2) + (1 ||| (V <<< 8 ||| W <<< (8 * (n + 2)))) <<< 12 = _
    rfl
  have hn2 : 2 * n + 2 < 1024 := by omega
  rw [hc, wLen_mk _ _ hn2, wWord_mk _ _ hn2, hX]
  have hs : 2 * n + 2 = 1 + (n + (1 + n)) := by omega
  rw [hs, bval_concat gen (by norm_num : (1 : ℕ) < 256 ^ 1), bval_concat gen hV,
    bval_concat gen (by norm_num : (0 : ℕ) < 256 ^ 1), bval_one gen (by norm_num : (1 : ℕ) < 256),
    bval_one gen (by norm_num : (0 : ℕ) < 256), bval_invW gen hl]
  simp only [letV]
  norm_num
  group

theorem bval_powEnt {G : Type*} [Group G] (gen : ℕ → G) {e m : ℕ}
    (he : wWord e < 2 ^ (8 * wLen e)) (hm : m * wLen e < 1024) :
    bval gen (wWord (powEnt e m)) (wLen (powEnt e m)) = (bval gen (wWord e) (wLen e)) ^ m := by
  set n := wLen e
  set W := wWord e
  have hW : W < 256 ^ n := by rwa [two_pow_eight_mul] at he
  set P : ℕ → ℕ := fun m => Nat.rec (motive := fun _ => ℕ) 0
    (fun k acc => acc ||| (W <<< (8 * (n * k)))) m with hPdef
  have hp : powEnt e m = 4 * (m * n) + P m <<< 12 := rfl
  have key : ∀ k, P k < 256 ^ (n * k) ∧ bval gen (P k) (n * k) = (bval gen W n) ^ k := by
    intro k
    induction k with
    | zero => exact ⟨by simp [hPdef], by simp [bval_zero]⟩
    | succ k ih =>
      obtain ⟨hlt, hv⟩ := ih
      have hlt2 : P k < 2 ^ (8 * (n * k)) := by rw [two_pow_eight_mul]; exact hlt
      have e1 : P (k + 1) = P k + W * 256 ^ (n * k) := by
        change P k ||| (W <<< (8 * (n * k))) = _
        rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt hlt2, Nat.shiftLeft_eq,
          two_pow_eight_mul, Nat.add_comm]
      rw [e1]
      refine ⟨?_, ?_⟩
      · calc P k + W * 256 ^ (n * k) < 256 ^ (n * k) + W * 256 ^ (n * k) := by omega
          _ = (W + 1) * 256 ^ (n * k) := by ring
          _ ≤ 256 ^ n * 256 ^ (n * k) := Nat.mul_le_mul_right _ (by omega)
          _ = 256 ^ (n * (k + 1)) := by ring
      · rw [Nat.mul_succ, bval_concat gen hlt, hv, pow_succ]
  have hmn : m * n < 1024 := hm
  rw [hp, wLen_mk _ _ hmn, wWord_mk _ _ hmn, Nat.mul_comm m n]
  exact (key m).2

end CFSG.Certificates.HO

end
