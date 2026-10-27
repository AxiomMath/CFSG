module

public import CFSG.Certificates.Kernel.SporSch.HNXCnt.Base
public import CFSG.Certificates.Kernel.Orders.HN.Checks.K
public import CFSG.Certificates.Kernel.Spor.OrdSound
import all CFSG.Certificates.Kernel.Spor.OrdSound
import CFSG.Certificates.Kernel.Spor.PackFld
public import CFSG.Certificates.Kernel.Spor.Loops
public import Certificates.Data.Kernel.SporSch.HNXOrb
public import Certificates.Data.Kernel.SporSch.HNXPrim

public section

namespace CFSG.KS.SporSch.HNXP

open CFSG.KC.Enum CFSG.KC.LL CFSG.KC.LL.HNX CFSG.KS.SporSch Finset

theorem lanes_rec_inv {P : Nat → Nat → Prop} {x : Nat} {F : Nat → Nat → Nat} {N : Nat}
    (h0 : P 0 x) (hs : ∀ i < N, ∀ acc, P i acc → P (i + 1) (F i acc)) :
    ∀ n ≤ N, P n (Nat.rec (motive := fun _ => Nat) x F n) := by
  intro n
  induction n with
  | zero => intro _; exact h0
  | succ n ih => intro hn; exact hs n (by omega) _ (ih (by omega))

theorem lanes_rec_add (F : Nat → Nat) : ∀ n,
    Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun k acc => Nat.add acc (F k)) n =
      ∑ k ∈ range n, F k
  | 0 => rfl
  | n + 1 => by
    rw [Finset.sum_range_succ, ← lanes_rec_add F n]
    rfl

theorem lanes_lt {w n : Nat} {g : Nat → Nat} (hg : ∀ t < n, g t < 2 ^ w) :
    ∑ t ∈ range n, g t * 2 ^ (w * t) < 2 ^ (w * n) :=
  CFSG.KS.Ord.pk_lt hg

theorem lanes_lane {w n s : Nat} {g : Nat → Nat} (hg : ∀ t < n, g t < 2 ^ w) (hs : s < n) :
    (∑ t ∈ range n, g t * 2 ^ (w * t)) / 2 ^ (w * s) % 2 ^ w = g s :=
  CFSG.KS.Ord.lane_pk hg hs

theorem lanes_or_single {w n r0 v e : Nat} {h : Nat → Nat} (hw : 0 < w)
    (hh : ∀ r < n, h r < 2 ^ w) (h0 : h r0 = 0) (hr0 : r0 < n) (hv : v < 2 ^ w)
    (he : e = w * r0) :
    Nat.lor (∑ r ∈ range n, h r * 2 ^ (w * r)) (Nat.shiftLeft v e) =
      ∑ r ∈ range n, (if r = r0 then v else h r) * 2 ^ (w * r) := by
  subst he
  have hb : ∀ r < n, (if r = r0 then v else h r) < 2 ^ w := fun r hr => by
    split
    · exact hv
    · exact hh r hr
  refine CFSG.KS.Ord.pk_of_fld hw (CFSG.KS.PackFld.fld_congr
    (CFSG.KS.PackFld.fld_or (CFSG.KS.Ord.fld_pk hh)
      (CFSG.KS.PackFld.fld_shl r0 (CFSG.KS.PackFld.fld_one hv))) fun t => ?_) hb
  by_cases ht : t < n
  · by_cases htr : t = r0
    · subst htr
      simp [ht, h0]
    · have h1 : t - r0 ≠ 0 ∨ ¬ r0 ≤ t := by omega
      rcases h1 with h1 | h1 <;> simp [ht, htr, h1]
  · have htr : t ≠ r0 := by omega
    have h1 : t - r0 ≠ 0 := by omega
    simp [ht, htr, h1]

theorem lanes_sum_ext {m M : Nat} (hm : m ≤ M) (F : Nat → Nat) :
    ∑ r ∈ range M, (if r < m then F r else 0) = ∑ r ∈ range m, F r := by
  obtain ⟨e, rfl⟩ : ∃ e, M = m + e := ⟨M - m, by omega⟩
  rw [Finset.sum_range_add]
  have h2 : ∑ x ∈ range e, (if m + x < m then F (m + x) else 0) = 0 :=
    Finset.sum_eq_zero fun x _ => if_neg (by omega)
  rw [h2, Nat.add_zero]
  exact Finset.sum_congr rfl fun r hr => if_pos (Finset.mem_range.1 hr)

theorem lanes_dm (x a b c : Nat) (h : b + c ≤ a) : x % 2 ^ a / 2 ^ b % 2 ^ c = x / 2 ^ b % 2 ^ c := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  by_cases hi : i < c
  · have : i + b < a := by omega
    simp [hi, this]
  · simp [hi]

theorem row_lane (Y r l : Nat) (hl : l < 133) :
    fldW Y (1729 * r) 1729 / 2 ^ (13 * l) % 2 ^ 13 = Y / 2 ^ (1729 * r + 13 * l) % 2 ^ 13 := by
  rw [fldW_eq, lanes_dm _ _ _ _ (by omega), Nat.div_div_eq_div_mul, ← Nat.pow_add]

theorem lanes_rows (m : Nat) (G : Nat → Nat) :
    ∑ u ∈ range (133 * m), G u * 2 ^ (13 * u) =
      ∑ i ∈ range m, ∑ j ∈ range 133, G (133 * i + j) * 2 ^ (1729 * i + 13 * j) := by
  have := CFSG.KS.Ord.pk_rows 13 133 G m
  unfold CFSG.KS.Ord.pk at this
  rw [this]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  congr 2
  ring

theorem lanes_rec_or {f : Nat → Nat} (hf : ∀ r < 64, f r < 2 ^ 1729) : ∀ c ≤ 64,
    Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun r acc => Nat.lor acc (Nat.shiftLeft (f r) (Nat.mul (nat_lit 1729) r))) c =
      ∑ r ∈ range 64, (if r < c then f r else 0) * 2 ^ (1729 * r) := by
  refine lanes_rec_inv (P := fun c acc => acc = ∑ r ∈ range 64, (if r < c then f r else 0) *
    2 ^ (1729 * r)) ?_ ?_
  · exact (Finset.sum_eq_zero fun r _ => by rw [if_neg (Nat.not_lt_zero r), Nat.zero_mul]).symm
  · intro i hi acc hacc
    rw [hacc]
    refine (lanes_or_single (r0 := i) (by omega) (fun r hr => by
      split
      · exact hf r hr
      · exact Nat.two_pow_pos _) (if_neg (Nat.lt_irrefl i)) hi (hf i hi) rfl).trans ?_
    refine Finset.sum_congr rfl fun r _ => ?_
    by_cases h : r = i
    · subst h; simp
    · have : (r < i + 1) = (r < i) := propext (by omega)
      simp [h, this]

theorem leafA_eq {CM3 M : Nat} (hc : constsOK CM3 M = true) (L c : Nat) (hc64 : c ≤ 64) :
    leafA L 464 c M = ∑ r ∈ Finset.range 64,
      (if r < c then L / 2 ^ (464 * r) % 2 ^ 399 else 0) * 2 ^ (1729 * r) := by
  unfold constsOK at hc
  have hM : M = Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 399)) (nat_lit 1) :=
    Nat.eq_of_beq_eq_true ((CFSG.KS.bAnd_iff _ _).1 hc).2
  subst hM
  unfold leafA
  refine (lanes_rec_or (f := fun r => fldW L (Nat.mul 464 r) 399) (fun r _ => by
    rw [fldW_eq]; exact Nat.lt_of_lt_of_le (Nat.mod_lt _ (by positivity))
      (Nat.pow_le_pow_right (by omega) (by omega))) c hc64).trans ?_
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [fldW_eq]
  rfl

theorem lanes_CM3 {CM3 M : Nat} (hc : constsOK CM3 M = true) :
    CM3 = ∑ r ∈ range 64, 7 * 2 ^ (1729 * r) := by
  unfold constsOK at hc
  have h := Nat.eq_of_beq_eq_true ((CFSG.KS.bAnd_iff _ _).1 hc).1
  rw [h]
  refine (lanes_rec_or (f := fun _ => 7) (fun _ _ => by
    exact Nat.lt_of_lt_of_le (by norm_num : 7 < 2 ^ 3) (Nat.pow_le_pow_right (by omega) (by omega)))
    64 le_rfl).trans ?_
  refine Finset.sum_congr rfl fun r hr => ?_
  rw [if_pos (Finset.mem_range.1 hr)]

theorem lanes_rec_eq {x N : Nat} {F : Nat → Nat → Nat} {S : Nat → Nat} (h0 : x = S 0)
    (hs : ∀ i < N, ∀ acc, acc = S i → F i acc = S (i + 1)) :
    ∀ n ≤ N, Nat.rec (motive := fun _ => Nat) x F n = S n :=
  lanes_rec_inv (P := fun n acc => acc = S n) h0 hs

theorem lanes_rec_succ (x : Nat) (F : Nat → Nat → Nat) (n : Nat) :
    Nat.rec (motive := fun _ => Nat) x F (n + 1) = F n (Nat.rec (motive := fun _ => Nat) x F n) :=
  rfl

theorem lanes_ent_lt (W j k : Nat) : ent13 W j k < 2 ^ 13 := Nat.mod_lt _ (by positivity)

theorem lanes_trM_inner (W i : Nat) (hi : i < 133) : ∀ j ≤ 133,
    Nat.rec (motive := fun _ => Nat) (∑ u ∈ range (133 * 133),
      (if u % 133 < i then ent13 W (u % 133) (u / 133) else 0) * 2 ^ (13 * u))
      (fun j acc2 => Nat.lor acc2 (Nat.shiftLeft (fldW (fldW W (Nat.mul (nat_lit 1729) i)
        (nat_lit 1729)) (Nat.mul (nat_lit 13) j) (nat_lit 13))
          (Nat.add (Nat.mul (nat_lit 1729) j) (Nat.mul (nat_lit 13) i)))) j =
      ∑ u ∈ range (133 * 133),
        (if u % 133 < i ∨ (u % 133 = i ∧ u / 133 < j) then ent13 W (u % 133) (u / 133) else 0) *
          2 ^ (13 * u) := by
  have hE : ∀ u, ent13 W (u % 133) (u / 133) < 2 ^ 13 := fun u => lanes_ent_lt _ _ _
  intro n
  induction n with
  | zero =>
    intro _
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [if_congr (show u % 133 < i ↔ (u % 133 < i ∨ (u % 133 = i ∧ u / 133 < 0)) by omega) rfl rfl]
  | succ j ih =>
    intro hj'
    have hj : j < 133 := by omega
    simp only [lanes_rec_succ]
    rw [ih (by omega)]
    have hv : fldW (fldW W (Nat.mul 1729 i) 1729) (Nat.mul 13 j) 13 = ent13 W i j := by
      rw [fldW_eq]
      exact row_lane W i j hj
    refine (lanes_or_single (w := 13) (n := 133 * 133) (r0 := 133 * j + i) (by omega)
      (fun r _ => by split; exact hE r; exact Nat.two_pow_pos _) (if_neg (by omega))
      (by omega) (hv ▸ lanes_ent_lt W i j) (by show 1729 * j + 13 * i = _; ring)).trans ?_
    refine Finset.sum_congr rfl fun u _ => ?_
    by_cases hu : u = 133 * j + i
    · subst hu
      have h1 : (133 * j + i) % 133 = i := by omega
      have h2 : (133 * j + i) / 133 = j := by omega
      rw [if_pos rfl, if_pos (by omega), h1, h2, hv]
    · rw [if_neg hu]
      exact congrArg (· * 2 ^ (13 * u)) (if_congr (by omega) rfl rfl)

theorem lanes_trM_outer (W : Nat) : ∀ n ≤ 133,
    Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun i acc => CFSG.KC.Loop.strictN acc (fun s => CFSG.KC.Loop.strictN
        (fldW W (Nat.mul (nat_lit 1729) i) (nat_lit 1729)) (fun row =>
          Nat.rec (motive := fun _ => Nat) s
            (fun j acc2 => Nat.lor acc2 (Nat.shiftLeft (fldW row (Nat.mul (nat_lit 13) j) (nat_lit 13))
              (Nat.add (Nat.mul (nat_lit 1729) j) (Nat.mul (nat_lit 13) i)))) (nat_lit 133)))) n =
      ∑ u ∈ range (133 * 133),
        (if u % 133 < n then ent13 W (u % 133) (u / 133) else 0) * 2 ^ (13 * u) := by
  intro n hn
  refine lanes_rec_eq (N := 133) (S := fun n => ∑ u ∈ range (133 * 133),
    (if u % 133 < n then ent13 W (u % 133) (u / 133) else 0) * 2 ^ (13 * u)) ?_ ?_ n hn
  · exact (Finset.sum_eq_zero fun r _ => by rw [if_neg (Nat.not_lt_zero _), Nat.zero_mul]).symm
  · intro i hi acc hacc
    beta_reduce
    rw [loopStrictN_eq, loopStrictN_eq, hacc]
    refine (lanes_trM_inner W i hi (nat_lit 133) (Nat.le_refl _)).trans ?_
    refine Finset.sum_congr rfl fun u hu => ?_
    have := Finset.mem_range.1 hu
    have e : u / nat_lit 133 < nat_lit 133 ↔ u / 133 < 133 := Iff.rfl
    have : u / 133 < 133 := by omega
    exact congrArg (· * 2 ^ (13 * u)) (if_congr ⟨fun h => by omega, fun h => by
      rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | h
      · exact Or.inl h
      · exact Or.inr ⟨h, this⟩⟩ rfl rfl)

theorem trM_eq (W : Nat) : trM W = ∑ k ∈ Finset.range 133, ∑ l ∈ Finset.range 133,
    ent13 W l k * 2 ^ (1729 * k + 13 * l) := by
  unfold trM
  refine (lanes_trM_outer W (nat_lit 133) (Nat.le_refl _)).trans ?_
  rw [Finset.sum_congr rfl fun u _ => congrArg (· * 2 ^ (13 * u))
      (if_pos (Nat.mod_lt u (by omega)) : (if u % 133 < 133 then ent13 W (u % 133) (u / 133) else 0)
        = ent13 W (u % 133) (u / 133)), lanes_rows]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l hl => ?_
  have := Finset.mem_range.1 hl
  have h1 : (133 * k + l) % 133 = l := by omega
  have h2 : (133 * k + l) / 133 = k := by omega
  rw [h1, h2]

theorem lanes_canon_eq {W : Nat} (hlt : W < 2 ^ (13 * (133 * 133))) :
    W = ∑ k ∈ Finset.range 133, ∑ l ∈ Finset.range 133, ent13 W k l * 2 ^ (1729 * k + 13 * l) := by
  have h := CFSG.KS.Ord.pk_lane (w := 13) (by omega) hlt
  unfold CFSG.KS.Ord.pk at h
  rw [lanes_rows] at h
  refine h.trans (Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_)
  unfold CFSG.KS.Ord.lane ent13
  congr 3
  ring

theorem validHN_spec {W : Nat} (h : validHN W = true) :
    W = ∑ k ∈ Finset.range 133, ∑ l ∈ Finset.range 133, ent13 W k l * 2 ^ (1729 * k + 13 * l) ∧
      ∀ k < 133, ∀ l < 133, ent13 W k l < 5 := by
  have hC : CFSG.KS.Ord.Canon 5 133 13 W := CFSG.KS.Ord.validM_canon CFSG.KD.OrdHN.consts h
  refine ⟨lanes_canon_eq hC.1, fun k hk l hl => ?_⟩
  have h2 := hC.2 (133 * k + l) (by nlinarith)
  unfold CFSG.KS.Ord.lane at h2
  unfold ent13
  have e : 1729 * k + 13 * l = 13 * (133 * k + l) := by ring
  rw [e]
  exact h2

theorem canonG_spec {G : Nat} (h : canonG G = true) :
    G = ∑ k ∈ Finset.range 133, ∑ l ∈ Finset.range 133, ent13 G k l * 2 ^ (1729 * k + 13 * l) ∧
      ∀ k < 133, ∀ l < 133, ent13 G k l < 5 := by
  unfold canonG at h
  obtain ⟨h1, h2⟩ := (CFSG.KS.bAnd_iff _ _).1 h
  have hlt' : G < 1 <<< 229957 := Nat.blt_eq.mp h1
  rw [Nat.shiftLeft_eq, Nat.one_mul, show (229957 : Nat) = 13 * (133 * 133) by norm_num] at hlt'
  have hlt : G < 2 ^ (13 * (133 * 133)) := hlt'
  refine ⟨lanes_canon_eq hlt, fun k hk l hl => ?_⟩
  have h3 := CFSG.KS.allN_spec h2 k hk
  rw [strictB_eq] at h3
  have h4 := CFSG.KS.allN_spec h3 l hl
  have h5 : fldW (fldW G (Nat.mul 1729 k) 1729) (Nat.mul 13 l) 13 < 5 := Nat.blt_eq.mp h4
  rw [fldW_eq] at h5
  unfold ent13
  rw [← row_lane G k l hl]
  exact h5

theorem lanes_idBlk (t c : Nat) (htc : 64 * t + c ≤ 133) : ∀ n ≤ c,
    Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun r acc => Nat.lor acc (Nat.shiftLeft (nat_lit 1) (Nat.add (Nat.mul (nat_lit 1729) r)
        (Nat.mul (nat_lit 13) (Nat.add (Nat.mul (nat_lit 64) t) r))))) n =
      ∑ u ∈ range (133 * 133),
        (if u / 133 < n ∧ u % 133 = 64 * t + u / 133 then 1 else 0) * 2 ^ (13 * u) := by
  intro n hn
  refine lanes_rec_eq (N := c) (S := fun n => ∑ u ∈ range (133 * 133),
    (if u / 133 < n ∧ u % 133 = 64 * t + u / 133 then 1 else 0) * 2 ^ (13 * u)) ?_ ?_ n hn
  · exact (Finset.sum_eq_zero fun r _ => by
      rw [if_neg (fun h => Nat.not_lt_zero _ h.1), Nat.zero_mul]).symm
  · intro i hi acc hacc
    beta_reduce
    rw [hacc]
    refine (lanes_or_single (w := 13) (n := 133 * 133) (r0 := 133 * i + (64 * t + i)) (by omega)
      (fun r _ => by split; exact (by norm_num); exact Nat.two_pow_pos _) (if_neg (by omega))
      (by omega) (by norm_num) (by show 1729 * i + 13 * (64 * t + i) = _; ring)).trans ?_
    refine Finset.sum_congr rfl fun u _ => ?_
    by_cases hu : u = 133 * i + (64 * t + i)
    · rw [if_pos hu, if_pos (by omega)]
    · rw [if_neg hu]
      exact congrArg (· * 2 ^ (13 * u)) (if_congr (by omega) rfl rfl)

theorem idBlk_lane (t c r l : Nat) (hc : c ≤ 64) (hr : r < 64) (hl : l < 133)
    (htc : 64 * t + c ≤ 133) :
    idBlk t c / 2 ^ (1729 * r + 13 * l) % 2 ^ 13 = if r < c ∧ l = 64 * t + r then 1 else 0 := by
  have h := lanes_idBlk t c htc c le_rfl
  unfold idBlk
  rw [h, show 1729 * r + 13 * l = 13 * (133 * r + l) by ring,
    lanes_lane (fun u _ => by split; exact (by norm_num); exact Nat.two_pow_pos _) (by omega)]
  exact if_congr (by omega) rfl rfl

theorem lanes_qgo_term (T : Nat → Nat) (t r k q : Nat) (Q : List Nat) (hne : 64 * t + r ≠ k) :
    (if k + 1 ≤ 64 * t + r ∧ 64 * t + r < k + 1 + Q.length then xv T (Q[64 * t + r - (k + 1)]!)
      else 0) =
    (if k ≤ 64 * t + r ∧ 64 * t + r < k + (q :: Q).length then xv T ((q :: Q)[64 * t + r - k]!)
      else 0) := by
  rw [List.length_cons]
  by_cases h : k + 1 ≤ 64 * t + r ∧ 64 * t + r < k + 1 + Q.length
  · rw [if_pos h, if_pos (by omega), show 64 * t + r - k = (64 * t + r - (k + 1)) + 1 by omega,
      List.getElem!_cons_succ]
  · rw [if_neg h, if_neg (by omega)]

theorem lanes_xv_lt (T : Nat → Nat) (q : Nat) : xv T q < 2 ^ 399 := by
  unfold xv
  rw [fldW_eq]
  exact Nat.mod_lt _ (Nat.two_pow_pos _)

theorem lanes_qgo (T : Nat → Nat) (t : Nat) : ∀ (Q : List Nat) (k : Nat),
    List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
      (fun q _ ih k => strictN (ih (Nat.succ k)) (fun rest =>
        nIf(Nat.beq (Nat.shiftRight k (nat_lit 6)) t,
          Nat.lor rest (Nat.shiftLeft (fldW (getRec T (nat_lit 464) q) (nat_lit 0) (nat_lit 399))
            (Nat.mul (nat_lit 1729) (Nat.land k (nat_lit 63)))), rest))) Q k =
      ∑ r ∈ range 64, (if k ≤ 64 * t + r ∧ 64 * t + r < k + Q.length then
        xv T (Q[64 * t + r - k]!) else 0) * 2 ^ (1729 * r) := by
  intro Q
  induction Q with
  | nil =>
    intro k
    exact (Finset.sum_eq_zero fun r _ => by
      rw [if_neg (by simp), Nat.zero_mul]).symm
  | cons q Q ih =>
    intro k
    dsimp only
    rw [strictN_eq, ih]
    have hh : ∀ r < 64, (if k + 1 ≤ 64 * t + r ∧ 64 * t + r < k + 1 + Q.length then
        xv T (Q[64 * t + r - (k + 1)]!) else 0) < 2 ^ 1729 := fun r _ => by
      split
      · exact Nat.lt_of_lt_of_le (lanes_xv_lt T _) (Nat.pow_le_pow_right (by omega) (by omega))
      · exact Nat.two_pow_pos _
    cases hb : Nat.beq (Nat.shiftRight k (nat_lit 6)) t
    · have hne : k / 64 ≠ t := by
        have := Nat.ne_of_beq_eq_false hb
        rw [show Nat.shiftRight k 6 = k / 64 from Nat.shiftRight_eq_div_pow k 6] at this
        exact this
      dsimp only
      refine Finset.sum_congr rfl fun r hr => ?_
      have := Finset.mem_range.1 hr
      rw [lanes_qgo_term T t r k q Q (by omega)]
    · have heq : k / 64 = t := by
        have := Nat.eq_of_beq_eq_true hb
        rw [show Nat.shiftRight k 6 = k / 64 from Nat.shiftRight_eq_div_pow k 6] at this
        exact this
      dsimp only
      refine (lanes_or_single (w := 1729) (n := 64) (r0 := k % 64) (by omega) hh
        (if_neg (by omega)) (Nat.mod_lt _ (by omega))
        (Nat.lt_of_lt_of_le (lanes_xv_lt T q) (Nat.pow_le_pow_right (by omega) (by omega)))
        (by
          show 1729 * (k &&& 63) = _
          rw [show (63 : Nat) = 2 ^ 6 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod])).trans ?_
      refine Finset.sum_congr rfl fun r hr => ?_
      have := Finset.mem_range.1 hr
      by_cases hr0 : r = k % 64
      · rw [if_pos hr0, List.length_cons, if_pos (by omega), show 64 * t + r - k = 0 by omega,
          List.getElem!_cons_zero]
      · rw [if_neg hr0, lanes_qgo_term T t r k q Q (by omega)]

theorem qBlk_eq (T : Nat → Nat) (Q : List Nat) (t : Nat) :
    qBlk T Q t = ∑ r ∈ Finset.range 64,
      (if 64 * t + r < Q.length then xv T (Q[64 * t + r]!) else 0) * 2 ^ (1729 * r) := by
  unfold qBlk
  refine (lanes_qgo T t Q 0).trans (Finset.sum_congr rfl fun r _ => ?_)
  rw [Nat.sub_zero, Nat.zero_add]
  exact congrArg (· * 2 ^ (1729 * r)) (if_congr (by omega) rfl rfl)

theorem lanes_col {CM3 M A : Nat} (hc : constsOK CM3 M = true) {a : Nat → Nat}
    (hA : A = ∑ r ∈ Finset.range 64, a r * 2 ^ (1729 * r)) (ha : ∀ r < 64, a r < 2 ^ 399)
    {k : Nat} (hk : k < 133) :
    (A >>> (3 * k)) &&& CM3 = ∑ r ∈ range 64, (a r / 2 ^ (3 * k) % 8) * 2 ^ (1729 * r) := by
  have ha' : ∀ r < 64, a r < 2 ^ 1729 := fun r hr =>
    Nat.lt_of_lt_of_le (ha r hr) (Nat.pow_le_pow_right (by omega) (by omega))
  have h7 : ∀ r < 64, (7 : Nat) < 2 ^ 1729 := fun _ _ =>
    Nat.lt_of_lt_of_le (by norm_num : (7 : Nat) < 2 ^ 3) (Nat.pow_le_pow_right (by omega) (by omega))
  have FA : CFSG.KS.PackFld.Fld 1729 (∑ r ∈ range 64, a r * 2 ^ (1729 * r))
      (fun t => if t < 64 then a t else 0) := CFSG.KS.Ord.fld_pk ha'
  have FC : CFSG.KS.PackFld.Fld 1729 (∑ r ∈ range 64, 7 * 2 ^ (1729 * r))
      (fun t => if t < 64 then 7 else 0) := CFSG.KS.Ord.fld_pk h7
  have hb : ∀ r < 64, a r / 2 ^ (3 * k) % 8 < 2 ^ 1729 := fun r _ =>
    Nat.lt_of_lt_of_le (Nat.mod_lt _ (by norm_num))
      (by rw [show (8 : Nat) = 2 ^ 3 by norm_num]; exact Nat.pow_le_pow_right (by omega) (by omega))
  rw [lanes_CM3 hc, hA]
  refine CFSG.KS.Ord.pk_of_fld (by omega) ?_ hb
  intro i b hbw
  rw [Nat.testBit_and, Nat.testBit_shiftRight, FC i b hbw]
  by_cases hi : i < 64
  · simp only [hi, if_true]
    rw [show (7 : Nat) = 2 ^ 3 - 1 by norm_num, Nat.testBit_two_pow_sub_one,
      show (8 : Nat) = 2 ^ 3 by norm_num, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
    by_cases hb3 : b < 3
    · rw [show 3 * k + (1729 * i + b) = 1729 * i + (b + 3 * k) by ring, FA i _ (by omega)]
      simp [hi, hb3]
    · simp [hb3]
  · simp [hi]

theorem lanes_dm133 {i j : Nat} (hj : j < 133) : (133 * i + j) / 133 = i ∧ (133 * i + j) % 133 = j :=
  ⟨by omega, by omega⟩

theorem lanes_rowG {G : Nat} {g : Nat → Nat → Nat}
    (hG : G = ∑ k ∈ Finset.range 133, ∑ l ∈ Finset.range 133, g k l * 2 ^ (1729 * k + 13 * l))
    (hg : ∀ k < 133, ∀ l < 133, g k l < 2 ^ 13) {k : Nat} (hk : k < 133) :
    (G >>> (1729 * k)) &&& (2 ^ (13 * 133) - 1) = ∑ l ∈ range 133, g k l * 2 ^ (13 * l) := by
  have hGp : G = ∑ u ∈ range (133 * 133), g (u / 133) (u % 133) * 2 ^ (13 * u) := by
    rw [lanes_rows, hG]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj => ?_
    obtain ⟨e1, e2⟩ := lanes_dm133 (i := i) (Finset.mem_range.1 hj)
    beta_reduce
    rw [e1, e2]
  have hb : ∀ t < 133 * 133, g (t / 133) (t % 133) < 2 ^ 13 := fun t ht =>
    hg _ (by omega) _ (by omega)
  have h := CFSG.KS.Ord.row_eq (w := 13) (d := 133) (k := k) (b := fun u => g (u / 133) (u % 133))
    (by omega) hb hk
  unfold CFSG.KS.Ord.pk at h
  rw [show 1729 * k = 133 * 13 * k by ring, hGp]
  refine h.trans (Finset.sum_congr rfl fun j hj => ?_)
  obtain ⟨e1, e2⟩ := lanes_dm133 (i := k) (Finset.mem_range.1 hj)
  beta_reduce
  rw [e1, e2]

theorem lanes_U (c g : Nat → Nat → Nat) :
    ∑ k ∈ range 133, (∑ r ∈ range 64, c k r * 2 ^ (1729 * r)) *
        (∑ l ∈ range 133, g k l * 2 ^ (13 * l)) =
      ∑ u ∈ range (133 * 133), (if u / 133 < 64 then
        ∑ k ∈ range 133, c k (u / 133) * g k (u % 133) else 0) * 2 ^ (13 * u) := by
  calc _ = ∑ k ∈ range 133, ∑ r ∈ range 64, ∑ l ∈ range 133,
        c k r * g k l * 2 ^ (1729 * r + 13 * l) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun l _ => ?_
        rw [Nat.pow_add]
        ring
    _ = ∑ r ∈ range 64, ∑ l ∈ range 133, ∑ k ∈ range 133,
        c k r * g k l * 2 ^ (1729 * r + 13 * l) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun r _ => Finset.sum_comm
    _ = ∑ r ∈ range 133, (if r < 64 then ∑ l ∈ range 133,
        (∑ k ∈ range 133, c k r * g k l) * 2 ^ (1729 * r + 13 * l) else 0) := by
        rw [lanes_sum_ext (by omega)]
        refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun l _ => ?_
        rw [Finset.sum_mul]
    _ = _ := by
        rw [lanes_rows]
        refine Finset.sum_congr rfl fun i _ => ?_
        by_cases hi : i < 64
        · rw [if_pos hi]
          refine Finset.sum_congr rfl fun j hj => ?_
          obtain ⟨e1, e2⟩ := lanes_dm133 (i := i) (Finset.mem_range.1 hj)
          rw [e1, e2, if_pos hi]
        · rw [if_neg hi]
          refine (Finset.sum_eq_zero fun j hj => ?_).symm
          obtain ⟨e1, e2⟩ := lanes_dm133 (i := i) (Finset.mem_range.1 hj)
          rw [e1, if_neg hi, Nat.zero_mul]

theorem lanes_mulC_rec (A G CM3 RM n : Nat) :
    Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun k acc => Nat.add acc (Nat.mul (Nat.land (Nat.shiftRight A (Nat.mul (nat_lit 3) k)) CM3)
        (Nat.land (Nat.shiftRight G (Nat.mul (nat_lit 1729) k)) RM))) n =
      ∑ k ∈ range n, ((A >>> (3 * k)) &&& CM3) * ((G >>> (1729 * k)) &&& RM) :=
  lanes_rec_add _ n

theorem lanes_F_le {a : Nat → Nat} {g : Nat → Nat → Nat} (hg : ∀ k < 133, ∀ l < 133, g k l < 5)
    (r l : Nat) (hl : l < 133) :
    ∑ k ∈ range 133, (a r / 2 ^ (3 * k) % 8) * g k l ≤ 3724 := by
  calc _ ≤ ∑ _k ∈ range 133, 28 := Finset.sum_le_sum fun k hk => by
          have h1 := Nat.mod_lt (a r / 2 ^ (3 * k)) (show 8 > 0 by norm_num)
          have h2 := hg k (Finset.mem_range.1 hk) l hl
          exact Nat.mul_le_mul (show _ ≤ 7 by omega) (show _ ≤ 4 by omega) |>.trans (by norm_num)
    _ = 3724 := by simp

theorem mulC_lane {CM3 M A G : Nat} (hc : constsOK CM3 M = true) {a : Nat → Nat}
    (hA : A = ∑ r ∈ Finset.range 64, a r * 2 ^ (1729 * r)) (ha : ∀ r < 64, a r < 2 ^ 399)
    {g : Nat → Nat → Nat}
    (hG : G = ∑ k ∈ Finset.range 133, ∑ l ∈ Finset.range 133, g k l * 2 ^ (1729 * k + 13 * l))
    (hg : ∀ k < 133, ∀ l < 133, g k l < 5) :
    ∀ r < 64, ∀ l < 133, mulC CM3 A G / 2 ^ (1729 * r + 13 * l) % 2 ^ 13 =
      (∑ k ∈ Finset.range 133, (a r / 2 ^ (3 * k) % 8) * g k l) % 5 := by
  obtain ⟨-, -, -, -, hT, -, hL, hH, -, hRM, -⟩ := CFSG.KS.Ord.consts_facts CFSG.KD.OrdHN.consts
  intro r hr l hl
  have hg' : ∀ k < 133, ∀ l < 133, g k l < 2 ^ 13 := fun k hk l hl =>
    Nat.lt_of_lt_of_le (hg k hk l hl) (by norm_num)
  have hU : ∑ k ∈ range 133, ((A >>> (3 * k)) &&& CM3) * ((G >>> (1729 * k)) &&& (2 ^ (13 * 133) - 1))
      = ∑ u ∈ range (133 * 133), (if u / 133 < 64 then
        ∑ k ∈ range 133, (a (u / 133) / 2 ^ (3 * k) % 8) * g k (u % 133) else 0) * 2 ^ (13 * u) := by
    rw [← lanes_U (fun k r => a r / 2 ^ (3 * k) % 8) g]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [lanes_col hc hA ha (Finset.mem_range.1 hk), lanes_rowG hG hg' (Finset.mem_range.1 hk)]
  have hFb : ∀ t < 133 * 133, (if t / 133 < 64 then
      ∑ k ∈ range 133, (a (t / 133) / 2 ^ (3 * k) % 8) * g k (t % 133) else 0) ≤ 3724 := by
    intro t _
    split
    · exact lanes_F_le hg _ _ (Nat.mod_lt _ (by omega))
    · omega
  have hR := CFSG.KS.Ord.redP_pk (w := 13) (n := 133 * 133) (p := 5) (T := 9)
    (f := fun t => if t / 133 < 64 then
      ∑ k ∈ range 133, (a (t / 133) / 2 ^ (3 * k) % 8) * g k (t % 133) else 0) (by omega) hT
    (fun t ht => Nat.lt_of_le_of_lt (hFb t ht) (by norm_num))
    (fun t ht => Nat.lt_of_le_of_lt (hFb t ht) (by norm_num))
  unfold CFSG.KS.Ord.pk at hR hL hH
  beta_reduce at hR hL hH
  have hrec := lanes_mulC_rec A G CM3 CFSG.KD.OrdHN.RM (nat_lit 133)
  unfold mulC
  rw [hrec, hRM, hU, hL, hH, hR, show 1729 * r + 13 * l = 13 * (133 * r + l) by ring,
    lanes_lane (fun t _ => Nat.lt_of_lt_of_le (Nat.mod_lt _ (by omega)) (by norm_num)) (by omega)]
  obtain ⟨e1, e2⟩ := lanes_dm133 (i := r) hl
  beta_reduce
  rw [e1, e2, if_pos hr]

theorem lanes_lenQ : ∀ Q : List Nat, lenQ Q = Q.length
  | [] => rfl
  | _ :: Q => congrArg Nat.succ (lanes_lenQ Q)

theorem lanes_blk {T : Nat → Nat} {CM3 M : Nat} (hc : constsOK CM3 M = true) {Q : List Nat}
    {G t c : Nat} (hlen : Q.length = 133) (hG : canonG G = true)
    (hm : mulC CM3 (qBlk T Q t) G = idBlk t c) (hc64 : c ≤ 64) (htc : 64 * t + c ≤ 133) :
    ∀ r < c, ∀ l < 133, (∑ k ∈ Finset.range 133, xe T (Q[64 * t + r]!) k * ent13 G k l) % 5 =
      if 64 * t + r = l then 1 else 0 := by
  intro r hr l hl
  obtain ⟨hGe, hGl⟩ := canonG_spec hG
  have ha : ∀ r < 64, (fun r => if 64 * t + r < Q.length then xv T (Q[64 * t + r]!) else 0) r
      < 2 ^ 399 := fun r _ => by
    beta_reduce
    split
    · exact lanes_xv_lt T _
    · exact Nat.two_pow_pos _
  have h1 := mulC_lane hc (qBlk_eq T Q t) ha hGe hGl r (by omega) l hl
  rw [hm, idBlk_lane t c r l hc64 (by omega) hl htc] at h1
  beta_reduce at h1
  rw [if_pos (show 64 * t + r < Q.length by omega)] at h1
  unfold xe
  rw [← h1]
  exact if_congr (by omega) rfl rfl

theorem qBasisK_sound {T : Nat → Nat} {CM3 M : Nat} (hc : constsOK CM3 M = true) {Q : List Nat}
    {G : Nat} (h : qBasisK T CM3 Q G = true) :
    Q.length = 133 ∧ (∀ k < 133, ∀ l < 133, ent13 G k l < 5) ∧
      ∀ r < 133, ∀ l < 133,
        (∑ k ∈ Finset.range 133, xe T (Q[r]!) k * ent13 G k l) % 5 = if r = l then 1 else 0 := by
  unfold qBasisK at h
  obtain ⟨h1, h⟩ := (CFSG.KS.bAnd_iff _ _).1 h
  obtain ⟨-, h⟩ := (CFSG.KS.bAnd_iff _ _).1 h
  obtain ⟨h3, h⟩ := (CFSG.KS.bAnd_iff _ _).1 h
  obtain ⟨h4, h⟩ := (CFSG.KS.bAnd_iff _ _).1 h
  obtain ⟨h5, h6⟩ := (CFSG.KS.bAnd_iff _ _).1 h
  have hlen : Q.length = 133 := by
    rw [← lanes_lenQ]
    exact Nat.eq_of_beq_eq_true h1
  have m0 : mulC CM3 (qBlk T Q 0) G = idBlk 0 64 := Nat.eq_of_beq_eq_true h4
  have m1 : mulC CM3 (qBlk T Q 1) G = idBlk 1 64 := Nat.eq_of_beq_eq_true h5
  have m2 : mulC CM3 (qBlk T Q 2) G = idBlk 2 5 := Nat.eq_of_beq_eq_true h6
  refine ⟨hlen, (canonG_spec h3).2, fun r hr l hl => ?_⟩
  by_cases hr0 : r < 64
  · have := lanes_blk hc hlen h3 m0 (by omega) (by omega) r hr0 l hl
    rwa [show 64 * 0 + r = r by omega] at this
  by_cases hr1 : r < 128
  · have := lanes_blk hc hlen h3 m1 (by omega) (by omega) (r - 64) (by omega) l hl
    rwa [show 64 * 1 + (r - 64) = r by omega] at this
  · have := lanes_blk hc hlen h3 m2 (by omega) (by omega) (r - 128) (by omega) l hl
    rwa [show 64 * 2 + (r - 128) = r by omega] at this

end CFSG.KS.SporSch.HNXP

end
