module

public import CFSG.Certificates.Kernel.HNLocal.Defs
import all CFSG.Certificates.Kernel.Spor.OrdSound
import CFSG.Certificates.Kernel.Spor.PackFld

public section

namespace CFSG.KS.HNLocal.MatPf

open CFSG.KC.Ord CFSG.KC.HNLocal CFSG.KS.Ord CFSG.KS.HNLocal Matrix CFSG.KS.PackFld

private theorem strictN_eq' (y : Nat) (k : Nat → Nat) : CFSG.KC.Loop.strictN y k = k y := by
  cases y <;> rfl

private theorem rec_eq {x N : Nat} {F : Nat → Nat → Nat} {S : Nat → Nat} (h0 : x = S 0)
    (hs : ∀ i < N, F i (S i) = S (i + 1)) :
    ∀ n ≤ N, Nat.rec (motive := fun _ => Nat) x F n = S n := by
  intro n
  induction n with
  | zero => intro _; exact h0
  | succ n ih =>
    intro hn
    rw [← hs n (by omega), ← ih (by omega)]

private theorem OM_lane (X : Nat) (i j : Fin 133) :
    OM X i j = ((lane 13 X (133 * i.val + j.val) : Nat) : ZMod 5) := by
  show ((X / 2 ^ (1729 * i.val + 13 * j.val) % 2 ^ 13 : Nat) : ZMod 5) = _
  unfold lane
  rw [show 13 * (133 * i.val + j.val) = 1729 * i.val + 13 * j.val by ring]

private theorem OM_pk {g : Nat → Nat} (hg : ∀ t < 133 * 133, g t < 2 ^ 13) (i j : Fin 133) :
    OM (pk 13 (133 * 133) g) i j = ((g (133 * i.val + j.val) : Nat) : ZMod 5) := by
  rw [OM_lane, lane_pk hg (idx_lt i.isLt j.isLt)]

private theorem lane_zero {X s : Nat} (hX : Canon 5 133 13 X) (hs : 133 * 133 ≤ s) :
    lane 13 X s = 0 := by
  have h : X < 2 ^ (13 * s) :=
    lt_of_lt_of_le hX.1 (Nat.pow_le_pow_right (n := 2) (by norm_num)
      (show 13 * (133 * 133) ≤ 13 * s by omega))
  unfold lane
  rw [Nat.div_eq_of_lt h, Nat.zero_mod]

private theorem lane_lt5 {X : Nat} (hX : Canon 5 133 13 X) (s : Nat) : lane 13 X s < 5 := by
  by_cases hs : s < 133 * 133
  · exact hX.2 s hs
  · rw [lane_zero hX (by omega)]
    norm_num

private theorem land_val (X o : Nat) :
    Nat.land (Nat.shiftRight X o) (nat_lit 8191) = X / 2 ^ o % 2 ^ 13 := by
  change (X >>> o) &&& (2 ^ 13 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

private theorem dm (x a b c : Nat) (h : b + c ≤ a) : x % 2 ^ a / 2 ^ b % 2 ^ c = x / 2 ^ b % 2 ^ c := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  by_cases hi : i < c
  · have : i + b < a := by omega
    simp [hi, this]
  · simp [hi]

private theorem row_val (W i j : Nat) (hj : j < 133) :
    Nat.land (Nat.shiftRight (Nat.land (Nat.shiftRight W (Nat.mul (nat_lit 1729) i))
        (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 1729)) (nat_lit 1))) (Nat.mul (nat_lit 13) j))
      (nat_lit 8191) = lane 13 W (133 * i + j) := by
  rw [land_val]
  change ((W >>> (1729 * i)) &&& ((1 <<< 1729) - 1)) / 2 ^ (13 * j) % 2 ^ 13 = _
  rw [Nat.one_shiftLeft, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow,
    dm _ _ _ _ (by omega), Nat.div_div_eq_div_mul, ← Nat.pow_add]
  unfold lane
  rw [show 13 * (133 * i + j) = 1729 * i + 13 * j by ring]

private theorem pk_or_single {w n r0 v e : Nat} {h : Nat → Nat} (hw : 0 < w)
    (hh : ∀ r < n, h r < 2 ^ w) (h0 : h r0 = 0) (hr0 : r0 < n) (hv : v < 2 ^ w)
    (he : e = w * r0) :
    Nat.lor (pk w n h) (Nat.shiftLeft v e) = pk w n (fun r => if r = r0 then v else h r) := by
  subst he
  have hb : ∀ r < n, (if r = r0 then v else h r) < 2 ^ w := fun r hr => by
    split
    · exact hv
    · exact hh r hr
  refine pk_of_fld hw (fld_congr (fld_or (fld_pk hh) (fld_shl r0 (fld_one hv))) fun t => ?_) hb
  by_cases ht : t < n
  · by_cases htr : t = r0
    · subst htr
      simp [ht, h0]
    · have h1 : t - r0 ≠ 0 ∨ ¬ r0 ≤ t := by omega
      rcases h1 with h1 | h1 <;> simp [ht, htr, h1]
  · have htr : t ≠ r0 := by omega
    have h1 : t - r0 ≠ 0 := by omega
    simp [ht, htr, h1]

private noncomputable def tl (W u : Nat) : Nat := lane 13 W (133 * (u % 133) + u / 133)

private theorem tl_lt (W u : Nat) : tl W u < 2 ^ 13 := Nat.mod_lt _ (by positivity)

private theorem trM_inner (W i : Nat) (hi : i < 133) : ∀ j ≤ 133,
    Nat.rec (motive := fun _ => Nat)
      (pk 13 (133 * 133) (fun u => if u % 133 < i then tl W u else 0))
      (fun j acc2 => Nat.lor acc2 (Nat.shiftLeft (Nat.land (Nat.shiftRight
        (Nat.land (Nat.shiftRight W (Nat.mul (nat_lit 1729) i))
          (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 1729)) (nat_lit 1))) (Nat.mul (nat_lit 13) j))
            (nat_lit 8191)) (Nat.add (Nat.mul (nat_lit 1729) j) (Nat.mul (nat_lit 13) i)))) j =
      pk 13 (133 * 133)
        (fun u => if u % 133 < i ∨ (u % 133 = i ∧ u / 133 < j) then tl W u else 0) := by
  refine rec_eq (N := 133) (S := fun j => pk 13 (133 * 133)
    (fun u => if u % 133 < i ∨ (u % 133 = i ∧ u / 133 < j) then tl W u else 0)) ?_ ?_
  · exact pk_congr fun u _ => if_congr (by omega) rfl rfl
  intro j hj
  beta_reduce
  have hv : tl W (133 * j + i) = lane 13 W (133 * i + j) := by
    unfold tl
    rw [show (133 * j + i) % 133 = i by omega, show (133 * j + i) / 133 = j by omega]
  refine (pk_or_single (w := 13) (n := 133 * 133) (r0 := 133 * j + i) (by omega)
    (fun r _ => by split; exact tl_lt W r; exact Nat.two_pow_pos _) (if_neg (by omega))
    (by omega) (by rw [row_val W i j hj, ← hv]; exact tl_lt _ _)
    (by show 1729 * j + 13 * i = _; ring)).trans ?_
  refine pk_congr fun u _ => ?_
  by_cases hu : u = 133 * j + i
  · subst hu
    rw [if_pos rfl, if_pos (by omega), row_val W i j hj, hv]
  · rw [if_neg hu]
    exact if_congr (by omega) rfl rfl

private theorem trM_outer (W : Nat) : ∀ n ≤ 133,
    Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun i acc => CFSG.KC.Loop.strictN acc (fun s => CFSG.KC.Loop.strictN
        (Nat.land (Nat.shiftRight W (Nat.mul (nat_lit 1729) i))
          (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 1729)) (nat_lit 1))) (fun row =>
        Nat.rec (motive := fun _ => Nat) s
          (fun j acc2 => Nat.lor acc2 (Nat.shiftLeft (Nat.land (Nat.shiftRight row
            (Nat.mul (nat_lit 13) j)) (nat_lit 8191))
              (Nat.add (Nat.mul (nat_lit 1729) j) (Nat.mul (nat_lit 13) i)))) (nat_lit 133)))) n =
      pk 13 (133 * 133) (fun u => if u % 133 < n then tl W u else 0) := by
  refine rec_eq (N := 133) (S := fun n => pk 13 (133 * 133) (fun u => if u % 133 < n then tl W u else 0)) ?_ ?_
  · unfold pk
    exact (Finset.sum_eq_zero fun r _ => by
      show (if r % 133 < 0 then tl W r else 0) * 2 ^ (13 * r) = 0
      rw [if_neg (Nat.not_lt_zero _), Nat.zero_mul]).symm
  intro n hn
  beta_reduce
  rw [strictN_eq', strictN_eq']
  refine (trM_inner W n hn 133 le_rfl).trans (pk_congr fun u hu => ?_)
  have : u / 133 < 133 := by omega
  exact if_congr (by omega) rfl rfl

private theorem trM_closed (W : Nat) : trM W = pk 13 (133 * 133) (tl W) := by
  unfold trM
  exact (trM_outer W 133 le_rfl).trans (pk_congr fun u _ => if_pos (Nat.mod_lt u (by omega)))

theorem trM_sound' {X : Nat} (hX : Canon 5 133 13 X) :
    Canon 5 133 13 (trM X) ∧ OM (trM X) = (OM X)ᵀ := by
  have hT : ∀ t, tl X t < 5 := fun t => lane_lt5 hX _
  rw [trM_closed]
  refine ⟨canon_pk (fun t _ => hT t) (by norm_num), ?_⟩
  funext i j
  rw [OM_pk (fun t _ => lt_trans (hT t) (by norm_num)), Matrix.transpose_apply, OM_lane]
  unfold tl
  rw [show (133 * i.val + j.val) % 133 = j.val by omega,
    show (133 * i.val + j.val) / 133 = i.val by omega]

private theorem trace_rec (X : Nat) : ∀ n, Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Nat.add acc (Nat.land (Nat.shiftRight X (Nat.mul (nat_lit 1742) i))
      (nat_lit 8191))) n = ∑ k ∈ Finset.range n, lane 13 X (134 * k)
  | 0 => rfl
  | n + 1 => by
    rw [Finset.sum_range_succ, ← trace_rec X n]
    unfold lane
    rw [show 13 * (134 * n) = 1742 * n by ring, ← land_val]
    rfl

theorem traceL_sound' {X : Nat} (hX : Canon 5 133 13 X) :
    ((traceL X : Nat) : ZMod 5) = (OM X).trace := by
  have e : traceL X = (∑ k ∈ Finset.range 133, lane 13 X (134 * k)) % 5 := by
    unfold traceL
    exact congrArg (· % 5) (trace_rec X 133)
  rw [e, ZMod.natCast_mod, Nat.cast_sum, Matrix.trace,
    ← Fin.sum_univ_eq_sum_range (fun k => ((lane 13 X (134 * k) : Nat) : ZMod 5))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, OM_lane, show 133 * i.val + i.val = 134 * i.val by ring]

theorem subOne_sound' {L H CM RM ONE LV HV X : Nat}
    (hc : constsOK 5 13 1729 133 9 L H CM RM ONE LV HV = true)
    (hX : Canon 5 133 13 X) :
    Canon 5 133 13 (redP 13 L H 5 9 (X + 4 * ONE)) ∧
      OM (redP 13 L H 5 9 (X + 4 * ONE)) = OM X - 1 := by
  obtain ⟨-, -, -, -, hT, -, hL, hH, -, -, hONE⟩ := consts_facts hc
  clear hc
  have hXe := pk_lane (w := 13) (n := 133 * 133) (by norm_num) hX.1
  have ha : ∀ t < 133 * 133, lane 13 X t < 5 := hX.2
  rw [hL, hH, hONE, hXe]
  generalize lane 13 X = a at ha ⊢
  have h12 : (2 : Nat) ^ (13 - 1) = 4096 := by norm_num
  have e1 : pk 13 (133 * 133) a + 4 * pk 13 (133 * 133)
      (fun t => if t / 133 = t % 133 then 1 else 0) =
      pk 13 (133 * 133) (fun t => a t + (if t / 133 = t % 133 then 1 else 0) * 4) := by
    rw [Nat.mul_comm 4, pk_mul, pk_add]
  have e : redP 13 (pk 13 (133 * 133) fun _ => 1) (pk 13 (133 * 133) fun _ => 2 ^ (13 - 1)) 5 9
      (pk 13 (133 * 133) a + 4 * pk 13 (133 * 133) (fun t => if t / 133 = t % 133 then 1 else 0)) =
      pk 13 (133 * 133) (fun t => (a t + (if t / 133 = t % 133 then 1 else 0) * 4) % 5) := by
    rw [e1]
    refine redP_pk (by norm_num) hT (fun t ht => ?_) (fun t ht => ?_)
    · have := ha t ht
      rw [h12]
      split <;> omega
    · have := ha t ht
      have h10 : (5 : Nat) * 2 ^ (9 + 1) = 5120 := by norm_num
      rw [h10]
      split <;> omega
  rw [e]
  refine ⟨canon_pk (fun t _ => Nat.mod_lt _ (by norm_num)) (by norm_num), ?_⟩
  funext i j
  rw [OM_pk (fun t _ => lt_trans (Nat.mod_lt _ (by norm_num)) (by norm_num)), Matrix.sub_apply,
    OM_pk (fun t ht => lt_trans (ha t ht) (by norm_num)), Matrix.one_apply, ZMod.natCast_mod,
    (dm_eq (i := i.val) j.isLt).1, (dm_eq (i := i.val) j.isLt).2]
  have h4 : (4 : ZMod 5) = -1 := by decide
  by_cases h : i = j
  · subst h
    simp only [if_true]
    push_cast
    rw [h4]
    ring
  · have h' : i.val ≠ j.val := fun e => h (Fin.ext e)
    simp [h, h']

private noncomputable def rg (X m n t : Nat) : Nat :=
  if t < 133 * n then lane 13 X (t + 133 * m) else 0

private theorem rows_closed {X m n : Nat} (hX : Canon 5 133 13 X) :
    Nat.land (Nat.shiftRight X (1729 * m)) (2 ^ (1729 * n) - 1) = pk 13 (133 * 133) (rg X m n) := by
  have hF : Fld 13 (Nat.land (Nat.shiftRight X (1729 * m)) (2 ^ (1729 * n) - 1)) (rg X m n) := by
    intro t k hk
    change ((X >>> (1729 * m)) &&& (2 ^ (1729 * n) - 1)).testBit (13 * t + k) = _
    rw [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one]
    unfold rg
    by_cases ht : t < 133 * n
    · have h1 : 13 * t + k < 1729 * n := by omega
      rw [if_pos ht, ← fld_lane 13 X (t + 133 * m) k hk,
        show 1729 * m + (13 * t + k) = 13 * (t + 133 * m) + k by ring]
      simp [h1]
    · have h1 : ¬ 13 * t + k < 1729 * n := by omega
      rw [if_neg ht]
      simp [h1]
  refine pk_of_fld (by norm_num) (fld_congr hF fun t => ?_)
    (fun t _ => lt_trans (by unfold rg; split; exact lane_lt5 hX _; norm_num) (by norm_num))
  by_cases ht : t < 133 * 133
  · rw [if_pos ht]
  · rw [if_neg ht]
    unfold rg
    split
    · exact lane_zero hX (by omega)
    · rfl

theorem rows_sound' {X m n : Nat} (hX : Canon 5 133 13 X) :
    Canon 5 133 13 (Nat.land (Nat.shiftRight X (1729 * m)) (2 ^ (1729 * n) - 1)) ∧
      ∀ i j : Fin 133, OM (Nat.land (Nat.shiftRight X (1729 * m)) (2 ^ (1729 * n) - 1)) i j =
        if h : i.val < n ∧ m + i.val < 133 then OM X ⟨m + i.val, h.2⟩ j else 0 := by
  have hr : ∀ t, rg X m n t < 5 := fun t => by
    unfold rg
    split
    · exact lane_lt5 hX _
    · norm_num
  rw [rows_closed hX]
  refine ⟨canon_pk (fun t _ => hr t) (by norm_num), fun i j => ?_⟩
  rw [OM_pk (fun t _ => lt_trans (hr t) (by norm_num))]
  unfold rg
  by_cases h : i.val < n ∧ m + i.val < 133
  · rw [dif_pos h, OM_lane, if_pos (by omega)]
    simp only
    rw [show 133 * i.val + j.val + 133 * m = 133 * (m + i.val) + j.val by ring]
  · rw [dif_neg h]
    by_cases h1 : 133 * i.val + j.val < 133 * n
    · rw [if_pos h1, lane_zero hX (by omega)]
      simp
    · rw [if_neg h1]
      simp

end CFSG.KS.HNLocal.MatPf

end
