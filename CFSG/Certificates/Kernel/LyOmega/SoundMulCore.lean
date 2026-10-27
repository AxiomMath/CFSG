module

public import Certificates.Data.Kernel.LyOmega.Chart
public import Certificates.Data.Kernel.LyOmega.Small
public import CFSG.Certificates.Kernel.LyOmega.Defs
import all CFSG.Certificates.Kernel.Spor.OrdSound
import all CFSG.Certificates.Kernel.LyOmega.TreeCoreMul
import CFSG.Certificates.Kernel.Spor.PackFld

public section

namespace CFSG.KS.LyOm.MC

open CFSG.KC.LyOm CFSG.KC.Ord CFSG.KC.LL CFSG.KC.Loop
open CFSG.KS.Ord CFSG.KS.PackFld CFSG.KS.LyOm.TreeCore

private theorem mask_pk (w : ℕ) : ∀ s, 2 ^ (w * s) - 1 = pk w s (fun _ => 2 ^ w - 1)
  | 0 => by simp [pk]
  | s + 1 => by
    rw [pk_succ, ← mask_pk w s, Nat.mul_succ, Nat.pow_add]
    obtain ⟨a, ha⟩ : ∃ a, 2 ^ (w * s) = a + 1 := ⟨_, (Nat.succ_pred_eq_of_pos (Nat.two_pow_pos _)).symm⟩
    obtain ⟨b, hb⟩ : ∃ b, 2 ^ w = b + 1 := ⟨_, (Nat.succ_pred_eq_of_pos (Nat.two_pow_pos _)).symm⟩
    rw [ha, hb, Nat.add_sub_cancel, Nat.add_sub_cancel]
    apply Nat.sub_eq_of_eq_add
    ring

private theorem cols_pk {w r s h : ℕ} (hw : 0 < w) (hr : 0 < r) (hs : s ≤ r) :
    (2 ^ (w * s) - 1) * rep1 (r * w) h =
      pk w (r * h) (fun t => if t % r < s then 2 ^ w - 1 else 0) := by
  rw [rep1_eq (Or.inl (Nat.mul_pos hr hw)), pk_rows, Finset.mul_sum, mask_pk]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold pk
  rw [Finset.sum_mul]
  obtain ⟨u, rfl⟩ : ∃ u, r = s + u := ⟨r - s, by omega⟩
  rw [Finset.sum_range_add]
  have h0 : ∑ j ∈ Finset.range u, (if ((s + u) * i + (s + j)) % (s + u) < s then 2 ^ w - 1 else 0) *
      2 ^ (w * ((s + u) * i + (s + j))) = 0 := by
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [(dm_eq (d := s + u) (i := i) (j := s + j) (by have := Finset.mem_range.1 hj; omega)).2]
    simp
  rw [h0, Nat.add_zero]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := Finset.mem_range.1 hj
  rw [(dm_eq (d := s + u) (i := i) (j := j) (by omega)).2, if_pos hj', Nat.mul_assoc, ← Nat.pow_add]
  congr 2
  ring

private theorem pk_trunc {w n n' : ℕ} {f : ℕ → ℕ} (hn : n' ≤ n) (h0 : ∀ t, n' ≤ t → t < n → f t = 0) :
    pk w n f = pk w n' f := by
  obtain ⟨u, rfl⟩ : ∃ u, n = n' + u := ⟨n - n', by omega⟩
  unfold pk
  rw [Finset.sum_range_add, Finset.sum_eq_zero (s := Finset.range u) fun t ht => by
    rw [h0 _ (by omega) (by have := Finset.mem_range.1 ht; omega), Nat.zero_mul], Nat.add_zero]

private theorem lc_lanes {w r c n X : ℕ} (hw : 0 < w) (hX : LCanon w r c X) (hn : c * r ≤ n) :
    ∃ x : ℕ → ℕ, X = pk w n x ∧ (∀ t < n, x t < 5) ∧ ∀ t, c * r ≤ t → x t = 0 := by
  have hlt : X < 2 ^ (w * (c * r)) := by rw [← Nat.mul_assoc]; exact hX.1
  refine ⟨lane w X, pk_lane hw (lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by norm_num)
    (Nat.mul_le_mul_left w hn))), fun t ht => ?_, fun t ht => ?_⟩
  · by_cases htc : t < c * r
    · have hc : 0 < c := Nat.pos_of_ne_zero fun h => by simp [h] at htc
      have h1 : t / c < r := (Nat.div_lt_iff_lt_mul hc).2 (by rw [Nat.mul_comm]; exact htc)
      have := hX.2 (t / c) h1 (t % c) (Nat.mod_lt _ hc)
      have e : w * c * (t / c) + w * (t % c) = w * t := by
        rw [Nat.mul_assoc, ← Nat.mul_add, Nat.div_add_mod]
      rw [e] at this
      exact this
    · unfold lane
      rw [Nat.div_eq_of_lt (lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by norm_num)
        (Nat.mul_le_mul_left w (by omega))))]
      simp
  · unfold lane
    rw [Nat.div_eq_of_lt (lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by norm_num)
      (Nat.mul_le_mul_left w ht)))]
    simp

private theorem lc_of_pk {w r c n : ℕ} {f : ℕ → ℕ} (h5 : 5 ≤ 2 ^ w) (hf : ∀ t < n, f t < 5)
    (h0 : ∀ t, c * r ≤ t → t < n → f t = 0) (hn : c * r ≤ n) : LCanon w r c (pk w n f) := by
  rw [pk_trunc hn h0]
  have hf' : ∀ t < c * r, f t < 2 ^ w := fun t ht => lt_of_lt_of_le (hf t (by omega)) h5
  refine ⟨by rw [Nat.mul_assoc]; exact pk_lt hf', fun i hi j hj => ?_⟩
  have hidx : c * i + j < c * r := by
    have := Nat.mul_le_mul_left c (Nat.succ_le_of_lt hi)
    rw [Nat.mul_succ] at this
    omega
  have e : w * c * i + w * j = w * (c * i + j) := by ring
  rw [e]
  have := lane_pk hf' hidx
  unfold lane at this
  rw [this]
  exact hf _ (by omega)

private theorem ent_pk {w c n S i j : ℕ} {f : ℕ → ℕ} (hS : S = w * c) (hf : ∀ t < n, f t < 2 ^ w)
    (h : c * i + j < n) : ent w S (pk w n f) i j = ((f (c * i + j) : ℕ) : ZMod 5) := by
  unfold ent
  have e : S * i + w * j = w * (c * i + j) := by rw [hS]; ring
  rw [e]
  have := lane_pk hf h
  unfold lane at this
  rw [this]

private theorem idx {r h i j : ℕ} (hi : i < h) (hj : j < r) : r * i + j < r * h := tcm_idx hi hj

private theorem ent_prod {w c h d S i j : ℕ} {a b : ℕ → ℕ} (hS : S = w * c) (h5 : 5 ≤ 2 ^ w)
    (hi : i < h) (hj : j < c) :
    ent w S (pk w (c * h) (fun t => (∑ k ∈ Finset.range d, a (c * (t / c) + k) * b (c * k + t % c)) % 5))
      i j = ∑ k ∈ Finset.range d, ((a (c * i + k) : ℕ) : ZMod 5) * ((b (c * k + j) : ℕ) : ZMod 5) := by
  rw [ent_pk hS (fun t _ => lt_of_lt_of_le (Nat.mod_lt _ (by norm_num)) h5) (idx hi hj),
    (dm_eq hj).1, (dm_eq hj).2, ZMod.natCast_mod]
  push_cast
  rfl

private theorem prod_core {w r h m d S T CM : ℕ} {a b : ℕ → ℕ} (hw : 0 < w) (hS : S = w * r)
    (hCM : CM = pk w (r * h) (fun t => if t % r = 0 then 2 ^ w - 1 else 0))
    (h5 : 5 ≤ 2 ^ w) (ha : ∀ t < r * h, a t < 5) (hb : ∀ t < r * m, b t < 5) (hdr : d ≤ r)
    (hdm : d ≤ m) (hT : 5 * 2 ^ T ≤ 2 ^ (w - 1)) (hB : 16 * d < 2 ^ (w - 1))
    (hB2 : 16 * d < 5 * 2 ^ (T + 1)) :
    redP w (pk w (r * h) (fun _ => 1)) (pk w (r * h) (fun _ => 2 ^ (w - 1))) 5 T
      (∑ k ∈ Finset.range d, ((pk w (r * h) a >>> (w * k)) &&& CM) *
        ((pk w (r * m) b >>> (S * k)) &&& (2 ^ S - 1))) =
    pk w (r * h) (fun t => (∑ k ∈ Finset.range d, a (r * (t / r) + k) * b (r * k + t % r)) % 5) := by
  rw [tcm_core hw hS rfl hCM (fun t ht => lt_of_lt_of_le (ha t ht) h5)
    (fun t ht => lt_of_lt_of_le (hb t ht) h5) hdr hdm]
  have hbd : ∀ t < r * h, ∑ k ∈ Finset.range d, a (r * (t / r) + k) * b (r * k + t % r) ≤ 16 * d := by
    intro t ht
    have hr : 0 < r := Nat.pos_of_ne_zero fun h0 => by simp [h0] at ht
    have h2 : t / r < h := (Nat.div_lt_iff_lt_mul hr).2 (by rw [Nat.mul_comm]; exact ht)
    exact tcm_bound (fun k hk => ha _ (idx h2 (by omega)))
      (fun k hk => hb _ (idx (by omega) (Nat.mod_lt _ hr)))
  exact redP_pk hw hT (fun t ht => by have := hbd t ht; omega) (fun t ht => by have := hbd t ht; omega)

private theorem bc_facts {C : BConsts} (hC : bConstsOK C = true) :
    C.L7 = pk 12 (111 * 7) (fun _ => 1) ∧ C.H7 = pk 12 (111 * 7) (fun _ => 2 ^ (12 - 1)) ∧
    C.CM7 = pk 12 (111 * 7) (fun t => if t % 111 = 0 then 2 ^ 12 - 1 else 0) ∧
    C.ONE7 = rep1 1344 7 ∧
    C.MASK7 = pk 12 (111 * 7) (fun t => if t % 111 < 7 then 2 ^ 12 - 1 else 0) ∧
    C.LV = pk 12 111 (fun _ => 1) ∧ C.HV = pk 12 111 (fun _ => 2 ^ (12 - 1)) ∧
    C.LW = pk 12 7 (fun _ => 1) ∧ C.HW = pk 12 7 (fun _ => 2 ^ (12 - 1)) ∧
    C.LF = pk 12 (111 * 111) (fun _ => 1) ∧ C.HF = pk 12 (111 * 111) (fun _ => 2 ^ (12 - 1)) ∧
    C.CMF = pk 12 (111 * 111) (fun t => if t % 111 = 0 then 2 ^ 12 - 1 else 0) := by
  unfold bConstsOK at hC
  obtain ⟨h1, hC⟩ := rawAnd_true hC
  obtain ⟨h2, hC⟩ := rawAnd_true hC
  obtain ⟨h3, hC⟩ := rawAnd_true hC
  obtain ⟨h4, hC⟩ := rawAnd_true hC
  obtain ⟨h5, hC⟩ := rawAnd_true hC
  obtain ⟨h6, hC⟩ := rawAnd_true hC
  obtain ⟨h7, hC⟩ := rawAnd_true hC
  obtain ⟨h8, hC⟩ := rawAnd_true hC
  obtain ⟨h9, hC⟩ := rawAnd_true hC
  obtain ⟨h10, hC⟩ := rawAnd_true hC
  obtain ⟨h11, hC⟩ := rawAnd_true hC
  obtain ⟨h12, -⟩ := rawAnd_true hC
  have e1 : C.L7 = pk 12 (111 * 7) (fun _ => 1) :=
    (Nat.eq_of_beq_eq_true h1).trans (tcm_L (w := 12) (n := 111 * 7) (by norm_num))
  have e6 : C.LV = pk 12 111 (fun _ => 1) :=
    (Nat.eq_of_beq_eq_true h6).trans (tcm_L (w := 12) (n := 111) (by norm_num))
  have e8 : C.LW = pk 12 7 (fun _ => 1) :=
    (Nat.eq_of_beq_eq_true h8).trans (tcm_L (w := 12) (n := 7) (by norm_num))
  have e10 : C.LF = pk 12 (111 * 111) (fun _ => 1) :=
    (Nat.eq_of_beq_eq_true h10).trans (tcm_L (w := 12) (n := 111 * 111) (by norm_num))
  refine ⟨e1, ?_, ?_, Nat.eq_of_beq_eq_true h4, ?_, e6, ?_, e8, ?_, e10, ?_, ?_⟩
  · rw [Nat.eq_of_beq_eq_true h2, e1]; exact tcm_H
  · exact (Nat.eq_of_beq_eq_true h3).trans (tcm_CM (w := 12) (r := 111) (h := 7) (by norm_num)
      (by norm_num))
  · exact (Nat.eq_of_beq_eq_true h5).trans (cols_pk (w := 12) (r := 111) (s := 7) (h := 7)
      (by norm_num) (by norm_num) (by norm_num))
  · rw [Nat.eq_of_beq_eq_true h7, e6]; exact tcm_H
  · rw [Nat.eq_of_beq_eq_true h9, e8]; exact tcm_H
  · rw [Nat.eq_of_beq_eq_true h11, e10]; exact tcm_H
  · exact (Nat.eq_of_beq_eq_true h12).trans (tcm_CM (w := 12) (r := 111) (h := 111) (by norm_num)
      (by norm_num))

private theorem sc_facts {C : SConsts} (hC : sConstsOK C = true) :
    C.Lb = pk 11 (49 * 64) (fun _ => 1) ∧ C.Hb = pk 11 (49 * 64) (fun _ => 2 ^ (11 - 1)) ∧
    C.CMb = pk 11 (49 * 64) (fun t => if t % 49 = 0 then 2 ^ 11 - 1 else 0) ∧
    C.L7 = pk 11 (7 * 7) (fun _ => 1) ∧ C.H7 = pk 11 (7 * 7) (fun _ => 2 ^ (11 - 1)) ∧
    C.CM7 = pk 11 (7 * 7) (fun t => if t % 7 = 0 then 2 ^ 11 - 1 else 0) := by
  unfold sConstsOK at hC
  obtain ⟨h1, hC⟩ := rawAnd_true hC
  obtain ⟨h2, hC⟩ := rawAnd_true hC
  obtain ⟨h3, hC⟩ := rawAnd_true hC
  obtain ⟨h4, hC⟩ := rawAnd_true hC
  obtain ⟨h5, hC⟩ := rawAnd_true hC
  obtain ⟨h6, -⟩ := rawAnd_true hC
  have e1 : C.Lb = pk 11 (49 * 64) (fun _ => 1) :=
    (Nat.eq_of_beq_eq_true h1).trans (tcm_L (w := 11) (n := 49 * 64) (by norm_num))
  have e4 : C.L7 = pk 11 (7 * 7) (fun _ => 1) :=
    (Nat.eq_of_beq_eq_true h4).trans (tcm_L (w := 11) (n := 7 * 7) (by norm_num))
  refine ⟨e1, ?_, ?_, e4, ?_, ?_⟩
  · rw [Nat.eq_of_beq_eq_true h2, e1]; exact tcm_H
  · exact (Nat.eq_of_beq_eq_true h3).trans (tcm_CM (w := 11) (r := 49) (h := 64) (by norm_num)
      (by norm_num))
  · rw [Nat.eq_of_beq_eq_true h5, e4]; exact tcm_H
  · exact (Nat.eq_of_beq_eq_true h6).trans (tcm_CM (w := 11) (r := 7) (h := 7) (by norm_num)
      (by norm_num))

private theorem bMul_pk {C : BConsts} (hC : bConstsOK C = true) {x g : ℕ → ℕ}
    (hx : ∀ t < 111 * 7, x t < 5) (hg : ∀ t < 111 * 111, g t < 5) :
    bMul C (pk 12 (111 * 7) x) (pk 12 (111 * 111) g) = pk 12 (111 * 7) (fun t =>
      (∑ k ∈ Finset.range (37 * 3), x (111 * (t / 111) + k) * g (111 * k + t % 111)) % 5) := by
  obtain ⟨hL, hH, hCM, -⟩ := bc_facts hC
  unfold bMul rowsMulR rmB
  rw [tcm_RM, hL, hH, tcm_grp rfl]
  exact prod_core (S := nat_lit 1332) (by norm_num) (by norm_num) hCM (by norm_num) hx hg
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

private theorem fMul_pk {C : BConsts} (hC : bConstsOK C = true) {x g : ℕ → ℕ}
    (hx : ∀ t < 111 * 111, x t < 5) (hg : ∀ t < 111 * 111, g t < 5) :
    fMul C (pk 12 (111 * 111) x) (pk 12 (111 * 111) g) = pk 12 (111 * 111) (fun t =>
      (∑ k ∈ Finset.range 111, x (111 * (t / 111) + k) * g (111 * k + t % 111)) % 5) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hL, hH, hCM⟩ := bc_facts hC
  unfold fMul mulR rmB
  rw [tcm_RM, hL, hH, mulU_eq]
  exact prod_core (S := nat_lit 1332) (by norm_num) (by norm_num) hCM (by norm_num) hx hg
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

private theorem bMul7_pk {C : BConsts} (hC : bConstsOK C = true) {x g : ℕ → ℕ}
    (hx : ∀ t < 111 * 7, x t < 5) (hg : ∀ t < 111 * 7, g t < 5) :
    bMul7 C (pk 12 (111 * 7) x) (pk 12 (111 * 7) g) = pk 12 (111 * 7) (fun t =>
      (∑ k ∈ Finset.range 7, x (111 * (t / 111) + k) * g (111 * k + t % 111)) % 5) := by
  obtain ⟨hL, hH, hCM, -⟩ := bc_facts hC
  unfold bMul7 mulR rmB
  rw [tcm_RM, hL, hH, mulU_eq]
  exact prod_core (S := nat_lit 1332) (by norm_num) (by norm_num) hCM (by norm_num) hx hg
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

private theorem sMul_pk {C : SConsts} (hC : sConstsOK C = true) {x g : ℕ → ℕ}
    (hx : ∀ t < 7 * 7, x t < 5) (hg : ∀ t < 7 * 7, g t < 5) :
    sMul C (pk 11 (7 * 7) x) (pk 11 (7 * 7) g) = pk 11 (7 * 7) (fun t =>
      (∑ k ∈ Finset.range 7, x (7 * (t / 7) + k) * g (7 * k + t % 7)) % 5) := by
  obtain ⟨-, -, -, hL, hH, hCM⟩ := sc_facts hC
  unfold sMul mulR
  rw [tcm_RM, hL, hH, mulU_eq]
  exact prod_core (S := nat_lit 77) (by norm_num) (by norm_num) hCM (by norm_num) hx hg
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

private theorem sBlk_pk {C : SConsts} (hC : sConstsOK C = true) {x g : ℕ → ℕ}
    (hx : ∀ t < 49 * 64, x t < 5) (hg : ∀ t < 49 * 49, g t < 5) :
    sBlk C (pk 11 (49 * 64) x) (pk 11 (49 * 49) g) = pk 11 (49 * 64) (fun t =>
      (∑ k ∈ Finset.range (7 * 7), x (49 * (t / 49) + k) * g (49 * k + t % 49)) % 5) := by
  obtain ⟨hL, hH, hCM, -⟩ := sc_facts hC
  unfold sBlk rowsMulR
  rw [tcm_RM, hL, hH, tcm_grp rfl]
  exact prod_core (S := nat_lit 539) (by norm_num) (by norm_num) hCM (by norm_num) hx hg
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

private theorem sum_fin {n : ℕ} (F : ℕ → ZMod 5) :
    ∑ k : Fin n, F k.val = ∑ k ∈ Finset.range n, F k := Fin.sum_univ_eq_sum_range F n

theorem bMul_sound {C : BConsts} (hC : bConstsOK C = true) {X G : ℕ} (hX : LCanon 12 7 111 X)
    (hG : LCanon 12 111 111 G) :
    LCanon 12 7 111 (bMul C X G) ∧ blkM (bMul C X G) = blkM X * bigM G := by
  obtain ⟨x, hxe, hx, -⟩ := lc_lanes (n := 111 * 7) (by norm_num) hX le_rfl
  obtain ⟨g, hge, hg, -⟩ := lc_lanes (n := 111 * 111) (by norm_num) hG le_rfl
  rw [hxe, hge]
  rw [bMul_pk hC hx hg]
  refine ⟨lc_of_pk (by norm_num) (fun t _ => Nat.mod_lt _ (by norm_num))
    (fun t h1 h2 => absurd h2 (by omega)) le_rfl, ?_⟩
  ext i j
  simp only [blkM, bigM, Matrix.mul_apply]
  rw [ent_prod (by norm_num) (by norm_num) i.isLt j.isLt]
  rw [show 37 * 3 = 111 from rfl, ← sum_fin]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [ent_pk (by norm_num) (fun t ht => lt_of_lt_of_le (hx t ht) (by norm_num)) (idx i.isLt k.isLt),
    ent_pk (by norm_num) (fun t ht => lt_of_lt_of_le (hg t ht) (by norm_num)) (idx k.isLt j.isLt)]

theorem fMul_sound {C : BConsts} (hC : bConstsOK C = true) {X Y : ℕ} (hX : LCanon 12 111 111 X)
    (hY : LCanon 12 111 111 Y) :
    LCanon 12 111 111 (fMul C X Y) ∧ bigM (fMul C X Y) = bigM X * bigM Y := by
  obtain ⟨x, hxe, hx, -⟩ := lc_lanes (n := 111 * 111) (by norm_num) hX le_rfl
  obtain ⟨g, hge, hg, -⟩ := lc_lanes (n := 111 * 111) (by norm_num) hY le_rfl
  rw [hxe, hge]
  rw [fMul_pk hC hx hg]
  refine ⟨lc_of_pk (by norm_num) (fun t _ => Nat.mod_lt _ (by norm_num))
    (fun t h1 h2 => absurd h2 (by omega)) le_rfl, ?_⟩
  ext i j
  simp only [bigM, Matrix.mul_apply]
  rw [ent_prod (by norm_num) (by norm_num) i.isLt j.isLt, ← sum_fin]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [ent_pk (by norm_num) (fun t ht => lt_of_lt_of_le (hx t ht) (by norm_num)) (idx i.isLt k.isLt),
    ent_pk (by norm_num) (fun t ht => lt_of_lt_of_le (hg t ht) (by norm_num)) (idx k.isLt j.isLt)]

theorem sMul_sound {C : SConsts} (hC : sConstsOK C = true) {X Y : ℕ} (hX : LCanon 11 7 7 X)
    (hY : LCanon 11 7 7 Y) :
    LCanon 11 7 7 (sMul C X Y) ∧ smM (sMul C X Y) = smM X * smM Y := by
  obtain ⟨x, hxe, hx, -⟩ := lc_lanes (n := 7 * 7) (by norm_num) hX le_rfl
  obtain ⟨g, hge, hg, -⟩ := lc_lanes (n := 7 * 7) (by norm_num) hY le_rfl
  rw [hxe, hge]
  rw [sMul_pk hC hx hg]
  refine ⟨lc_of_pk (by norm_num) (fun t _ => Nat.mod_lt _ (by norm_num))
    (fun t h1 h2 => absurd h2 (by omega)) le_rfl, ?_⟩
  ext i j
  simp only [smM, Matrix.mul_apply]
  rw [ent_prod (by norm_num) (by norm_num) i.isLt j.isLt, ← sum_fin]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [ent_pk (by norm_num) (fun t ht => lt_of_lt_of_le (hx t ht) (by norm_num)) (idx i.isLt k.isLt),
    ent_pk (by norm_num) (fun t ht => lt_of_lt_of_le (hg t ht) (by norm_num)) (idx k.isLt j.isLt)]

theorem sBlk_sound {C : SConsts} (hC : sConstsOK C = true) {r X K : ℕ} (hr : r ≤ 64)
    (hX : LCanon 11 r 49 X) (hK : LCanon 11 49 49 K) :
    LCanon 11 r 49 (sBlk C X K) ∧ ∀ q < r, vec49 (sBlk C X K / 2 ^ (539 * q)) =
      Matrix.vecMul (vec49 (X / 2 ^ (539 * q))) (kM K) := by
  obtain ⟨x, hxe, hx, hx0⟩ := lc_lanes (n := 49 * 64) (by norm_num) hX (by omega)
  obtain ⟨g, hge, hg, -⟩ := lc_lanes (n := 49 * 49) (by norm_num) hK le_rfl
  rw [hxe, hge]
  rw [sBlk_pk hC hx hg]
  have hrow : ∀ t, 49 * r ≤ t → ∀ k < 49, x (49 * (t / 49) + k) = 0 := by
    intro t ht k hk
    refine hx0 _ ?_
    have : r ≤ t / 49 := (Nat.le_div_iff_mul_le (by norm_num)).2 (by rw [Nat.mul_comm]; exact ht)
    omega
  refine ⟨lc_of_pk (by norm_num) (fun t _ => Nat.mod_lt _ (by norm_num)) (fun t h1 _ => ?_)
    (by omega), fun q hq => ?_⟩
  · rw [Finset.sum_eq_zero fun k hk => by
      rw [hrow t h1 k (by have := Finset.mem_range.1 hk; omega), Nat.zero_mul], Nat.zero_mod]
  · funext j
    have hd : ∀ (Z m : ℕ), Z / 2 ^ (539 * q) / 2 ^ (0 * 0 + 11 * m) % 2 ^ 11 =
        Z / 2 ^ (539 * q + 11 * m) % 2 ^ 11 := by
      intro Z m
      rw [Nat.div_div_eq_div_mul, ← Nat.pow_add, Nat.zero_mul, Nat.zero_add]
    simp only [vec49, Matrix.vecMul, dotProduct, kM, ent]
    rw [hd]
    have e1 := ent_prod (w := 11) (c := 49) (h := 64) (d := 7 * 7) (S := 539) (a := x) (b := g)
      (by norm_num) (by norm_num) (show q < 64 by omega) j.isLt
    unfold ent at e1
    rw [e1, show 7 * 7 = 49 from rfl, ← sum_fin]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hd]
    have e2 := ent_pk (w := 11) (c := 49) (S := 539) (i := q) (j := k.val) (by norm_num)
      (fun t ht => lt_of_lt_of_le (hx t ht) (by norm_num)) (idx (show q < 64 by omega) k.isLt)
    have e3 := ent_pk (w := 11) (c := 49) (S := 539) (i := k.val) (j := j.val) (by norm_num)
      (fun t ht => lt_of_lt_of_le (hg t ht) (by norm_num)) (idx k.isLt j.isLt)
    unfold ent at e2 e3
    rw [e2, e3]

private theorem cols7_pk {y : ℕ → ℕ} (hy : ∀ t < 111 * 7, y t < 5) {o : ℕ} (ho : o ≤ 104) :
    ((pk 12 (111 * 7) y >>> (12 * o)) &&&
        pk 12 (111 * 7) (fun t => if t % 111 < 7 then 2 ^ 12 - 1 else 0)) =
      pk 12 (111 * 7) (fun t => if t % 111 < 7 then y (t + o) else 0) := by
  have hy' : ∀ t < 111 * 7, y t < 2 ^ 12 := fun t ht => lt_of_lt_of_le (hy t ht) (by norm_num)
  have hm : ∀ t < 111 * 7, (if t % 111 < 7 then 2 ^ 12 - 1 else 0) < 2 ^ 12 :=
    fun t _ => by split <;> norm_num
  refine pk_of_fld (by norm_num) (fld_congr (fld_and (fld_shr o (fld_pk hy')) (fld_pk hm))
    fun t => ?_) (fun t ht => by split <;> [exact hy' _ (by omega); norm_num])
  by_cases ht : t < 111 * 7
  · by_cases h7 : t % 111 < 7
    · have h3 : t + o < 111 * 7 := by omega
      simp only [ht, h7, h3, ↓reduceIte]
      rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (hy' _ h3)]
    · simp [ht, h7]
  · simp [ht]

private theorem span_core {C : BConsts} (hC : bConstsOK C = true) {o : ℕ} (ho : o ≤ 104) {N Y : ℕ}
    (hN : LCanon 12 7 111 N) (hY : LCanon 12 7 111 Y)
    (h : bMul7 C ((Y >>> (12 * o)) &&& C.MASK7) N = Y) :
    ∀ i j : Fin 7, ∀ l : Fin 111, blkM Y i l =
      ∑ k : Fin 7, blkM Y i ⟨o + k.val, by omega⟩ * blkM N k l := by
  obtain ⟨-, -, -, -, hM, -⟩ := bc_facts hC
  obtain ⟨y, hye, hy, -⟩ := lc_lanes (n := 111 * 7) (by norm_num) hY le_rfl
  obtain ⟨n, hne, hn, -⟩ := lc_lanes (n := 111 * 7) (by norm_num) hN le_rfl
  rw [hye, hne] at h
  rw [hye, hne]
  rw [hM, cols7_pk hy ho, bMul7_pk hC (fun t ht => by split <;> [exact hy _ (by omega); norm_num])
    hn] at h
  intro i _ l
  simp only [blkM]
  conv_lhs => rw [← h]
  have e := ent_prod (w := 12) (c := 111) (h := 7) (d := 7) (S := 1332)
    (a := fun s => if s % 111 < 7 then y (s + o) else 0) (b := n) (by norm_num) (by norm_num)
    i.isLt l.isLt
  beta_reduce at e
  rw [e, ← sum_fin]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hk : (111 * i.val + k.val) % 111 < 7 := by rw [(dm_eq (by omega)).2]; exact k.isLt
  rw [if_pos hk, ent_pk (by norm_num) (fun t ht => lt_of_lt_of_le (hy t ht) (by norm_num))
      (show 111 * i.val + (o + k.val) < 111 * 7 by omega),
    ent_pk (by norm_num) (fun t ht => lt_of_lt_of_le (hn t ht) (by norm_num)) (idx k.isLt l.isLt),
    show 111 * i.val + k.val + o = 111 * i.val + (o + k.val) by ring]

theorem sameSpanL_sound {C : BConsts} (hC : bConstsOK C = true) {N Y : ℕ}
    (hN : LCanon 12 7 111 N) (hY : LCanon 12 7 111 Y) (h : sameSpanL C N Y = true) :
    blkM Y = lastCols (blkM Y) * blkM N := by
  have h' : bMul7 C ((Y >>> (12 * 104)) &&& C.MASK7) N = Y := Nat.eq_of_beq_eq_true h
  ext i l
  rw [span_core hC le_rfl hN hY h' i ⟨0, by norm_num⟩ l, Matrix.mul_apply]
  rfl

theorem sameSpan_sound {C : BConsts} (hC : bConstsOK C = true) {N Y : ℕ}
    (hN : LCanon 12 7 111 N) (hY : LCanon 12 7 111 Y) (h : sameSpan C N Y = true) :
    blkM Y = firstCols (blkM Y) * blkM N := by
  have h' : bMul7 C ((Y >>> (12 * 0)) &&& C.MASK7) N = Y := by
    rw [Nat.mul_zero, Nat.shiftRight_zero]
    exact Nat.eq_of_beq_eq_true h
  ext i l
  rw [span_core hC (by norm_num) hN hY h' i ⟨0, by norm_num⟩ l, Matrix.mul_apply]
  simp only [Nat.zero_add]
  rfl

end CFSG.KS.LyOm.MC

end
