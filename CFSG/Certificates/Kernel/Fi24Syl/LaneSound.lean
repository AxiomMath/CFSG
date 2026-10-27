module

public import CFSG.Certificates.Kernel.Fi24Syl.MatSound
import all CFSG.Certificates.Kernel.Spor.OrdSound
import CFSG.Certificates.Kernel.Spor.PackFld

public section

namespace CFSG.KS.Fi24Syl

open CFSG.KC.Ord CFSG.KC.Loop CFSG.KC.Fi24Syl CFSG.KS.Ord CFSG.KS.PackFld Matrix

@[expose] noncomputable def vrow (r : ℕ) : Fin 7 → ZMod 3 :=
  fun j => (((r + 1) % 2187 / 3 ^ j.val % 3 : ℕ) : ZMod 3)

@[expose] noncomputable def zF (Y : Matrix (Fin 7) (Fin 7) (ZMod 3)) (r : ℕ) : ℕ :=
  if vecMul (vrow r) Y = 0 then 1 else 0

@[expose] noncomputable def fixZ (Y : Matrix (Fin 7) (Fin 7) (ZMod 3)) : ℕ :=
  ∑ r ∈ Finset.range 2187, zF Y r * 2 ^ (42 * r)

@[expose] noncomputable def fixC (Y : Matrix (Fin 7) (Fin 7) (ZMod 3)) : ℕ :=
  ∑ r ∈ Finset.range 2187, zF Y r

private theorem shl' (a b : ℕ) : Nat.shiftLeft a b = a * 2 ^ b := Nat.shiftLeft_eq a b

private theorem shr' (a b : ℕ) : Nat.shiftRight a b = a / 2 ^ b := Nat.shiftRight_eq_div_pow a b

private theorem natRec_sum (F : ℕ → ℕ) : ∀ k,
    Nat.rec (motive := fun _ => ℕ) 0 (fun l ih2 => Nat.add ih2 (F l)) k =
      ∑ l ∈ Finset.range k, F l
  | 0 => by simp
  | k + 1 => by
    rw [Finset.sum_range_succ, ← natRec_sum F k]
    rfl

private theorem natRec_sum' (F : ℕ → ℕ) : ∀ k,
    Nat.rec (motive := fun _ => ℕ) 0 (fun l ih2 => Nat.add (F l) ih2) k =
      ∑ l ∈ Finset.range k, F l
  | 0 => by simp
  | k + 1 => by
    rw [Finset.sum_range_succ, ← natRec_sum' F k]
    exact Nat.add_comm _ _

theorem sumBelow_eq {m hi : ℕ} (f : ℕ → ℕ) (hm : m ≤ 64 * hi) :
    sumBelow m hi f = ∑ i ∈ Finset.range m, f i := by
  have g : ∀ hi, sumBelow m hi f =
      ∑ i ∈ Finset.range (64 * hi), Bool.rec (motive := fun _ => ℕ) 0 (f i) (Nat.blt i m) := by
    intro hi
    induction hi with
    | zero => simp [sumBelow]
    | succ hi ih =>
      have e : sumBelow m (hi + 1) f = Nat.add (Nat.rec (motive := fun _ => ℕ) 0 (fun l ih2 =>
          Nat.add ((fun i => Bool.rec (motive := fun _ => ℕ) 0 (f i) (Nat.blt i m))
            (Nat.add (Nat.shiftLeft hi 6) l)) ih2) 64) (sumBelow m hi f) := rfl
      have e2 : ∀ l, Nat.add (Nat.shiftLeft hi 6) l = 64 * hi + l := fun l => by
        change hi <<< 6 + l = _
        rw [Nat.shiftLeft_eq, Nat.mul_comm]
      rw [e, natRec_sum', ih, Nat.mul_succ, Finset.sum_range_add]
      simp only [e2]
      exact Nat.add_comm _ _
  rw [g]
  obtain ⟨d, hd⟩ : ∃ d, 64 * hi = m + d := ⟨64 * hi - m, by omega⟩
  rw [hd, Finset.sum_range_add]
  have h2 : ∑ l ∈ Finset.range d,
      Bool.rec (motive := fun _ => ℕ) 0 (f (m + l)) (Nat.blt (m + l) m) = 0 := by
    apply Finset.sum_eq_zero
    intro l _
    have hb : Nat.blt (m + l) m = false := by
      cases e : Nat.blt (m + l) m
      · rfl
      · rw [Nat.blt_eq] at e
        omega
    rw [hb]
  rw [h2, Nat.add_zero]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hb : Nat.blt i m = true := by
    rw [Nat.blt_eq]
    exact Finset.mem_range.1 hi
  rw [hb]

private theorem pk_mul_pk (w n k : ℕ) (f g : ℕ → ℕ) :
    pk w n f * pk w k g = pk w (n + k) (fun s => ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range k,
      if i + j = s then f i * g j else 0) := by
  unfold pk
  rw [Finset.sum_mul_sum]
  symm
  calc _ = ∑ s ∈ Finset.range (n + k), ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range k,
        (if i + j = s then f i * g j * 2 ^ (w * s) else 0) := by
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => ?_
        split <;> simp
    _ = ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range k, ∑ s ∈ Finset.range (n + k),
        (if i + j = s then f i * g j * 2 ^ (w * s) else 0) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_comm]
    _ = _ := by
        refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
        have h1 := Finset.mem_range.1 hi
        have h2 := Finset.mem_range.1 hj
        rw [Finset.sum_ite_eq (Finset.range (n + k)) (i + j),
          if_pos (Finset.mem_range.2 (by omega)), Nat.mul_add, Nat.pow_add]
        ring

private theorem conv_single {n k s : ℕ} (f g : ℕ → ℕ) :
    (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range k, if i + j = s then f i * g j else 0) =
      ∑ j ∈ Finset.range k, if j ≤ s ∧ s - j < n then f (s - j) * g j else 0 := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  have e : ∀ i, (if i + j = s then f i * g j else 0) =
      if s - j = i ∧ j ≤ s then f i * g j else 0 := by
    intro i
    by_cases h : i + j = s
    · rw [if_pos h, if_pos ⟨by omega, by omega⟩]
    · rw [if_neg h, if_neg (by omega)]
  simp only [e]
  by_cases hjs : j ≤ s
  · simp only [hjs, and_true, true_and]
    rw [Finset.sum_ite_eq]
    by_cases hn : s - j < n
    · rw [if_pos (Finset.mem_range.2 hn), if_pos hn]
    · rw [if_neg (fun h => hn (Finset.mem_range.1 h)), if_neg hn]
  · simp [hjs]

private theorem rep1_pk (s m : ℕ) (hs : 0 < s) : rep1 s m = pk s m (fun _ => 1) := by
  rw [rep1_eq (Or.inl hs)]
  unfold pk
  simp

private noncomputable def av (t : ℕ) : ℕ := (t / 7 + 1) % 2187 / 3 ^ (t % 7) % 3

private theorem av_lt (t : ℕ) : av t < 3 := Nat.mod_lt _ (by norm_num)

private theorem vecOf_eq (m : ℕ) :
    vecOf m = ∑ j ∈ Finset.range 7, m / 3 ^ j % 3 * 2 ^ (6 * j) := by
  unfold vecOf
  rw [natRec_sum (fun j => Nat.shiftLeft (Nat.mod (Nat.div m (Nat.pow 3 j)) 3) (Nat.mul 6 j))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [shl']
  rfl

private theorem AV_eq : sumBelow 2187 35 vecRow = pk 6 (7 * 2187) av := by
  rw [sumBelow_eq _ (by norm_num), pk_rows]
  refine Finset.sum_congr rfl fun r _ => ?_
  unfold vecRow
  rw [shl', vecOf_eq, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j hj => ?_
  obtain ⟨e1, e2⟩ := dm_eq (d := 7) (i := r) (Finset.mem_range.1 hj)
  unfold av
  have e : 6 * j + Nat.mul 42 r = 6 * (7 * r + j) := by
    change 6 * j + 42 * r = _
    ring
  rw [e1, e2, Nat.mul_assoc, ← Nat.pow_add, e]
  rfl

private theorem CMa_eq : Nat.mul 63 (rep1 42 2187) =
    pk 6 (7 * 2187) (fun t => if t % 7 = 0 then 63 else 0) := by
  change 63 * rep1 42 2187 = _
  rw [rep1_eq (Or.inl (by norm_num)), pk_rows, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single 0]
  · have e : 42 * i = 6 * (7 * i + 0) := by ring
    have e2 : (7 * i + 0) % 7 = 0 := by simp
    rw [e, e2, if_pos rfl]
  · intro j hj hj0
    rw [(dm_eq (i := i) (Finset.mem_range.1 hj)).2, if_neg hj0, Nat.zero_mul]
  · intro h0
    exact absurd (Finset.mem_range.2 (by norm_num)) h0

private theorem rows6 (g : ℕ → ℕ) :
    pk 6 (7 * 2187) (fun t => if t % 7 = 6 then g (t / 7) else 0) =
      pk 42 2187 (fun r => g r * 2 ^ 36) := by
  rw [pk_rows]
  unfold pk
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single 6]
  · have e2 : (7 * i + 6) % 7 = 6 := by omega
    have e3 : (7 * i + 6) / 7 = i := by omega
    rw [if_pos e2, e3, Nat.mul_assoc, ← Nat.pow_add]
    congr 2
    ring
  · intro j hj hj6
    rw [(dm_eq (i := i) (Finset.mem_range.1 hj)).2, if_neg hj6, Nat.zero_mul]
  · intro h0
    exact absurd (Finset.mem_range.2 (by norm_num)) h0

private theorem TL_eq (c : ℕ) : Nat.mul c (Nat.shiftLeft (rep1 42 2187) 36) =
    pk 42 2187 (fun _ => c * 2 ^ 36) := by
  change c * (rep1 42 2187 <<< 36) = _
  rw [Nat.shiftLeft_eq, rep1_pk 42 2187 (by norm_num), pk_mul, Nat.mul_comm, pk_mul]
  exact pk_congr fun _ _ => by ring

private noncomputable def prodR (a b : ℕ → ℕ) (t : ℕ) : ℕ :=
  ∑ k ∈ Finset.range 7, a (7 * (t / 7) + k) * b (7 * k + t % 7)

private theorem idx_lt' {d m i j : ℕ} (hi : i < m) (hj : j < d) : d * i + j < d * m := by
  have := Nat.mul_le_mul_left d (Nat.succ_le_of_lt hi)
  rw [Nat.mul_succ] at this
  omega

private theorem colm_eq {m k : ℕ} {a : ℕ → ℕ} (ha : ∀ t < 7 * m, a t < 2 ^ 6) (hk : k < 7) :
    (pk 6 (7 * m) a >>> (6 * k)) &&& pk 6 (7 * m) (fun t => if t % 7 = 0 then 63 else 0) =
      ∑ i ∈ Finset.range m, a (7 * i + k) * 2 ^ (6 * (7 * i)) := by
  have hm : ∀ t < 7 * m, (if t % 7 = 0 then 63 else 0) < 2 ^ 6 :=
    fun t _ => by split <;> norm_num
  have hlt : ∀ t < 7 * m, t % 7 = 0 → t + k < 7 * m := by
    intro t ht h0
    have h1 := Nat.div_add_mod t 7
    have h2 : t / 7 < m := (Nat.div_lt_iff_lt_mul (by norm_num)).2 (by linarith)
    have := idx_lt' (d := 7) h2 hk
    rw [h0] at h1
    omega
  have hF : Fld 6 ((pk 6 (7 * m) a >>> (6 * k)) &&&
      pk 6 (7 * m) (fun t => if t % 7 = 0 then 63 else 0))
      (fun t => if t < 7 * m then (if t % 7 = 0 then a (t + k) else 0) else 0) := by
    refine fld_congr (fld_and (fld_shr k (fld_pk ha)) (fld_pk hm)) fun t => ?_
    by_cases ht : t < 7 * m
    · by_cases h0 : t % 7 = 0
      · have h3 := hlt t ht h0
        simp only [ht, h0, h3, ↓reduceIte]
        have e63 : (63 : ℕ) = 2 ^ 6 - 1 := by norm_num
        rw [e63, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (ha _ h3)]
      · simp [ht, h0]
    · simp [ht]
  have hb : ∀ t < 7 * m, (if t % 7 = 0 then a (t + k) else 0) < 2 ^ 6 := by
    intro t ht
    by_cases h0 : t % 7 = 0
    · rw [if_pos h0]
      exact ha _ (hlt t ht h0)
    · rw [if_neg h0]
      norm_num
  rw [pk_of_fld (by norm_num) hF hb, pk_rows]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single 0]
  · have e2 : (7 * i + 0) % 7 = 0 := by simp
    rw [e2, if_pos rfl, Nat.add_zero]
  · intro j hj hj0
    rw [(dm_eq (i := i) (Finset.mem_range.1 hj)).2, if_neg hj0, Nat.zero_mul]
  · intro h0
    exact absurd (Finset.mem_range.2 (by norm_num)) h0

private theorem mulUm_pk {m : ℕ} {a b : ℕ → ℕ} (ha : ∀ t < 7 * m, a t < 2 ^ 6)
    (hb : ∀ t < 7 * 7, b t < 2 ^ 6) :
    mulU 6 42 7 (pk 6 (7 * m) (fun t => if t % 7 = 0 then 63 else 0)) (2 ^ 42 - 1)
      (pk 6 (7 * m) a) (pk 6 (7 * 7) b) = pk 6 (7 * m) (prodR a b) := by
  rw [mulU_eq]
  calc _ = ∑ k ∈ Finset.range 7, ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range 7,
        a (7 * i + k) * b (7 * k + j) * 2 ^ (6 * (7 * i + j)) := by
        refine Finset.sum_congr rfl fun k hk => ?_
        have hk' := Finset.mem_range.1 hk
        have hr := row_eq (w := 6) (d := 7) (by norm_num) hb hk'
        have e42 : (42 : ℕ) * k = 7 * 6 * k := by ring
        have e2 : (2 : ℕ) ^ 42 - 1 = 2 ^ (6 * 7) - 1 := by norm_num
        rw [colm_eq ha hk', e42, e2, hr, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        unfold pk
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Nat.mul_add 6, Nat.pow_add]
        ring
    _ = ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range 7, ∑ k ∈ Finset.range 7,
        a (7 * i + k) * b (7 * k + j) * 2 ^ (6 * (7 * i + j)) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = _ := by
        rw [pk_rows]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj => ?_
        obtain ⟨e1, e2⟩ := dm_eq (d := 7) (i := i) (Finset.mem_range.1 hj)
        unfold prodR
        rw [e1, e2, Finset.sum_mul]

private theorem prodR_le {a b : ℕ → ℕ} (ha : ∀ t, a t < 3) (hb : ∀ t, b t < 3) (t : ℕ) :
    prodR a b t ≤ 28 := by
  unfold prodR
  calc _ ≤ ∑ _k ∈ Finset.range 7, 4 := Finset.sum_le_sum fun k _ => by
          have h1 : a (7 * (t / 7) + k) ≤ 2 := by have := ha (7 * (t / 7) + k); omega
          have h2 : b (7 * k + t % 7) ≤ 2 := by have := hb (7 * k + t % 7); omega
          exact (Nat.mul_le_mul h1 h2).trans (by norm_num)
    _ = 28 := by simp

private theorem Y_eq {nn : ℕ → ℕ} (hnn : ∀ t, nn t < 3) :
    redP 6 (rep1 6 15309) (Nat.mul 32 (rep1 6 15309)) 3 3
      (mulU 6 42 7 (Nat.mul 63 (rep1 42 2187)) RM (sumBelow 2187 35 vecRow) (pk 6 (7 * 7) nn)) =
      pk 6 (7 * 2187) (fun t => prodR av nn t % 3) := by
  have hL : rep1 6 15309 = pk 6 (7 * 2187) (fun _ => 1) := rep1_pk 6 _ (by norm_num)
  have hH : Nat.mul 32 (rep1 6 15309) = pk 6 (7 * 2187) (fun _ => 2 ^ (6 - 1)) := by
    change 32 * _ = _
    rw [hL, Nat.mul_comm, pk_mul]
    exact pk_congr fun _ _ => by norm_num
  have hRM : RM = 2 ^ 42 - 1 := by decide +kernel
  rw [hH, hL, CMa_eq, AV_eq, hRM,
    mulUm_pk (fun t _ => Nat.lt_of_lt_of_le (av_lt t) (by norm_num))
      (fun t _ => Nat.lt_of_lt_of_le (hnn t) (by norm_num))]
  exact redP_pk (by norm_num) (by norm_num)
    (fun t _ => by have := prodR_le av_lt hnn t; norm_num; omega)
    (fun t _ => by have := prodR_le av_lt hnn t; norm_num; omega)

private theorem F1_eq {y : ℕ → ℕ} (hy : ∀ t, y t < 3) :
    Nat.land (Nat.add (pk 6 (7 * 2187) y) (Nat.mul 31 (rep1 6 15309))) (Nat.mul 32 (rep1 6 15309)) =
      pk 6 (7 * 2187) (fun t => if y t = 0 then 0 else 1) * 2 ^ 5 := by
  have hL : rep1 6 15309 = pk 6 (7 * 2187) (fun _ => 1) := rep1_pk 6 _ (by norm_num)
  change (pk 6 (7 * 2187) y + 31 * rep1 6 15309) &&& (32 * rep1 6 15309) = _
  rw [hL, Nat.mul_comm 31, Nat.mul_comm 32, pk_mul, pk_mul, pk_add, pk_mul]
  refine pk_of_fld (w := 6) (n := 7 * 2187) (g := fun t => (if y t = 0 then 0 else 1) * 2 ^ 5)
    (by norm_num) (fld_congr (fld_and (fld_pk (n := 7 * 2187)
    (g := fun t => y t + 1 * 31) fun t _ => by have := hy t; norm_num; omega)
    (fld_pk (n := 7 * 2187) (g := fun _ => 1 * 32) fun _ _ => by norm_num)) fun t => ?_)
    fun t _ => by split <;> norm_num
  by_cases ht : t < 7 * 2187
  · simp only [ht, ↓reduceIte, Nat.one_mul]
    have := hy t
    have e32 : (32 : ℕ) = 2 ^ 5 := by norm_num
    rw [e32, and_top (by omega)]
    by_cases h0 : y t = 0
    · simp [h0]
    · have h1 : 2 ^ 5 ≤ y t + 31 := by omega
      simp [h0, h1]
  · simp [ht]

private theorem LV7_eq : LV7 = pk 6 7 (fun _ => 1) := by
  unfold pk
  decide +kernel

private theorem conv7 (f : ℕ → ℕ) {r : ℕ} (hr : r < 2187) :
    (∑ i ∈ Finset.range (7 * 2187), ∑ j ∈ Finset.range 7,
      if i + j = 7 * r + 6 then f i * 1 else 0) = ∑ i ∈ Finset.range 7, f (7 * r + i) := by
  rw [conv_single]
  rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := Finset.mem_range.1 hj
  rw [if_pos ⟨by omega, by omega⟩, Nat.mul_one]
  congr 1
  omega

private theorem E_eq {fl : ℕ → ℕ} (hfl : ∀ t, fl t ≤ 1) :
    Nat.land (Nat.mul (pk 6 (7 * 2187) fl) LV7) (Nat.mul 63 (Nat.shiftLeft (rep1 42 2187) 36)) =
      pk 42 2187 (fun r => (∑ i ∈ Finset.range 7, fl (7 * r + i)) * 2 ^ 36) := by
  set cv : ℕ → ℕ := fun s => ∑ i ∈ Finset.range (7 * 2187), ∑ j ∈ Finset.range 7,
    if i + j = s then fl i * 1 else 0 with hcv
  have hcv7 : ∀ s, cv s ≤ 7 := by
    intro s
    simp only [hcv]
    rw [conv_single]
    calc _ ≤ ∑ _j ∈ Finset.range 7, 1 := Finset.sum_le_sum fun j _ => by
            split
            · rw [Nat.mul_one]
              exact hfl _
            · omega
      _ = 7 := by simp
  have hT : Nat.mul 63 (Nat.shiftLeft (rep1 42 2187) 36) =
      pk 6 (7 * 2187) (fun t => if t % 7 = 6 then 63 else 0) := by
    rw [TL_eq]
    exact (rows6 (fun _ => 63)).symm
  change pk 6 (7 * 2187) fl * LV7 &&& Nat.mul 63 (Nat.shiftLeft (rep1 42 2187) 36) = _
  rw [hT, LV7_eq, pk_mul_pk]
  have hF := fld_and (fld_pk (w := 6) (n := 7 * 2187 + 7) (g := cv)
    (fun t _ => by have := hcv7 t; omega))
    (fld_pk (w := 6) (n := 7 * 2187) (g := fun t => if t % 7 = 6 then 63 else 0)
      (fun t _ => by split <;> norm_num))
  rw [pk_of_fld (n := 7 * 2187) (g := fun t => if t % 7 = 6 then cv t else 0) (by norm_num)
    (fld_congr hF fun t => ?_) (fun t _ => by split <;> (try have := hcv7 t) <;> omega),
    ← rows6 (fun r => ∑ i ∈ Finset.range 7, fl (7 * r + i))]
  · refine pk_congr fun t ht => ?_
    by_cases h6 : t % 7 = 6
    · rw [if_pos h6, if_pos h6]
      have ht' : 7 * (t / 7) + 6 = t := by omega
      have hr : t / 7 < 2187 := by omega
      have h := conv7 fl hr
      rw [ht'] at h
      exact h
    · rw [if_neg h6, if_neg h6]
  · by_cases ht : t < 7 * 2187
    · have ht' : t < 7 * 2187 + 7 := by omega
      simp only [ht, ht', ↓reduceIte]
      by_cases h6 : t % 7 = 6
      · simp only [h6, ↓reduceIte]
        have e63 : (63 : ℕ) = 2 ^ 6 - 1 := by norm_num
        rw [e63, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (by have := hcv7 t; omega)]
      · simp [h6]
    · simp [ht]

private theorem Z_eq {cn : ℕ → ℕ} (hcn : ∀ r, cn r ≤ 7) :
    Nat.shiftRight (Nat.sub (Nat.mul 32 (Nat.shiftLeft (rep1 42 2187) 36))
      (Nat.land (Nat.add (pk 42 2187 (fun r => cn r * 2 ^ 36))
        (Nat.mul 31 (Nat.shiftLeft (rep1 42 2187) 36)))
        (Nat.mul 32 (Nat.shiftLeft (rep1 42 2187) 36)))) 41 =
      pk 42 2187 (fun r => if cn r = 0 then 1 else 0) := by
  rw [TL_eq, TL_eq]
  change (pk 42 2187 (fun _ => 32 * 2 ^ 36) - ((pk 42 2187 (fun r => cn r * 2 ^ 36) +
    pk 42 2187 (fun _ => 31 * 2 ^ 36)) &&& pk 42 2187 (fun _ => 32 * 2 ^ 36))) >>> 41 = _
  rw [pk_add]
  have h41 : ∀ r, (cn r * 2 ^ 36 + 31 * 2 ^ 36) &&& 32 * 2 ^ 36 =
      if cn r = 0 then 0 else 2 ^ 41 := by
    intro r
    have e : (32 : ℕ) * 2 ^ 36 = 2 ^ 41 := by norm_num
    have := hcn r
    rw [e, and_top (by omega)]
    by_cases h0 : cn r = 0
    · simp only [h0, Nat.zero_mul, Nat.zero_add, if_pos]
      norm_num
    · have h1 : 2 ^ 41 ≤ cn r * 2 ^ 36 + 31 * 2 ^ 36 := by
        have : 1 ≤ cn r := by omega
        nlinarith
      simp [h0, h1]
  have hA : (pk 42 2187 (fun r => cn r * 2 ^ 36 + 31 * 2 ^ 36) &&& pk 42 2187 (fun _ => 32 * 2 ^ 36)) =
      pk 42 2187 (fun r => if cn r = 0 then 0 else 2 ^ 41) := by
    refine pk_of_fld (by norm_num) (fld_congr (fld_and (fld_pk (fun r _ => by
      have := hcn r; norm_num; omega)) (fld_pk (n := 2187) (g := fun _ => 32 * 2 ^ 36)
      (fun _ _ => by norm_num))) fun r => ?_) (fun r _ => by split <;> norm_num)
    by_cases hr : r < 2187
    · simp only [hr, ↓reduceIte]
      exact h41 r
    · simp [hr]
  rw [hA, pk_sub (fun r _ => by split <;> norm_num), Nat.shiftRight_eq_div_pow]
  have e : pk 42 2187 (fun r => 32 * 2 ^ 36 - if cn r = 0 then 0 else 2 ^ 41) =
      pk 42 2187 (fun r => if cn r = 0 then 1 else 0) * 2 ^ 41 := by
    rw [pk_mul]
    exact pk_congr fun r _ => by split <;> norm_num
  rw [e, Nat.mul_div_cancel _ (by positivity)]

private theorem fc_eq {z : ℕ → ℕ} (hz : ∀ r, z r ≤ 1) :
    Nat.land (Nat.shiftRight (Nat.mul (pk 42 2187 z) (rep1 42 2187)) 91812) RM =
      ∑ r ∈ Finset.range 2187, z r := by
  have hRM : RM = 2 ^ 42 - 1 := by decide +kernel
  have land' : ∀ a b : ℕ, Nat.land a b = a &&& b := fun _ _ => rfl
  have mul' : ∀ a b : ℕ, Nat.mul a b = a * b := fun _ _ => rfl
  rw [land', mul', shr', hRM, Nat.and_two_pow_sub_one_eq_mod, rep1_pk 42 _ (by norm_num),
    pk_mul_pk]
  have hb : ∀ s, (∑ i ∈ Finset.range 2187, ∑ j ∈ Finset.range 2187,
      if i + j = s then z i * 1 else 0) ≤ 2187 := by
    intro s
    rw [conv_single]
    calc _ ≤ ∑ _j ∈ Finset.range 2187, 1 := Finset.sum_le_sum fun j _ => by
            split
            · rw [Nat.mul_one]
              exact hz _
            · omega
      _ = 2187 := by simp
  have e : (91812 : ℕ) = 42 * 2186 := by norm_num
  have h := lane_pk (w := 42) (n := 2187 + 2187)
    (fun t _ => Nat.lt_of_le_of_lt (hb t) (by norm_num)) (by norm_num : 2186 < 2187 + 2187)
  unfold lane at h
  rw [e, h, conv_single, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := Finset.mem_range.1 hj
  rw [if_pos ⟨by omega, by omega⟩, Nat.mul_one]
  congr 1
  omega

private theorem prodR_cast {nn : ℕ → ℕ} (r i : ℕ) (hr : r < 2187) (hi : i < 7) :
    ((prodR av nn (7 * r + i) % 3 : ℕ) : ZMod 3) =
      ∑ k : Fin 7, vrow r k * ((nn (7 * k.val + i) : ℕ) : ZMod 3) := by
  obtain ⟨e1, e2⟩ := dm_eq (d := 7) (i := r) hi
  unfold prodR
  rw [ZMod.natCast_mod, e1, e2, Nat.cast_sum, Finset.sum_range (fun k =>
    ((av (7 * r + k) * nn (7 * k + i) : ℕ) : ZMod 3))]
  refine Finset.sum_congr rfl fun k _ => ?_
  obtain ⟨f1, f2⟩ := dm_eq (d := 7) (i := r) k.isLt
  rw [Nat.cast_mul]
  unfold av vrow
  rw [f1, f2]

private theorem cnt_zero {nn : ℕ → ℕ} {N : ℕ} (hN : N = pk 6 (7 * 7) nn)
    (hnn : ∀ t < 7 * 7, nn t < 2 ^ 6) {r : ℕ} (hr : r < 2187) :
    (∑ i ∈ Finset.range 7, (if prodR av nn (7 * r + i) % 3 = 0 then 0 else 1)) = 0 ↔
      vecMul (vrow r) (mat7 N) = 0 := by
  rw [Finset.sum_eq_zero_iff]
  constructor
  · intro h
    funext i
    have h1 := h i.val (Finset.mem_range.2 i.isLt)
    have h2 : prodR av nn (7 * r + i.val) % 3 = 0 := by
      by_contra hc
      rw [if_neg hc] at h1
      exact absurd h1 one_ne_zero
    have h3 := prodR_cast (nn := nn) r i.val hr i.isLt
    rw [h2, Nat.cast_zero] at h3
    rw [Pi.zero_apply, vecMul, dotProduct, h3]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hN, mat7_apply, lane_pk hnn (idx_lt k.isLt i.isLt)]
  · intro h i hi
    have h3 := prodR_cast (nn := nn) r i hr (Finset.mem_range.1 hi)
    have h4 := congrFun h ⟨i, Finset.mem_range.1 hi⟩
    rw [Pi.zero_apply, vecMul, dotProduct] at h4
    have h5 : ((prodR av nn (7 * r + i) % 3 : ℕ) : ZMod 3) = 0 := by
      rw [h3, ← h4]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hN, mat7_apply, lane_pk hnn (idx_lt k.isLt (Finset.mem_range.1 hi))]
    have h6 : prodR av nn (7 * r + i) % 3 = 0 := by
      have := congrArg ZMod.val h5
      rwa [ZMod.val_natCast, ZMod.val_zero, Nat.mod_mod] at this
    rw [if_pos h6]

private theorem contrib_parts {N : ℕ} (hN : C7 N) :
    ∃ nn' : ℕ → ℕ, N = pk 6 (7 * 7) nn' ∧ (∀ t, nn' t < 3) ∧ (∀ t < 7 * 7, nn' t < 2 ^ 6) := by
  set nn : ℕ → ℕ := lane 6 N with hnn_def
  have hNpk : N = pk 6 (7 * 7) nn := pk_lane (by norm_num) hN.1
  have hnn3 : ∀ t, nn t < 3 ∨ 7 * 7 ≤ t := by
    intro t
    by_cases ht : t < 7 * 7
    · exact Or.inl (hN.2 t ht)
    · exact Or.inr (by omega)
  set nn' : ℕ → ℕ := fun t => if t < 7 * 7 then nn t else 0 with hnn'
  have hN' : N = pk 6 (7 * 7) nn' := by
    rw [hNpk]
    exact pk_congr fun t ht => by simp [hnn', ht]
  have hnn'3 : ∀ t, nn' t < 3 := by
    intro t
    simp only [hnn']
    split
    · rcases hnn3 t with h | h
      · exact h
      · omega
    · norm_num
  have hnn'w : ∀ t < 7 * 7, nn' t < 2 ^ 6 := fun t _ => Nat.lt_of_lt_of_le (hnn'3 t) (by norm_num)
  exact ⟨nn', hN', hnn'3, hnn'w⟩

private noncomputable def yF (nn : ℕ → ℕ) (t : ℕ) : ℕ := prodR av nn t % 3

private noncomputable def flF (y : ℕ → ℕ) (t : ℕ) : ℕ := if y t = 0 then 0 else 1

private noncomputable def cnF (fl : ℕ → ℕ) (r : ℕ) : ℕ := ∑ i ∈ Finset.range 7, fl (7 * r + i)

private noncomputable def zzF (cn : ℕ → ℕ) (r : ℕ) : ℕ := if cn r = 0 then 1 else 0

private theorem Y_eq' {nn : ℕ → ℕ} (hnn : ∀ t, nn t < 3) :
    redP 6 (rep1 6 15309) (Nat.mul 32 (rep1 6 15309)) 3 3
      (mulU 6 42 7 (Nat.mul 63 (rep1 42 2187)) RM (sumBelow 2187 35 vecRow) (pk 6 (7 * 7) nn)) =
      pk 6 (7 * 2187) (yF nn) := Y_eq hnn

private theorem F1_eq' {y : ℕ → ℕ} (hy : ∀ t, y t < 3) :
    Nat.land (Nat.add (pk 6 (7 * 2187) y) (Nat.mul 31 (rep1 6 15309))) (Nat.mul 32 (rep1 6 15309)) =
      pk 6 (7 * 2187) (flF y) * 2 ^ 5 := F1_eq hy

private theorem S_eq (fl : ℕ → ℕ) :
    Nat.shiftRight (pk 6 (7 * 2187) fl * 2 ^ 5) 5 = pk 6 (7 * 2187) fl := by
  rw [shr', Nat.mul_div_cancel _ (by norm_num)]

private theorem E_eq' {fl : ℕ → ℕ} (hfl : ∀ t, fl t ≤ 1) :
    Nat.land (Nat.mul (pk 6 (7 * 2187) fl) LV7) (Nat.mul 63 (Nat.shiftLeft (rep1 42 2187) 36)) =
      pk 42 2187 (fun r => cnF fl r * 2 ^ 36) := E_eq hfl

private theorem Z_eq' {cn : ℕ → ℕ} (hcn : ∀ r, cn r ≤ 7) :
    Nat.shiftRight (Nat.sub (Nat.mul 32 (Nat.shiftLeft (rep1 42 2187) 36))
      (Nat.land (Nat.add (pk 42 2187 (fun r => cn r * 2 ^ 36))
        (Nat.mul 31 (Nat.shiftLeft (rep1 42 2187) 36)))
        (Nat.mul 32 (Nat.shiftLeft (rep1 42 2187) 36)))) 41 =
      pk 42 2187 (zzF cn) := Z_eq hcn

private theorem ble_true {a b : ℕ} (h : a ≤ b) : Nat.ble a b = true := by
  rw [Nat.ble_eq]
  exact h

private theorem ble_false {a b : ℕ} (h : ¬ a ≤ b) : Nat.ble a b = false := by
  cases e : Nat.ble a b with
  | false => rfl
  | true =>
    rw [Nat.ble_eq] at e
    exact absurd e h

private theorem contrib_tail (Z c : ℕ) : Nat.add (Nat.add 0 Z)
    (Nat.add (Bool.rec (motive := fun _ => ℕ) 0 (Nat.shiftLeft Z 21) (Nat.ble 243 c))
      (Bool.rec (motive := fun _ => ℕ) (Nat.shiftLeft 1 91854) 0 (Nat.ble c 243))) =
    Z + ((if 243 ≤ c then Z * 2 ^ 21 else 0) + (if c ≤ 243 then 0 else 2 ^ 91854)) := by
  rw [shl', shl', Nat.one_mul]
  by_cases h1 : 243 ≤ c <;> by_cases h2 : c ≤ 243
  · rw [if_pos h1, if_pos h2, ble_true h1, ble_true h2]
    dsimp only
    simp only [Nat.add_eq, Nat.zero_add, Nat.add_zero]
  · rw [if_pos h1, if_neg h2, ble_true h1, ble_false h2]
    dsimp only
    simp only [Nat.add_eq, Nat.zero_add]
  · rw [if_neg h1, if_pos h2, ble_false h1, ble_true h2]
    dsimp only
    simp only [Nat.add_eq, Nat.zero_add, Nat.add_zero]
  · omega

private theorem contrib_gen {AV La Ha L31 CMa TL T31 T32 T63 R1 N Y F1 S E Z fc : ℕ}
    (hY : redP 6 La Ha 3 3 (mulU 6 42 7 CMa RM AV N) = Y)
    (hF1 : Nat.land (Nat.add Y L31) Ha = F1) (hS : Nat.shiftRight F1 5 = S)
    (hE : Nat.land (Nat.mul S LV7) T63 = E)
    (hZ : Nat.shiftRight (Nat.sub T32 (Nat.land (Nat.add E T31) T32)) 41 = Z)
    (hfc : Nat.land (Nat.shiftRight (Nat.mul Z R1) 91812) RM = fc) :
    contribK AV La Ha L31 CMa TL T31 T32 T63 R1 N 0 =
      Z + ((if 243 ≤ fc then Z * 2 ^ 21 else 0) + (if fc ≤ 243 then 0 else 2 ^ 91854)) := by
  unfold contribK
  simp only [strictN_eqO]
  rw [hY, hF1, hS, hE, hZ, hfc]
  exact contrib_tail Z fc

theorem contrib_sound {N : ℕ} (hN : C7 N) :
    contribK (sumBelow 2187 35 vecRow) (rep1 6 15309) (Nat.mul 32 (rep1 6 15309))
      (Nat.mul 31 (rep1 6 15309)) (Nat.mul 63 (rep1 42 2187)) (Nat.shiftLeft (rep1 42 2187) 36)
      (Nat.mul 31 (Nat.shiftLeft (rep1 42 2187) 36)) (Nat.mul 32 (Nat.shiftLeft (rep1 42 2187) 36))
      (Nat.mul 63 (Nat.shiftLeft (rep1 42 2187) 36)) (rep1 42 2187) N 0 =
      fixZ (mat7 N) + ((if 243 ≤ fixC (mat7 N) then fixZ (mat7 N) * 2 ^ 21 else 0) +
        (if fixC (mat7 N) ≤ 243 then 0 else 2 ^ 91854)) := by
  obtain ⟨nn, hN', hnn3, hnnw⟩ := contrib_parts hN
  have hY : redP 6 (rep1 6 15309) (Nat.mul 32 (rep1 6 15309)) 3 3
      (mulU 6 42 7 (Nat.mul 63 (rep1 42 2187)) RM (sumBelow 2187 35 vecRow) N) =
      pk 6 (7 * 2187) (yF nn) := by
    rw [hN']
    exact Y_eq' hnn3
  have hy3 : ∀ t, yF nn t < 3 := fun t => Nat.mod_lt _ (by norm_num)
  have hfl1 : ∀ t, flF (yF nn) t ≤ 1 := fun t => by
    unfold flF
    split <;> omega
  have hcn7 : ∀ r, cnF (flF (yF nn)) r ≤ 7 := by
    intro r
    calc cnF (flF (yF nn)) r ≤ ∑ _i ∈ Finset.range 7, 1 :=
          Finset.sum_le_sum fun i _ => hfl1 _
      _ = 7 := by simp
  have hz1 : ∀ r, zzF (cnF (flF (yF nn))) r ≤ 1 := fun r => by
    unfold zzF
    split <;> omega
  have hzF : ∀ r < 2187, zzF (cnF (flF (yF nn))) r = zF (mat7 N) r := by
    intro r hr
    have h := cnt_zero (nn := nn) hN' hnnw hr
    have e : cnF (flF (yF nn)) r =
        ∑ i ∈ Finset.range 7, (if prodR av nn (7 * r + i) % 3 = 0 then 0 else 1) := rfl
    unfold zzF zF
    rw [e]
    by_cases h0 : (∑ i ∈ Finset.range 7, (if prodR av nn (7 * r + i) % 3 = 0 then 0 else 1)) = 0
    · rw [if_pos h0, if_pos (h.1 h0)]
    · rw [if_neg h0, if_neg (fun h' => h0 (h.2 h'))]
  have hZfix : pk 42 2187 (zzF (cnF (flF (yF nn)))) = fixZ (mat7 N) := by
    unfold fixZ pk
    exact Finset.sum_congr rfl fun r hr => by rw [hzF r (Finset.mem_range.1 hr)]
  have hCfix : ∑ r ∈ Finset.range 2187, zzF (cnF (flF (yF nn))) r = fixC (mat7 N) := by
    unfold fixC
    exact Finset.sum_congr rfl fun r hr => hzF r (Finset.mem_range.1 hr)
  refine (contrib_gen (TL := Nat.shiftLeft (rep1 42 2187) 36) hY (F1_eq' hy3) (S_eq _)
    (E_eq' hfl1) (Z_eq' hcn7) (fc_eq hz1)).trans ?_
  rw [hZfix, hCfix]

end CFSG.KS.Fi24Syl

end
