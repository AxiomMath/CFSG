module

public import CFSG.Certificates.Kernel.Spor.OrdSound
import CFSG.Certificates.Kernel.Spor.PackFld

public section

namespace CFSG.KS.OrdCanon

open CFSG.KC.Ord CFSG.KS.Ord CFSG.KS.PackFld

private theorem andB_true {a b : Bool} (h : andB a b = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all [andB]

private theorem andB_intro {a b : Bool} (ha : a = true) (hb : b = true) : andB a b = true := by
  subst ha hb
  rfl

private noncomputable def pk (w n : Nat) (g : Nat → Nat) : Nat :=
  ∑ t ∈ Finset.range n, g t * 2 ^ (w * t)

private theorem pk_succ (w n : Nat) (g : Nat → Nat) :
    pk w (n + 1) g = pk w n g + g n * 2 ^ (w * n) :=
  Finset.sum_range_succ _ _

private theorem pk_congr {w n : Nat} {f g : Nat → Nat} (h : ∀ t < n, f t = g t) :
    pk w n f = pk w n g :=
  Finset.sum_congr rfl fun t ht => by rw [h t (Finset.mem_range.1 ht)]

private theorem pk_add (w n : Nat) (f g : Nat → Nat) :
    pk w n f + pk w n g = pk w n (fun t => f t + g t) := by
  unfold pk
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun t _ => (Nat.add_mul _ _ _).symm

private theorem pk_sub {w n : Nat} {f g : Nat → Nat} (h : ∀ t < n, g t ≤ f t) :
    pk w n f - pk w n g = pk w n (fun t => f t - g t) := by
  have e : pk w n g + pk w n (fun t => f t - g t) = pk w n f := by
    rw [pk_add]
    exact pk_congr fun t ht => Nat.add_sub_cancel' (h t ht)
  omega

private theorem pk_mul (w n c : Nat) (f : Nat → Nat) :
    pk w n f * c = pk w n (fun t => f t * c) := by
  unfold pk
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun t _ => Nat.mul_right_comm _ _ _

private theorem pk_zero (w n : Nat) : pk w n (fun _ => 0) = 0 := by
  simp [pk]

private theorem pk_lt {w n : Nat} {g : Nat → Nat} (hg : ∀ t < n, g t < 2 ^ w) :
    pk w n g < 2 ^ (w * n) := by
  induction n with
  | zero => simp [pk]
  | succ n ih =>
    rw [pk_succ]
    have h1 := ih fun t ht => hg t (by omega)
    have h2 : g n + 1 ≤ 2 ^ w := hg n (by omega)
    have h3 := Nat.mul_le_mul_right (2 ^ (w * n)) h2
    have e : 2 ^ (w * (n + 1)) = 2 ^ w * 2 ^ (w * n) := by
      rw [← Nat.pow_add, Nat.mul_succ, Nat.add_comm]
    rw [e]
    rw [Nat.add_mul, Nat.one_mul] at h3
    omega

private theorem fld_pk {w n : Nat} {g : Nat → Nat} (hg : ∀ t < n, g t < 2 ^ w) :
    Fld w (pk w n g) (fun t => if t < n then g t else 0) := by
  induction n with
  | zero => exact fld_congr (fld_zero w) fun t => by simp
  | succ n ih =>
    have ih' := ih fun t ht => hg t (by omega)
    have hl := pk_lt (w := w) (n := n) (g := g) fun t ht => hg t (by omega)
    have e : pk w (n + 1) g = g n <<< (w * n) ||| pk w n g := by
      rw [pk_succ, ← Nat.shiftLeft_add_eq_or_of_lt hl, Nat.shiftLeft_eq, Nat.add_comm]
    rw [e]
    refine fld_congr (fld_or (fld_shl n (fld_one (hg n (by omega)))) ih') fun t => ?_
    rcases Nat.lt_trichotomy t n with h | h | h
    · have h1 : ¬ n ≤ t := by omega
      have h2 : t < n + 1 := by omega
      simp [h, h1, h2]
    · subst h
      simp
    · have h1 : n ≤ t := by omega
      have h2 : t - n ≠ 0 := by omega
      have h3 : ¬ t < n := by omega
      have h4 : ¬ t < n + 1 := by omega
      simp [h1, h2, h3, h4]

private theorem fld_unique {w X Y : Nat} {g : Nat → Nat} (hw : 0 < w) (hX : Fld w X g)
    (hY : Fld w Y g) : X = Y := by
  apply Nat.eq_of_testBit_eq
  intro b
  have hb : b = w * (b / w) + b % w := (Nat.div_add_mod b w).symm
  rw [hb, hX _ _ (Nat.mod_lt _ hw), hY _ _ (Nat.mod_lt _ hw)]

private theorem pk_of_fld {w n X : Nat} {g : Nat → Nat} (hw : 0 < w)
    (hX : Fld w X (fun t => if t < n then g t else 0)) (hg : ∀ t < n, g t < 2 ^ w) :
    X = pk w n g :=
  fld_unique hw hX (fld_pk hg)

private theorem fld_and {w A B : Nat} {g h : Nat → Nat} (hA : Fld w A g) (hB : Fld w B h) :
    Fld w (A &&& B) (fun i => g i &&& h i) := by
  intro i k hk
  rw [Nat.testBit_and, hA i k hk, hB i k hk, Nat.testBit_and]

private theorem fld_lane (w X : Nat) : Fld w X (fun t => lane w X t) := by
  intro i k hk
  unfold lane
  rw [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.add_comm k]
  simp [hk]

private theorem pk_lane {w n X : Nat} (hw : 0 < w) (hX : X < 2 ^ (w * n)) :
    X = pk w n (lane w X) := by
  refine pk_of_fld hw (fld_congr (fld_lane w X) fun t => ?_)
    fun t _ => Nat.mod_lt _ (Nat.two_pow_pos w)
  by_cases ht : t < n
  · simp [ht]
  · have h : X < 2 ^ (w * t) :=
      Nat.lt_of_lt_of_le hX (Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left w (by omega)))
    simp only [ht, ↓reduceIte]
    unfold lane
    rw [Nat.div_eq_of_lt h, Nat.zero_mod]

private theorem testBit_top {y k : Nat} (hy : y < 2 * 2 ^ k) :
    y.testBit k = decide (2 ^ k ≤ y) := by
  by_cases h : 2 ^ k ≤ y
  · obtain ⟨r, rfl⟩ : ∃ r, y = 2 ^ k + r := ⟨y - 2 ^ k, by omega⟩
    rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow (by omega)]
    simp
  · rw [Nat.testBit_lt_two_pow (by omega)]
    simp [h]

private theorem or_top {a k : Nat} (ha : a < 2 ^ k) : a ||| 2 ^ k = a + 2 ^ k := by
  have h := Nat.shiftLeft_add_eq_or_of_lt ha 1
  rw [Nat.shiftLeft_eq, Nat.one_mul] at h
  rw [Nat.lor_comm, ← h, Nat.add_comm]

private theorem and_top {y k : Nat} (hy : y < 2 * 2 ^ k) :
    y &&& 2 ^ k = if 2 ^ k ≤ y then 2 ^ k else 0 := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and, Nat.testBit_two_pow]
  by_cases hj : k = j
  · subst hj
    rw [testBit_top hy]
    by_cases h : 2 ^ k ≤ y <;> simp [h]
  · by_cases h : 2 ^ k ≤ y <;> simp [h, hj]

private theorem two_pow_pred {w : Nat} (hw : 0 < w) : 2 ^ w = 2 * 2 ^ (w - 1) := by
  obtain ⟨v, rfl⟩ : ∃ v, w = v + 1 := ⟨w - 1, by omega⟩
  rw [Nat.add_sub_cancel, Nat.pow_succ, Nat.mul_comm]

private theorem or_H {w n : Nat} (hw : 0 < w) {f : Nat → Nat} (hf : ∀ t < n, f t < 2 ^ (w - 1)) :
    pk w n f ||| pk w n (fun _ => 2 ^ (w - 1)) = pk w n (fun t => f t + 2 ^ (w - 1)) := by
  have e2 := two_pow_pred hw
  have h0 := Nat.two_pow_pos (w - 1)
  have hp : (2 : Nat) ^ (w - 1) < 2 ^ w := by omega
  refine pk_of_fld hw (fld_congr (fld_or (fld_pk fun t ht => (by have := hf t ht; omega))
    (fld_pk (n := n) fun _ _ => hp)) fun t => ?_) fun t ht => by have := hf t ht; omega
  by_cases ht : t < n
  · simp only [ht, ↓reduceIte]
    exact or_top (hf t ht)
  · simp [ht]

private theorem top_H {w n : Nat} (hw : 0 < w) {f : Nat → Nat} {c : Nat}
    (hf : ∀ t < n, f t < 2 ^ (w - 1)) (hc : c ≤ 2 ^ (w - 1)) :
    ((pk w n f ||| pk w n (fun _ => 2 ^ (w - 1))) - c * pk w n (fun _ => 1)) &&&
        pk w n (fun _ => 2 ^ (w - 1)) =
      pk w n (fun t => if c ≤ f t then 2 ^ (w - 1) else 0) := by
  have e2 := two_pow_pred hw
  have h0 := Nat.two_pow_pos (w - 1)
  rw [or_H hw hf, Nat.mul_comm, pk_mul, pk_sub (fun t _ => by omega)]
  refine pk_of_fld hw (fld_congr (fld_and (fld_pk (fun t ht => by have := hf t ht; omega))
    (fld_pk (n := n) (g := fun _ => 2 ^ (w - 1)) (fun _ _ => by omega))) fun t => ?_)
    (fun t _ => by split <;> omega)
  by_cases ht : t < n
  · simp only [ht, ↓reduceIte, Nat.one_mul]
    have := hf t ht
    rw [and_top (by omega)]
    by_cases hcf : c ≤ f t
    · have h1 : 2 ^ (w - 1) ≤ f t + 2 ^ (w - 1) - c := by omega
      simp [hcf, h1]
    · have h1 : ¬ 2 ^ (w - 1) ≤ f t + 2 ^ (w - 1) - c := by omega
      simp [hcf, h1]
  · simp [ht]

private theorem rep1_eq {s m : Nat} (hs : 0 < s) :
    rep1 s m = ∑ i ∈ Finset.range m, 2 ^ (s * i) := by
  have key : ∀ m, (2 ^ s - 1) * ∑ i ∈ Finset.range m, 2 ^ (s * i) + 1 = 2 ^ (s * m) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, Nat.mul_add, Nat.add_right_comm, ih, Nat.mul_succ, Nat.pow_add]
      obtain ⟨q, hq⟩ : ∃ q, 2 ^ s = q + 1 :=
        ⟨2 ^ s - 1, by have := Nat.one_le_two_pow (n := s); omega⟩
      rw [hq, Nat.add_sub_cancel]
      ring
  have h2 : 2 ≤ 2 ^ s := by
    have := Nat.pow_le_pow_right (n := 2) (by omega) hs
    simpa using this
  unfold rep1
  change (1 <<< (s * m) - 1) / (1 <<< s - 1) = _
  rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.one_mul, Nat.one_mul, ← key m, Nat.add_sub_cancel]
  exact Nat.mul_div_cancel_left _ (by omega)

theorem validM_of_canon {p w S d T L H CM RM ONE LV HV X : Nat}
    (hc : constsOK p w S d T L H CM RM ONE LV HV = true) (hX : Canon p d w X) :
    validM p (d * S) L H X = true := by
  unfold constsOK at hc
  obtain ⟨hp2, hc⟩ := andB_true hc
  obtain ⟨hS, hc⟩ := andB_true hc
  obtain ⟨-, hc⟩ := andB_true hc
  obtain ⟨hT, hc⟩ := andB_true hc
  obtain ⟨-, hc⟩ := andB_true hc
  obtain ⟨hL, hc⟩ := andB_true hc
  obtain ⟨hH, -⟩ := andB_true hc
  have hS' : S = d * w := Nat.eq_of_beq_eq_true hS
  have hT' : p * 2 ^ T ≤ 2 ^ (w - 1) := by
    have h : p <<< T ≤ 1 <<< (w - 1) := Nat.le_of_ble_eq_true hT
    rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.one_mul] at h
    exact h
  have hp : p ≤ 2 ^ (w - 1) := Nat.le_trans (Nat.le_mul_of_pos_right p (Nat.two_pow_pos T)) hT'
  have hp2' : 2 ≤ p := Nat.le_of_ble_eq_true hp2
  have hw : 0 < w := by
    rcases Nat.eq_zero_or_pos w with h0 | h0
    · subst h0
      simp only [Nat.zero_sub, Nat.pow_zero] at hp
      omega
    · exact h0
  have hL' : L = pk w (d * d) (fun _ => 1) := by
    have h : L = rep1 w (d * d) := Nat.eq_of_beq_eq_true hL
    rw [h, rep1_eq hw]
    simp [pk]
  have hH' : H = pk w (d * d) (fun _ => 2 ^ (w - 1)) := by
    have h : H = L <<< (w - 1) := Nat.eq_of_beq_eq_true hH
    rw [h, Nat.shiftLeft_eq, hL', pk_mul]
    exact pk_congr fun _ _ => Nat.one_mul _
  obtain ⟨hX1, hX2⟩ := hX
  have hXe := pk_lane hw hX1
  have hlt : ∀ t < d * d, lane w X t < 2 ^ (w - 1) := fun t ht =>
    Nat.lt_of_lt_of_le (hX2 t ht) hp
  have e2 := two_pow_pred hw
  unfold validM
  refine andB_intro ?_ (andB_intro ?_ ?_)
  · rw [Nat.beq_eq]
    change X >>> (d * S) = 0
    rw [Nat.shiftRight_eq_div_pow, hS']
    have e : d * (d * w) = w * (d * d) := by ring
    rw [e]
    exact Nat.div_eq_of_lt hX1
  · rw [Nat.beq_eq]
    change X &&& H = 0
    rw [hH', hXe]
    have h0 := Nat.two_pow_pos (w - 1)
    rw [← pk_zero w (d * d)]
    refine pk_of_fld hw (fld_congr (fld_and (fld_pk (fun t ht => by have := hlt t ht; omega))
      (fld_pk (n := d * d) (g := fun _ => 2 ^ (w - 1)) (fun _ _ => by omega))) fun t => ?_)
      (fun _ _ => Nat.two_pow_pos w)
    by_cases ht : t < d * d
    · simp only [ht, ↓reduceIte]
      have := hlt t ht
      rw [and_top (by omega)]
      simp [Nat.not_le.2 this]
    · simp [ht]
  · rw [Nat.beq_eq]
    change ((X ||| H) - p * L) &&& H = 0
    rw [hH', hL', hXe, top_H hw hlt hp,
      pk_congr (g := fun _ => 0) fun t ht => by simp [Nat.not_le.2 (hX2 t ht)]]
    exact pk_zero w (d * d)

end CFSG.KS.OrdCanon

end
