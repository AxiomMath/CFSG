module

public import Certificates.Data.Kernel.U35Pk
public import CFSG.Certificates.Kernel.U35Pk.Prod
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Certificates.U35Pk

open CFSG.RankThree.PartOne.HNB Matrix

set_option exponentiation.threshold 2100

theorem allR_spec (f : ℕ → Bool) : ∀ (n lo : ℕ), U35Pk.allR f n lo = true → ∀ k < n, f (lo + k) = true
  | 0, _, _, k, hk => absurd hk (Nat.not_lt_zero k)
  | n + 1, lo, h, k, hk => by
    rw [U35Pk.allR_succ, Bool.and_eq_true] at h
    rcases k with _ | k
    · exact h.1
    · have := allR_spec f n (lo + 1) h.2 k (by omega)
      rwa [Nat.add_right_comm, Nat.add_assoc] at this

theorem lenK_cons (x : ℕ) (L : List ℕ) : U35Pk.lenK (x :: L) = U35Pk.lenK L + 1 := rfl

theorem allL_get (f : ℕ → Bool) : ∀ (L : List ℕ), U35Pk.allL L f = true →
    ∀ i < U35Pk.lenK L, f (U35Pk.getK L i) = true
  | [], _, i, hi => absurd hi (Nat.not_lt_zero i)
  | x :: L, h, i, hi => by
    change bAnd(f x, U35Pk.allL L f) = true at h
    rw [U35Pk.bAnd_eq, Bool.and_eq_true] at h
    rcases i with _ | i
    · exact h.1
    · exact allL_get f L h.2 i (by rw [lenK_cons] at hi; omega)

theorem anyL_get (f : ℕ → Bool) : ∀ (L : List ℕ), U35Pk.anyL L f = true →
    ∃ i < U35Pk.lenK L, f (U35Pk.getK L i) = true
  | [], h => absurd h Bool.false_ne_true
  | x :: L, h => by
    change bIf(f x, true, U35Pk.anyL L f) = true at h
    cases hx : f x
    · rw [hx] at h
      obtain ⟨i, hi, h'⟩ := anyL_get f L h
      exact ⟨i + 1, by rw [lenK_cons]; omega, h'⟩
    · exact ⟨0, by rw [lenK_cons]; omega, hx⟩

theorem anyL_of_get (f : ℕ → Bool) : ∀ (L : List ℕ) (i : ℕ), i < U35Pk.lenK L →
    f (U35Pk.getK L i) = true → U35Pk.anyL L f = true
  | [], i, hi, _ => absurd hi (Nat.not_lt_zero i)
  | x :: L, i, hi, h => by
    change bIf(f x, true, U35Pk.anyL L f) = true
    rcases i with _ | i
    · change f x = true at h
      rw [h]
    · cases f x
      · exact anyL_of_get f L i (by rw [lenK_cons] at hi; omega) h
      · rfl

@[expose] def sl (k a : ℕ) (m : ℕ) : ℕ := if m = k then a else 0

theorem ev_sl : ∀ {n k : ℕ} (a : ℕ), k < n → ev (sl k a) n = 2 ^ (18 * k) * a
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, 0, a, _ => by
    rw [ev_succ, ev_of_zero fun m => by simp [sl]]
    simp [sl]
  | n + 1, k + 1, a, h => by
    have e : (fun m => sl (k + 1) a (m + 1)) = sl k a := funext fun m => by simp [sl]
    rw [ev_succ, e, ev_sl a (by omega)]
    simp only [sl, if_neg (Nat.succ_ne_zero k).symm, Nat.zero_add]
    ring

@[expose] def pk (W V : ℕ → ℕ) : ℕ :=
  ev (fun m => W m % 2 ^ 18) 37 + 2 ^ 1024 * ev (fun m => V m % 2 ^ 18) 37

theorem ev_mod_lt (W : ℕ → ℕ) : ev (fun m => W m % 2 ^ 18) 37 < 2 ^ 1024 :=
  lt_trans (ev_lt fun m _ => Nat.mod_lt _ (by norm_num)) (by norm_num)

theorem lor_split_w {a c : ℕ} (b d w : ℕ) (ha : a < 2 ^ w) (hc : c < 2 ^ w) :
    (a + 2 ^ w * b) ||| (c + 2 ^ w * d) = (a ||| c) + 2 ^ w * (b ||| d) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or, Nat.add_comm a, Nat.add_comm c, Nat.add_comm (a ||| c),
    Nat.testBit_two_pow_mul_add _ ha, Nat.testBit_two_pow_mul_add _ hc,
    Nat.testBit_two_pow_mul_add _ (Nat.or_lt_two_pow ha hc)]
  split_ifs <;> simp

theorem ev_lor : ∀ {n : ℕ} {W M : ℕ → ℕ}, (∀ m < n, W m < 2 ^ 18) → (∀ m < n, M m < 2 ^ 18) →
    (ev W n ||| ev M n) = ev (fun m => W m ||| M m) n
  | 0, _, _, _, _ => by simp [ev]
  | n + 1, W, M, hW, hM => by
    rw [ev_succ, ev_succ, ev_succ, lor_split_w _ _ _ (hW 0 (by omega)) (hM 0 (by omega)),
      ev_lor (fun m hm => hW (m + 1) (by omega)) (fun m hm => hM (m + 1) (by omega))]

theorem pk_lor (W V W' V' : ℕ → ℕ) :
    Nat.lor (pk W V) (pk W' V') = pk (fun m => W m ||| W' m) (fun m => V m ||| V' m) := by
  change pk W V ||| pk W' V' = _
  unfold pk
  have hb : ∀ (U : ℕ → ℕ), ∀ m < 37, U m % 2 ^ 18 < 2 ^ 18 := fun U m _ => Nat.mod_lt _ (by norm_num)
  rw [lor_split _ _ (ev_mod_lt W) (ev_mod_lt W'), ev_lor (hb W) (hb W'), ev_lor (hb V) (hb V')]
  simp only [← Nat.or_mod_two_pow]

theorem pk_congr {W V W' V' : ℕ → ℕ} (h1 : ∀ m < 37, W m % 2 ^ 18 = W' m % 2 ^ 18)
    (h2 : ∀ m < 37, V m % 2 ^ 18 = V' m % 2 ^ 18) : pk W V = pk W' V' := by
  unfold pk
  rw [ev_congr (W := fun m => W m % 2 ^ 18) (V := fun m => W' m % 2 ^ 18) h1,
    ev_congr (W := fun m => V m % 2 ^ 18) (V := fun m => V' m % 2 ^ 18) h2]

theorem pk_sl {k a b : ℕ} (hk : k < 37) (ha : a < 2 ^ 18) (hb : b < 2 ^ 18) :
    pk (sl k a) (sl k b) = 2 ^ (18 * k) * a + 2 ^ 1024 * (2 ^ (18 * k) * b) := by
  unfold pk
  have e : ∀ c, c < 2 ^ 18 → (fun m => sl k c m % 2 ^ 18) = sl k c := fun c hc => funext fun m => by
    unfold sl
    split_ifs
    · exact Nat.mod_eq_of_lt hc
    · rfl
  rw [e a ha, e b hb, ev_sl a hk, ev_sl b hk]

theorem E_eq : U35Pk.E = 255 + 2 ^ 1024 * 255 := by decide +kernel

theorem lane_get {n s : ℕ} {W : ℕ → ℕ} (hW : ∀ m < n, W m < 2 ^ 8) (hs : s < n) :
    ev W n / 2 ^ (18 * s) % 2 ^ 8 = W s := by
  rw [ev_div (fun m hm => lt_trans (hW m hm) (by norm_num)) hs.le]
  obtain ⟨k, hk⟩ : ∃ k, n - s = k + 1 := ⟨n - s - 1, by omega⟩
  have e : ∀ x E : ℕ, (x + 2 ^ 18 * E) % 2 ^ 8 = x % 2 ^ 8 := fun x E => by
    have : 2 ^ 18 * E = 2 ^ 8 * (2 ^ 10 * E) := by ring
    rw [this, Nat.add_mul_mod_self_left]
  rw [hk, ev_succ, e, Nat.zero_add]
  exact Nat.mod_eq_of_lt (hW s hs)

theorem lo_window {lo : ℕ} (hi : ℕ) (hlo : lo < 2 ^ 1024) {p : ℕ} (h : p + 8 ≤ 1024) :
    (lo + 2 ^ 1024 * hi) / 2 ^ p % 2 ^ 8 = lo / 2 ^ p % 2 ^ 8 := by
  apply Nat.eq_of_testBit_eq
  intro b
  rw [testBit_div_mod, testBit_div_mod, testBit_split _ hlo]
  by_cases hb : b < 8
  · have : b + p < 1024 := by omega
    simp [hb, this]
  · simp [hb]

theorem hi_div {lo : ℕ} (hi : ℕ) (hlo : lo < 2 ^ 1024) (p : ℕ) :
    (lo + 2 ^ 1024 * hi) / 2 ^ p / 2 ^ 1024 = hi / 2 ^ p := by
  rw [Nat.div_div_eq_div_mul _ (2 ^ p) (2 ^ 1024), Nat.mul_comm (2 ^ p) (2 ^ 1024),
    ← Nat.div_div_eq_div_mul, split_div hlo]

theorem ev_lt1024 {n : ℕ} {W : ℕ → ℕ} (hW : ∀ m < n, W m < 2 ^ 8) (hn : n ≤ 37) :
    ev W n < 2 ^ 1024 :=
  lt_of_lt_of_le (ev_lt fun m hm => lt_trans (hW m hm) (by norm_num))
    (Nat.pow_le_pow_right (by norm_num) (by omega))

theorem mv_ev {n s k : ℕ} {W V : ℕ → ℕ} (hW : ∀ m < n, W m < 2 ^ 8) (hV : ∀ m < n, V m < 2 ^ 8)
    (hn : n ≤ 37) (hs : s < n) (hk : k < 37) :
    U35Pk.mv (ev W n + 2 ^ 1024 * ev V n) (18 * s) (18 * k) = pk (sl k (W s)) (sl k (V s)) := by
  have hlo := ev_lt1024 hW hn
  have hm : ∀ c p q : ℕ, U35Pk.mv c p q = ((c / 2 ^ p) &&& (255 + 2 ^ 1024 * 255)) * 2 ^ q :=
    fun c p q => by
      unfold U35Pk.mv
      rw [E_eq]
      change ((c >>> p) &&& _) <<< q = _
      rw [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  rw [hm, land_split _ _ _ _ (by norm_num : 255 < 2 ^ 1024)]
  have e255 : (255 : ℕ) = 2 ^ 8 - 1 := by norm_num
  rw [e255, Nat.and_two_pow_sub_one_eq_mod, Nat.and_two_pow_sub_one_eq_mod,
    Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by norm_num : 8 ≤ 1024)), lo_window _ hlo (by omega),
    hi_div _ hlo, lane_get hW hs, lane_get hV hs,
    pk_sl hk (lt_trans (hW s hs) (by norm_num)) (lt_trans (hV s hs) (by norm_num))]
  ring

theorem lanesB_lt8 (F : Fin 3 → Fin 3 → ℕ) (hF : ∀ r j, F r j < 5) : ∀ m < 9, lanesB F m < 2 ^ 8 :=
  fun m _ => lt_trans (lanesB_lt hF (by norm_num) m) (by norm_num)

theorem lanesA_lt8 (F : Fin 3 → Fin 3 → ℕ) (hF : ∀ r j, F r j < 5) : ∀ m < 37, lanesA F m < 2 ^ 8 :=
  fun m _ => lt_of_le_of_lt (lanesA_le hF m) (by norm_num)

theorem mv_encB (X : Matrix (Fin 3) (Fin 3) F25) {p q : ℕ} (hp : p % 18 = 0) (hp' : p / 18 < 9)
    (hq : q % 18 = 0) (hq' : q / 18 < 37) :
    U35Pk.mv (encB X) p q = pk (sl (q / 18) (lanesB (fun r j => re (X r j)) (p / 18)))
      (sl (q / 18) (lanesB (fun r j => im (X r j)) (p / 18))) := by
  have h := mv_ev (n := 9) (s := p / 18) (k := q / 18) (lanesB_lt8 _ fun r j => re_lt (X r j))
    (lanesB_lt8 _ fun r j => im_lt (X r j)) (by norm_num) hp' hq'
  rw [Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hp),
    Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hq)] at h
  exact h

theorem encA_pk (X : Matrix (Fin 3) (Fin 3) F25) :
    encA X = pk (lanesA fun r j => re (X r j)) (lanesA fun r j => im (X r j)) := by
  unfold encA packA pk
  have hm : ∀ F : Fin 3 → Fin 3 → ℕ, (∀ r j, F r j < 5) →
      ev (lanesA F) 37 = ev (fun m => lanesA F m % 2 ^ 18) 37 := fun F hF =>
    ev_congr fun m hm => (Nat.mod_eq_of_lt (lt_trans (lanesA_lt8 F hF m hm) (by norm_num))).symm
  rw [hm _ fun r j => re_lt (X r j), hm _ fun r j => im_lt (X r j)]

theorem bToA_enc (X : Matrix (Fin 3) (Fin 3) F25) : U35Pk.bToA (encB X) = encA X := by
  unfold U35Pk.bToA
  simp (disch := norm_num) only [mv_encB X, pk_lor]
  rw [encA_pk]
  apply pk_congr <;> intro m hm <;> interval_cases m <;> simp [sl, lanesA, lanesB]

theorem lane_lo (X : Matrix (Fin 3) (Fin 3) F25) {s : ℕ} (hs : s < 9) :
    encB X / 2 ^ (18 * s) % 2 ^ 8 = lanesB (fun r j => re (X r j)) s := by
  unfold encB packB
  rw [lo_window _ (ev_lt1024 (lanesB_lt8 _ fun r j => re_lt (X r j)) (by norm_num)) (by omega),
    lane_get (lanesB_lt8 _ fun r j => re_lt (X r j)) hs]

theorem lane_hi (X : Matrix (Fin 3) (Fin 3) F25) {s : ℕ} (hs : s < 9) :
    encB X / 2 ^ (1024 + 18 * s) % 2 ^ 8 = lanesB (fun r j => im (X r j)) s := by
  unfold encB packB
  rw [Nat.pow_add, ← Nat.div_div_eq_div_mul,
    split_div (ev_lt1024 (lanesB_lt8 _ fun r j => re_lt (X r j)) (by norm_num)),
    lane_get (lanesB_lt8 _ fun r j => im_lt (X r j)) hs]

theorem blk_lane {x M p : ℕ} (hM : M &&& 2 ^ p * (2 ^ 8 - 1) = 2 ^ p * (2 ^ 8 - 1)) (h : x &&& M = 0) :
    x / 2 ^ p % 2 ^ 8 = 0 := by
  have := land_shift_mask x p 8
  rw [← hM, ← Nat.and_assoc, h, Nat.zero_and] at this
  exact (Nat.mul_eq_zero.1 this.symm).resolve_left (by positivity)

theorem blk_masks : ∀ s ∈ [8, 5, 0, 1],
    U35Pk.BLKd &&& 2 ^ (18 * s) * (2 ^ 8 - 1) = 2 ^ (18 * s) * (2 ^ 8 - 1) ∧
    U35Pk.BLKd &&& 2 ^ (1024 + 18 * s) * (2 ^ 8 - 1) = 2 ^ (1024 + 18 * s) * (2 ^ 8 - 1) := by
  decide +kernel

theorem zero_of_lanes {x : F25} (h1 : re x = 0) (h2 : im x = 0) : x = 0 := ext_re_im h1 h2

theorem isBlk_enc {X : Matrix (Fin 3) (Fin 3) F25} (h : U35Pk.isBlk (encB X) = true) :
    X 0 2 = 0 ∧ X 1 2 = 0 ∧ X 2 0 = 0 ∧ X 2 1 = 0 := by
  have h0 : encB X &&& U35Pk.BLKd = 0 := Nat.eq_of_beq_eq_true h
  have hl : ∀ s ∈ [8, 5, 0, 1], lanesB (fun r j => re (X r j)) s = 0 ∧
      lanesB (fun r j => im (X r j)) s = 0 := fun s hs => by
    have hs9 : s < 9 := by simp at hs; omega
    obtain ⟨m1, m2⟩ := blk_masks s hs
    exact ⟨(lane_lo X hs9).symm.trans (blk_lane m1 h0), (lane_hi X hs9).symm.trans (blk_lane m2 h0)⟩
  obtain ⟨a1, a2⟩ := hl 8 (by simp)
  obtain ⟨b1, b2⟩ := hl 5 (by simp)
  obtain ⟨c1, c2⟩ := hl 0 (by simp)
  obtain ⟨d1, d2⟩ := hl 1 (by simp)
  exact ⟨zero_of_lanes a1 a2, zero_of_lanes b1 b2, zero_of_lanes c1 c2, zero_of_lanes d1 d2⟩

theorem blk_split : U35Pk.BLKd = 2 ^ (18 * 8) * (2 ^ 8 - 1) ||| 2 ^ (18 * 5) * (2 ^ 8 - 1) |||
    2 ^ (18 * 0) * (2 ^ 8 - 1) ||| 2 ^ (18 * 1) * (2 ^ 8 - 1) ||| 2 ^ (1024 + 18 * 8) * (2 ^ 8 - 1) |||
    2 ^ (1024 + 18 * 5) * (2 ^ 8 - 1) ||| 2 ^ (1024 + 18 * 0) * (2 ^ 8 - 1) |||
    2 ^ (1024 + 18 * 1) * (2 ^ 8 - 1) := by
  decide +kernel

theorem blk_of {X : Matrix (Fin 3) (Fin 3) F25} (h : X 0 2 = 0 ∧ X 1 2 = 0 ∧ X 2 0 = 0 ∧ X 2 1 = 0) :
    U35Pk.isBlk (encB X) = true := by
  have zl : ∀ s < 9, lanesB (fun r j => re (X r j)) s = 0 →
      encB X &&& 2 ^ (18 * s) * (2 ^ 8 - 1) = 0 := fun s hs h0 => by
    rw [land_shift_mask, lane_lo X hs, h0, Nat.mul_zero]
  have zh : ∀ s < 9, lanesB (fun r j => im (X r j)) s = 0 →
      encB X &&& 2 ^ (1024 + 18 * s) * (2 ^ 8 - 1) = 0 := fun s hs h0 => by
    rw [land_shift_mask, lane_hi X hs, h0, Nat.mul_zero]
  obtain ⟨h1, h2, h3, h4⟩ := h
  unfold U35Pk.isBlk
  rw [Nat.beq_eq, blk_split]
  change encB X &&& _ = 0
  rw [Nat.and_or_distrib_left, Nat.and_or_distrib_left, Nat.and_or_distrib_left,
    Nat.and_or_distrib_left, Nat.and_or_distrib_left, Nat.and_or_distrib_left,
    Nat.and_or_distrib_left]
  have r0 : re (0 : F25) = 0 := rfl
  have i0 : im (0 : F25) = 0 := rfl
  rw [zl 8 (by norm_num) (by simp only [lanesB, List.getD_cons_succ, List.getD_cons_zero, h1, r0]),
    zl 5 (by norm_num) (by simp only [lanesB, List.getD_cons_succ, List.getD_cons_zero, h2, r0]),
    zl 0 (by norm_num) (by simp only [lanesB, List.getD_cons_succ, List.getD_cons_zero, h3, r0]),
    zl 1 (by norm_num) (by simp only [lanesB, List.getD_cons_succ, List.getD_cons_zero, h4, r0]),
    zh 8 (by norm_num) (by simp only [lanesB, List.getD_cons_succ, List.getD_cons_zero, h1, i0]),
    zh 5 (by norm_num) (by simp only [lanesB, List.getD_cons_succ, List.getD_cons_zero, h2, i0]),
    zh 0 (by norm_num) (by simp only [lanesB, List.getD_cons_succ, List.getD_cons_zero, h3, i0]),
    zh 1 (by norm_num) (by simp only [lanesB, List.getD_cons_succ, List.getD_cons_zero, h4, i0])]
  simp

end CFSG.Certificates.U35Pk
