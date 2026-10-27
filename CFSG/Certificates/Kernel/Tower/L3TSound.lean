module

public import Certificates.Data.Kernel.Tower.Word
public import CFSG.Certificates.Kernel.Tower.L3Sound

public section

namespace Certificates.KernelTower

open CFSG.OddStandard.AltStdSmall4.Tower

variable {Y : Type*} [Group Y] {mul2 : Nat → Nat → Nat} {dec : Nat → Y}

theorem wevN_hom (M : IsModel (⊤ : Subgroup Y) 16384 mul2 dec) (β : Y →* Y) {G U : Nat}
    (hG : ∀ i < 4, l16 G i < 16384) (hU : ∀ i < 4, l16 U i < 16384)
    (hβ : ∀ i < 4, β (dec (l16 G i)) = dec (l16 U i)) :
    ∀ n w, wevN mul2 G n w < 16384 ∧ wevN mul2 U n w < 16384 ∧
      β (dec (wevN mul2 G n w)) = dec (wevN mul2 U n w) := by
  intro n
  induction n with
  | zero =>
    intro w
    have e : ∀ T, wevN mul2 T 0 w = 0 := fun _ => rfl
    rw [e, e, M.dec_zero, map_one]
    exact ⟨M.zero_lt, M.zero_lt, rfl⟩
  | succ n ih =>
    intro w
    have e : ∀ T, wevN mul2 T (n + 1) w = Bool.rec (motive := fun _ => Nat)
        (mul2 (l16 T (Nat.land (Nat.sub (Nat.land w 7) 1) 3)) (wevN mul2 T n (Nat.shiftRight w 3)))
        0 (Nat.beq (Nat.land w 7) 0) := fun _ => rfl
    rw [e, e]
    have hi : Nat.land (Nat.sub (Nat.land w 7) 1) 3 < 4 :=
      Nat.lt_succ_of_le (Nat.and_le_right : Nat.land (Nat.sub (Nat.land w 7) 1) 3 ≤ 3)
    obtain ⟨h1, h2, h3⟩ := ih (Nat.shiftRight w 3)
    cases Nat.beq (Nat.land w 7) 0 <;> dsimp only
    · refine ⟨M.mul_lt _ (hG _ hi) _ h1, M.mul_lt _ (hU _ hi) _ h2, ?_⟩
      rw [M.dec_mul _ (hG _ hi) _ h1, map_mul, hβ _ hi, h3, M.dec_mul _ (hU _ hi) _ h2]
    · rw [M.dec_zero, map_one]
      exact ⟨M.zero_lt, M.zero_lt, rfl⟩

theorem tgtOK_parts {GS IMW b G U W X H g2 : Nat} (h : tgtOK mul2 GS IMW b G U W X H g2 = true) :
    (∀ i < 4, l16 G i < 16384 ∧ l16 U i < 16384) ∧
      (∀ i < 4, wev mul2 G (l64 W i) = 2 * l16 GS i ∧
        wev mul2 U (l64 W i) = l16 IMW i ^^^ 2 * xbit X (2 * l16 GS i)) ∧
      wev mul2 G (l64 W 4) = 1 ∧ wev mul2 U (l64 W 4) = b ^^^ 2 * xbit X 1 ∧
      H < 16384 ∧ g2 < 16384 ∧ mul2 H g2 = 0 := by
  simp only [tgtOK, Bool.and_eq_true, allB_eq_true, Nat.blt_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  exact ⟨h1, fun i hi => ⟨Nat.eq_of_beq_eq_true (h2 i hi).1, Nat.eq_of_beq_eq_true (h2 i hi).2⟩,
    Nat.eq_of_beq_eq_true h3, Nat.eq_of_beq_eq_true h4, h5, h6, Nat.eq_of_beq_eq_true h7⟩

theorem pow_xor_mul {z : Y} (hz2 : z * z = 1) {p q : Nat} (hp : p ≤ 1) (hq : q ≤ 1) :
    z ^ (p ^^^ q) = z ^ p * z ^ q := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hp with rfl | rfl <;>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hq with rfl | rfl
  · simp
  · simp
  · simp
  · have e : (1 : Nat) ^^^ 1 = 0 := rfl
    rw [e, pow_zero, pow_one, hz2]

theorem pow_mul_self {z : Y} (hz2 : z * z = 1) {p : Nat} (hp : p ≤ 1) : z ^ p * z ^ p = 1 := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hp with rfl | rfl
  · simp
  · rw [pow_one, hz2]

@[expose] noncomputable def tgtBeta0 (M : IsModel (⊤ : Subgroup Y) 16384 mul2 dec) (X : Nat)
    (hz2 : dec 2 * dec 2 = 1) (hzc : ∀ y : Y, dec 2 * y = y * dec 2)
    (hX : ∀ a < 16384, ∀ b < 16384, xbit X (mul2 a b) = xbit X a ^^^ xbit X b) (β : Y →* Y) :
    Y →* Y where
  toFun x := dec 2 ^ xbit X (M.code x) * β x
  map_one' := by
    have h00 : mul2 0 0 = 0 := M.inj _ (M.mul_lt _ M.zero_lt _ M.zero_lt) _ M.zero_lt
      (by rw [M.dec_mul _ M.zero_lt _ M.zero_lt, M.dec_zero, mul_one])
    have hx0 := hX 0 M.zero_lt 0 M.zero_lt
    rw [h00, Nat.xor_self] at hx0
    rw [M.code_one, hx0, pow_zero, one_mul, map_one]
  map_mul' x y := by
    have hx := M.code_lt (Subgroup.mem_top x)
    have hy := M.code_lt (Subgroup.mem_top y)
    rw [M.code_mul (Subgroup.mem_top x) (Subgroup.mem_top y), hX _ hx _ hy,
      pow_xor_mul hz2 (xbit_le _ _) (xbit_le _ _), map_mul]
    have hc : β x * dec 2 ^ xbit X (M.code y) = dec 2 ^ xbit X (M.code y) * β x :=
      ((Commute.pow_left (hzc (β x)) _).eq).symm
    simp only [mul_assoc]
    congr 1
    rw [← mul_assoc, ← mul_assoc, hc]

theorem tgtBeta0_apply (M : IsModel (⊤ : Subgroup Y) 16384 mul2 dec) (X : Nat)
    (hz2 : dec 2 * dec 2 = 1) (hzc : ∀ y : Y, dec 2 * y = y * dec 2)
    (hX : ∀ a < 16384, ∀ b < 16384, xbit X (mul2 a b) = xbit X a ^^^ xbit X b) (β : Y →* Y)
    {k : Nat} (hk : k < 16384) :
    tgtBeta0 M X hz2 hzc hX β (dec k) = dec 2 ^ xbit X k * β (dec k) := by
  have e : tgtBeta0 M X hz2 hzc hX β (dec k) = dec 2 ^ xbit X (M.code (dec k)) * β (dec k) := rfl
  rw [e, M.code_dec hk]

theorem pow_dec_xor (M : IsModel (⊤ : Subgroup Y) 16384 mul2 dec)
    (hz : ∀ k < 16384, mul2 2 k = k ^^^ 2) {c x : Nat} (hc : c < 16384) (hx : x ≤ 1) :
    dec 2 ^ x * dec (c ^^^ 2 * x) = dec c := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hx with rfl | rfl
  · rw [pow_zero, one_mul, Nat.mul_zero, Nat.xor_zero]
  · have hlt : c ^^^ 2 < 16384 := Nat.xor_lt_two_pow (n := 14) hc (by omega)
    rw [pow_one, Nat.mul_one, ← M.dec_mul 2 (by omega) _ hlt, hz _ hlt, Nat.xor_assoc,
      Nat.xor_self, Nat.xor_zero]

theorem tgt_beta0 (M : IsModel (⊤ : Subgroup Y) 16384 mul2 dec)
    (hz : ∀ k < 16384, mul2 2 k = k ^^^ 2) (hzc : ∀ y : Y, dec 2 * y = y * dec 2)
    {X : Nat} (hX : ∀ a < 16384, ∀ b < 16384, xbit X (mul2 a b) = xbit X a ^^^ xbit X b)
    {GS IMW b G U W H g2 : Nat} (hC : tgtOK mul2 GS IMW b G U W X H g2 = true)
    (hIM : ∀ i < 4, l16 IMW i < 16384) (hb : b < 16384) (β : Y →* Y)
    (hβ : ∀ i < 4, β (dec (l16 G i)) = dec (l16 U i)) (hz2 : dec 2 * dec 2 = 1) :
    (∀ i < 4, tgtBeta0 M X hz2 hzc hX β (dec (2 * l16 GS i)) = dec (l16 IMW i)) ∧
      tgtBeta0 M X hz2 hzc hX β (dec 1) = dec b := by
  obtain ⟨hGU, hW, hW1, hU1, -⟩ := tgtOK_parts hC
  have hw := wevN_hom M β (fun i hi => (hGU i hi).1) (fun i hi => (hGU i hi).2) hβ 21
  refine ⟨fun i hi => ?_, ?_⟩
  · obtain ⟨hG, -, he⟩ := hw (l64 W i)
    have e1 : wevN mul2 G 21 (l64 W i) = 2 * l16 GS i := (hW i hi).1
    have e2 : wevN mul2 U 21 (l64 W i) = l16 IMW i ^^^ 2 * xbit X (2 * l16 GS i) := (hW i hi).2
    rw [e1] at hG he
    rw [e2] at he
    rw [tgtBeta0_apply M X hz2 hzc hX β hG, he, pow_dec_xor M hz (hIM i hi) (xbit_le _ _)]
  · obtain ⟨-, -, he⟩ := hw (l64 W 4)
    have e1 : wevN mul2 G 21 (l64 W 4) = 1 := hW1
    have e2 : wevN mul2 U 21 (l64 W 4) = b ^^^ 2 * xbit X 1 := hU1
    rw [e1, e2] at he
    rw [tgtBeta0_apply M X hz2 hzc hX β (by omega), he, pow_dec_xor M hz hb (xbit_le _ _)]

theorem tgt_sound (M : IsModel (⊤ : Subgroup Y) 16384 mul2 dec)
    (hz : ∀ k < 16384, mul2 2 k = k ^^^ 2) (hzc : ∀ y : Y, dec 2 * y = y * dec 2)
    {X : Nat} (hX : ∀ a < 16384, ∀ b < 16384, xbit X (mul2 a b) = xbit X a ^^^ xbit X b)
    {GS IMW b G U W H g2 S : Nat} (hC : tgtOK mul2 GS IMW b G U W X H g2 = true)
    (hIM : ∀ i < 4, l16 IMW i < 16384) (hb : b < 16384)
    (hfam : ∀ β₀ : Y →* Y, (∀ i < 4, β₀ (dec (2 * l16 GS i)) = dec (l16 IMW i)) →
      β₀ (dec 1) = dec b → ∀ k < 16384,
        (bitS S k = true ↔ dec 2 ^ xbit X k * (dec k * β₀ (dec k)) = dec H))
    (β : Y →* Y) (hβ : ∀ i < 4, β (dec (l16 G i)) = dec (l16 U i)) :
    ∀ k < 16384, (bitS S k = true ↔ dec k * β (dec k) * dec g2 = 1) := by
  obtain ⟨-, -, -, -, hH, hg2, hHg⟩ := tgtOK_parts hC
  have hz2 : dec 2 * dec 2 = 1 := by
    rw [← M.dec_mul 2 (by omega) 2 (by omega), hz 2 (by omega)]
    exact M.dec_zero
  obtain ⟨h1, h2⟩ := tgt_beta0 M hz hzc hX hC hIM hb β hβ hz2
  intro k hk
  rw [hfam _ h1 h2 k hk, tgtBeta0_apply M X hz2 hzc hX β hk]
  have hc : dec k * (dec 2 ^ xbit X k * β (dec k)) = dec 2 ^ xbit X k * (dec k * β (dec k)) := by
    have hzk : dec k * dec 2 ^ xbit X k = dec 2 ^ xbit X k * dec k :=
      ((Commute.pow_left (hzc (dec k)) _).eq).symm
    rw [← mul_assoc, ← mul_assoc, hzk]
  have hinv : dec g2 = (dec H)⁻¹ := by
    have e := M.dec_mul _ hH _ hg2
    rw [hHg, M.dec_zero] at e
    exact (inv_eq_of_mul_eq_one_right e.symm).symm
  rw [hc, ← mul_assoc (dec 2 ^ xbit X k) (dec 2 ^ xbit X k), pow_mul_self hz2 (xbit_le _ _),
    one_mul, hinv, mul_inv_eq_one]

end Certificates.KernelTower
