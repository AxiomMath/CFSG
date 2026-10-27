module

public import CFSG.Certificates.Kernel.LceSP.Base
import Mathlib.Tactic.Group
public import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.Certificates.LceP

open CFSG.KC CFSG.KC.LceS CFSG.KC.Loop

theorem land_lit (x k m : ℕ) (hm : m = 2 ^ k - 1) : Nat.land x m = x % 2 ^ k := by
  subst hm
  exact Nat.and_two_pow_sub_one_eq_mod x k

theorem land8 (x : ℕ) : Nat.land x 255 = x % 256 := land_lit x 8 255 (by norm_num)
theorem land20 (x : ℕ) : Nat.land x 1048575 = x % 1048576 := land_lit x 20 1048575 (by norm_num)
theorem land28 (x : ℕ) : Nat.land x 268435455 = x % 268435456 :=
  land_lit x 28 268435455 (by norm_num)
theorem land32 (x : ℕ) : Nat.land x 4294967295 = x % 4294967296 :=
  land_lit x 32 4294967295 (by norm_num)
theorem shr20 (x : ℕ) : Nat.shiftRight x 20 = x / 1048576 := shr_eq x 20
theorem shr28 (x : ℕ) : Nat.shiftRight x 28 = x / 268435456 := shr_eq x 28
theorem shr48 (x : ℕ) : Nat.shiftRight x 48 = x / 281474976710656 := shr_eq x 48
theorem lor20 {a : ℕ} (b : ℕ) (ha : a < 1048576) :
    Nat.lor a (Nat.shiftLeft b 20) = a + b * 1048576 := lor_shl (k := 20) ha
theorem lor32 {a : ℕ} (b : ℕ) (ha : a < 4294967296) :
    Nat.lor a (Nat.shiftLeft b 32) = a + b * 4294967296 := lor_shl (k := 32) ha

theorem fx_eq (R : ℕ) : fx R = R % 1048576 := land20 R
theorem fc_eq (R : ℕ) : fc R = R / 1048576 % 256 := by
  unfold fc
  rw [land8, shr20]
theorem fy_eq (R : ℕ) : fy R = R / 268435456 % 1048576 := by
  unfold fy
  rw [land20, shr28]
theorem fic_eq (R : ℕ) : fic R = R / 281474976710656 := shr48 R
theorem fxc_eq (R : ℕ) : fxc R = fx R + 1048576 * fc R := by
  unfold fxc
  rw [land28, fx_eq, fc_eq]
  omega
theorem fyic_eq (R : ℕ) : fyic R = fy R + 1048576 * fic R := by
  unfold fyic
  rw [shr28, fy_eq, fic_eq]
  omega

theorem fx_lt (R : ℕ) : fx R < 1048576 := by rw [fx_eq]; omega
theorem fy_lt (R : ℕ) : fy R < 1048576 := by rw [fy_eq]; omega
theorem fc_lt (R : ℕ) : fc R < 256 := by rw [fc_eq]; omega

theorem fct_lt (blk : ℕ → ℕ) (h : ℕ) : fct blk h < 2 ^ 56 := by
  unfold fct
  rw [strictN_eq]
  unfold rget
  change _ &&& (2 ^ 56 - 1) < _
  rw [Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_lt _ (by positivity)

theorem fic_lt (blk : ℕ → ℕ) (h : ℕ) : fic (fct blk h) < 256 := by
  rw [fic_eq]
  have := fct_lt blk h
  rw [Nat.div_lt_iff_lt_mul (by norm_num)]
  norm_num at this ⊢
  omega

theorem recOK_spec {INV nC R : ℕ} (h : recOK INV nC R = true) :
    fx R < nC ∧ fy R < nC ∧ fic R = inv16 INV (fc R) := by
  unfold recOK at h
  simp only [andB_iff, Nat.blt_eq, Nat.beq_eq] at h
  exact h

theorem lv_fic {G : Type*} [Group G] (gen : ℕ → G) {INV INV8 L nC : ℕ} (blk : ℕ → ℕ) {h : ℕ}
    (hinv : invOK INV INV8 L = true) (hR : recOK INV nC (fct blk h) = true) :
    lv gen (fic (fct blk h)) = (lv gen (fc (fct blk h)))⁻¹ ∧
      (fc (fct blk h) < L ∨ fc (fct blk h) = 255) ∧
      (fc (fct blk h) < L → fic (fct blk h) = fc (fct blk h) ^^^ 1) ∧
      (fc (fct blk h) = 255 → fic (fct blk h) = 255) := by
  obtain ⟨-, -, hfic⟩ := recOK_spec hR
  obtain ⟨hL, -, hc⟩ := invOK_spec hinv
  obtain ⟨h1, h2, h3⟩ := hc _ (fc_lt _)
  have hlt := fic_lt blk h
  rcases Nat.lt_or_ge (fc (fct blk h)) L with hcL | hcL
  · have e := (h1 hcL).1
    rw [e] at hfic
    refine ⟨?_, Or.inl hcL, fun _ => hfic, fun h255 => by omega⟩
    rw [hfic, lv_xor_one gen (by omega)]
  · by_cases h255 : fc (fct blk h) = 255
    · rw [h2 hcL h255] at hfic
      refine ⟨?_, Or.inr h255, fun h => by omega, fun _ => hfic⟩
      rw [hfic, h255, lv_255, inv_one]
    · rw [h3 hcL h255] at hfic
      omega

theorem sF_eq (R st : ℕ) : sF R st =
    if st % 268435456 = fxc R then fy R + st / 268435456 * 1048576 else 0 := by
  unfold sF
  simp only [brec_eq, Nat.beq_eq, land28, shr28, lor20 _ (fy_lt R)]

theorem sB_eq (R st : ℕ) : sB R st =
    if st % 268435456 = fyic R then fx R + st / 268435456 * 1048576 else 0 := by
  unfold sB
  simp only [brec_eq, Nat.beq_eq, land28, shr28, lor20 _ (fx_lt R)]

section Walk

variable {G : Type*} [Group G] (gen : ℕ → G) (H : Subgroup G)

@[expose] noncomputable def el (rep : ℕ → G) (R : ℕ) : G :=
  rep (fx R) * lv gen (fc R) * (rep (fy R))⁻¹

@[expose] def WI (rep : ℕ → G) (s W ft : ℕ) (a : G) (p st : ℕ) : Prop :=
  st / 1048576 = 0 ∨ ∃ cur < 1048576, st = cur + 1048576 * (W / 256 ^ p) ∧
    (rep s * bv gen W p * (rep cur)⁻¹ ∈ H ↔ (p ≤ ft ∨ a ∈ H))

theorem WI_zero (rep : ℕ → G) (s W ft : ℕ) (a : G) (p : ℕ) : WI gen H rep s W ft a p 0 :=
  Or.inl rfl

theorem WI_move {rep : ℕ → G} {s W ft : ℕ} {a : G} {p cur cur' : ℕ}
    (hX : rep s * bv gen W p * (rep cur)⁻¹ ∈ H ↔ (p ≤ ft ∨ a ∈ H))
    (hb : (p ≠ ft ∧ rep cur * lv gen (wLet W p) * (rep cur')⁻¹ ∈ H) ∨
      (p = ft ∧ rep cur * lv gen (wLet W p) * (rep cur')⁻¹ = a)) :
    rep s * bv gen W (p + 1) * (rep cur')⁻¹ ∈ H ↔ (p + 1 ≤ ft ∨ a ∈ H) := by
  have e : rep s * bv gen W (p + 1) * (rep cur')⁻¹ =
      (rep s * bv gen W p * (rep cur)⁻¹) * (rep cur * lv gen (wLet W p) * (rep cur')⁻¹) := by
    rw [bv_succ]
    group
  rw [e]
  rcases hb with ⟨hp, hb⟩ | ⟨hp, hb⟩
  · rw [H.mul_mem_cancel_right hb, hX]
    constructor
    · rintro (h | h)
      · exact Or.inl (by omega)
      · exact Or.inr h
    · rintro (h | h)
      · exact Or.inl (by omega)
      · exact Or.inr h
  · have hX' : rep s * bv gen W p * (rep cur)⁻¹ ∈ H := hX.2 (Or.inl (le_of_eq hp))
    rw [hb, H.mul_mem_cancel_left hX']
    constructor
    · intro h
      exact Or.inr h
    · rintro (h | h)
      · omega
      · exact h

theorem div256_succ (W p : ℕ) : W / 256 ^ p / 256 = W / 256 ^ (p + 1) := by
  rw [Nat.div_div_eq_div_mul, pow_succ]

theorem WI_sF {rep : ℕ → G} {s W ft : ℕ} {a : G} {p st R : ℕ} (hI : WI gen H rep s W ft a p st)
    (hb : (p ≠ ft ∧ el gen rep R ∈ H) ∨ (p = ft ∧ el gen rep R = a)) :
    WI gen H rep s W ft a (p + 1) (sF R st) := by
  rw [sF_eq]
  split_ifs with hm
  · rcases hI with hd | ⟨cur, hcur, hst, hX⟩
    · left
      have := fy_lt R
      omega
    · right
      rw [fxc_eq] at hm
      have hfx := fx_lt R
      have hfc := fc_lt R
      have h1 : cur = fx R := by omega
      have h2 : W / 256 ^ p % 256 = fc R := by omega
      have h3 : st / 268435456 = W / 256 ^ (p + 1) := by
        rw [← div256_succ]
        omega
      refine ⟨fy R, fy_lt R, by rw [h3]; ring, WI_move gen H hX ?_⟩
      rw [wLet_eq, h2, h1]
      exact hb
  · exact Or.inl rfl

theorem WI_sB {rep : ℕ → G} {s W ft : ℕ} {a : G} {p st R : ℕ} (hI : WI gen H rep s W ft a p st)
    (hp : p ≠ ft) (hR : el gen rep R ∈ H) (hl : lv gen (fic R) = (lv gen (fc R))⁻¹) :
    WI gen H rep s W ft a (p + 1) (sB R st) := by
  rw [sB_eq]
  split_ifs with hm
  · rcases hI with hd | ⟨cur, hcur, hst, hX⟩
    · left
      have := fx_lt R
      omega
    · right
      rw [fyic_eq] at hm
      have hfy := fy_lt R
      have h1 : cur = fy R := by omega
      have h2 : W / 256 ^ p % 256 = fic R := by omega
      have h3 : st / 268435456 = W / 256 ^ (p + 1) := by
        rw [← div256_succ]
        omega
      refine ⟨fx R, fx_lt R, by rw [h3]; ring, WI_move gen H hX (Or.inl ⟨hp, ?_⟩)⟩
      rw [wLet_eq, h2, h1, hl]
      have : rep (fy R) * (lv gen (fc R))⁻¹ * (rep (fx R))⁻¹ = (el gen rep R)⁻¹ := by
        unfold el
        group
      rw [this]
      exact H.inv_mem hR
  · exact Or.inl rfl

@[expose] def RefsOK (blk : ℕ → ℕ) (rep : ℕ → G) (i : ℕ) : Prop :=
  ∀ h < i, el gen rep (fct blk h) ∈ H ∧ lv gen (fic (fct blk h)) = (lv gen (fc (fct blk h)))⁻¹

theorem WI_ref {blk : ℕ → ℕ} {rep : ℕ → G} {s W ft : ℕ} {a : G} {p st i e : ℕ}
    (hI : WI gen H rep s W ft a p st) (hp : p ≠ ft) (hrefs : RefsOK gen H blk rep i) :
    WI gen H rep s W ft a (p + 1) (refStep blk i e st) := by
  unfold refStep
  rw [brec_eq]
  split_ifs with hh
  · rw [Nat.blt_eq] at hh
    simp only [strictN_eq]
    rw [brec_eq]
    obtain ⟨h1, h2⟩ := hrefs _ hh
    split_ifs
    · exact WI_sB gen H hI hp h1 h2
    · exact WI_sF gen H hI (Or.inl ⟨hp, h1⟩)
  · exact Or.inl rfl

theorem walkGo_spec {blk : ℕ → ℕ} {rep : ℕ → G} {s W ft : ℕ} {i Ri n : ℕ}
    (hrefs : RefsOK gen H blk rep i) :
    ∀ k ≤ n, ∀ J st, WI gen H rep s W ft (el gen rep Ri) (n - k) st →
      WI gen H rep s W ft (el gen rep Ri) n (walkGo blk i Ri ft n k J st)
  | 0, _, J, st, hI => by
    change WI gen H rep s W ft (el gen rep Ri) n st
    simpa using hI
  | k + 1, hk, J, st, hI => by
    change WI gen H rep s W ft (el gen rep Ri) n (Bool.rec (motive := fun _ => ℕ)
      (walkGo blk i Ri ft n k (Nat.shiftRight J 32) (refStep blk i (Nat.land J 4294967295) st))
      (walkGo blk i Ri ft n k J (sF Ri st)) (Nat.beq (Nat.sub n (Nat.succ k)) ft))
    have e : n - k = n - (k + 1) + 1 := by omega
    rw [brec_eq]
    split_ifs with hp
    · rw [Nat.beq_eq] at hp
      apply walkGo_spec hrefs k (by omega)
      rw [e]
      exact WI_sF gen H hI (Or.inr ⟨hp, rfl⟩)
    · rw [Nat.beq_eq] at hp
      apply walkGo_spec hrefs k (by omega)
      rw [e]
      exact WI_ref gen H hI hp hrefs

theorem walkOK_sound {blk : ℕ → ℕ} {rep : ℕ → G} {INV nC i R w fs ft J : ℕ}
    (h : walkOK blk INV nC i R w fs ft J = true) (hfs : fs < 1048576)
    (hrefs : RefsOK gen H blk rep i) (hrep0 : rep 0 = 1)
    (h2 : wKind w = 2 → bv gen (wWord w) (wLen w) = 1)
    (h3 : wKind w = 3 → bv gen (wWord w) (wLen w) ∈ H) :
    recOK INV nC R = true ∧ el gen rep R ∈ H := by
  unfold walkOK at h
  simp only [andB_iff, orB_iff, Nat.blt_eq, Nat.beq_eq, Nat.add_eq] at h
  obtain ⟨hrec, hft, hkind, hwalk⟩ := h
  refine ⟨hrec, ?_⟩
  have h0 : WI gen H rep fs (wWord w) ft (el gen rep R) (wLen w - wLen w)
      (wStart fs (wWord w)) := by
    rw [Nat.sub_self]
    right
    refine ⟨fs, hfs, ?_, ?_⟩
    · unfold wStart
      rw [lor20 _ hfs, pow_zero, Nat.div_one]
      ring
    · rw [bv_zero, mul_one, mul_inv_cancel]
      exact ⟨fun _ => Or.inl (Nat.zero_le _), fun _ => H.one_mem⟩
  have hn := walkGo_spec gen H (Ri := R) hrefs (wLen w) le_rfl (Nat.shiftRight J 53) _ h0
  rw [hwalk] at hn
  rcases hn with hd | ⟨cur, hcur, hst, hX⟩
  · omega
  · have hc : cur = fs := by omega
    rw [hc] at hX
    have hW : rep fs * bv gen (wWord w) (wLen w) * (rep fs)⁻¹ ∈ H := by
      rcases hkind with hk | ⟨hk, hfs0⟩
      · rw [h2 hk, mul_one, mul_inv_cancel]
        exact H.one_mem
      · rw [hfs0, hrep0, one_mul, inv_one, mul_one]
        exact h3 hk
    rcases hX.1 hW with h' | h'
    · omega
    · exact h'

end Walk

end CFSG.Certificates.LceP

end
