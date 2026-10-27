module

public import CFSG.Certificates.Kernel.DceTwCore
public import CFSG.Certificates.Kernel.Th.Spec.DceLce
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.KC.Th.Spec.Dce

open CFSG.KC.Th CFSG.KC.Th.DceS CFSG.KC.Loop CFSG.Certificates.DceLoop
  CFSG.Certificates.DceWord CFSG.Certificates.DceTw CFSG.Certificates.LCE

set_option exponentiation.threshold 700

@[expose] noncomputable def xl {G : Type*} [Group G] (xg : ℕ → G) (LC c : ℕ) : G :=
  letV xg (byte LC c)

theorem xor1_facts : ∀ k < 254, (Nat.xor k 1) % 2 ≠ k % 2 ∧ (Nat.xor k 1) / 2 = k / 2 ∧
    Nat.xor k 1 ≠ 255 ∧ k ≠ 255 := by decide +kernel

theorem letV_xor1 {G : Type*} [Group G] (y : ℕ → G) {k : ℕ} (hk : k < 254) :
    letV y (Nat.xor k 1) = (letV y k)⁻¹ := by
  obtain ⟨h1, h2, h3, h4⟩ := xor1_facts k hk
  unfold letV
  rw [if_neg h3, if_neg h4, h2]
  by_cases hp : k % 2 = 0
  · have : ¬ (Nat.xor k 1) % 2 = 0 := by omega
    rw [if_neg this, if_pos hp]
  · have : (Nat.xor k 1) % 2 = 0 := by omega
    rw [if_pos this, if_neg hp, inv_inv]

theorem xl_u {G : Type*} [Group G] (xg : ℕ → G) {LT LC LI TL VL NL : ℕ}
    (hL : LetOK LT LC LI TL VL NL) :
    xl xg LC TL = xg 7 ∧ xl xg LC VL = (xg 7)⁻¹ := by
  have h1 : byte LC TL = 14 := hL.tc
  have h2 : byte LC VL = 15 := hL.vc
  unfold xl
  rw [h1, h2]
  refine ⟨?_, ?_⟩
  · unfold letV
    simp
  · unfold letV
    simp

theorem xl_inv {G : Type*} [Group G] (xg : ℕ → G) {LT LC LI TL VL NL : ℕ}
    (hL : LetOK LT LC LI TL VL NL) {c : ℕ} (hc : c < NL) (hN : isN TL VL NL c = true) :
    xl xg LC (byte LI c) = (xl xg LC c)⁻¹ := by
  unfold xl
  rw [(hL.inv c hc).2.2]
  have := (hL.nval c hN).1
  exact letV_xor1 xg (by omega)

theorem byte_lt256 (x i : ℕ) : byte x i < 256 := land255_lt _

theorem byte_add_low {a v n i : ℕ} (hi : i < n) :
    byte (a + 2 ^ (8 * n) * v) i = byte a i := by
  unfold byte
  change ((a + 2 ^ (8 * n) * v) >>> (8 * i)) &&& 255 = (a >>> (8 * i)) &&& 255
  rw [show (255 : ℕ) = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
  have e : 2 ^ (8 * n) = 2 ^ (8 * i) * (256 * 2 ^ (8 * (n - i - 1))) := by
    rw [show (256 : ℕ) = 2 ^ 8 from rfl, ← Nat.pow_add, ← Nat.pow_add]
    congr 1
    omega
  rw [e, Nat.mul_assoc, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _),
    show (2 : ℕ) ^ 8 = 256 from rfl, Nat.mul_assoc 256, Nat.add_mul_mod_self_left]

theorem byte_add_at {a v n : ℕ} (ha : a < 2 ^ (8 * n)) (hv : v < 256) :
    byte (a + 2 ^ (8 * n) * v) n = v := by
  unfold byte
  change ((a + 2 ^ (8 * n) * v) >>> (8 * n)) &&& 255 = v
  rw [show (255 : ℕ) = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    Nat.shiftRight_eq_div_pow, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _),
    Nat.div_eq_of_lt ha, Nat.zero_add]
  exact Nat.mod_eq_of_lt hv

theorem mapW_spec (LC Wd : ℕ) : ∀ n, mapW LC Wd n < 2 ^ (8 * n) ∧
    ∀ i < n, byte (mapW LC Wd n) i = byte LC (byte Wd i)
  | 0 => ⟨by norm_num [mapW], fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | n + 1 => by
    obtain ⟨hlt, hb⟩ := mapW_spec LC Wd n
    have hv := byte_lt256 LC (byte Wd n)
    have hdef : mapW LC Wd (n + 1) = Nat.lor (mapW LC Wd n)
        (Nat.shiftLeft (byte LC (byte Wd n)) (Nat.mul 8 n)) := rfl
    have e : mapW LC Wd (n + 1) = mapW LC Wd n + 2 ^ (8 * n) * byte LC (byte Wd n) := by
      rw [hdef]
      change mapW LC Wd n ||| byte LC (byte Wd n) <<< (8 * n) = _
      rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt hlt, Nat.shiftLeft_eq, Nat.mul_comm,
        Nat.add_comm]
    rw [e]
    refine ⟨?_, fun i hi => ?_⟩
    · calc mapW LC Wd n + 2 ^ (8 * n) * byte LC (byte Wd n)
          < 2 ^ (8 * n) + 2 ^ (8 * n) * byte LC (byte Wd n) := by omega
        _ = 2 ^ (8 * n) * (byte LC (byte Wd n) + 1) := by ring
        _ ≤ 2 ^ (8 * n) * 256 := Nat.mul_le_mul_left _ hv
        _ = 2 ^ (8 * (n + 1)) := by
          rw [show 8 * (n + 1) = 8 * n + 8 by ring, Nat.pow_add]
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · rw [byte_add_low hi, hb i hi]
      · exact byte_add_at hlt hv

theorem wLen_enc {n M : ℕ} (hn : n < 1024) : LceS.wLen (4 * n + (M <<< 12)) = n := by
  unfold LceS.wLen
  change ((4 * n + (M <<< 12)) >>> 2) &&& 1023 = n
  have : (4 * n + (M <<< 12)) >>> 2 = n + 1024 * M := by
    rw [Nat.shiftRight_eq_div_pow, show (2 : ℕ) ^ 2 = 4 from rfl, Nat.shiftLeft_eq,
      show 4 * n + M * 2 ^ 12 = 4 * (n + 1024 * M) by ring,
      Nat.mul_div_cancel_left _ (by norm_num)]
  rw [this, show (1023 : ℕ) = 2 ^ 10 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem wWord_enc {n M : ℕ} (hn : n < 1024) : LceS.wWord (4 * n + (M <<< 12)) = M := by
  unfold LceS.wWord
  change (4 * n + (M <<< 12)) >>> 12 = M
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, show (2 : ℕ) ^ 12 = 4096 from rfl,
    Nat.mul_comm M, Nat.add_mul_div_left _ _ (by norm_num), Nat.div_eq_of_lt (by omega),
    Nat.zero_add]

theorem bval_eq_wv {G : Type*} [Group G] (y : ℕ → G) (W n : ℕ) :
    bval y W n = wv (letV y) W n := rfl

theorem wv_mapW {G : Type*} [Group G] (f : ℕ → G) (LC Wd n : ℕ) :
    wv f (mapW LC Wd n) n = wv (fun c => f (byte LC c)) Wd n := by
  unfold wv
  congr 1
  apply List.map_congr_left
  intro i hi
  have hi' : i < n := List.mem_range.1 hi
  rw [← byte_eq_byteG, ← byte_eq_byteG, (mapW_spec LC Wd n).2 i hi']

theorem relOK_enc {RR : ℕ → ℕ} {LT LC TL VL NL RH r : ℕ} (h : relOK RR LT LC TL VL NL RH r = true) :
    byte RH r < 39 ∧
      LceS.wWord (Hsw.sel (byte RH r)) = mapW LC (Nat.shiftRight (RR r) 12) (bits (RR r) 2 10) ∧
      LceS.wLen (Hsw.sel (byte RH r)) = bits (RR r) 2 10 ∧
      (∀ i < bits (RR r) 2 10, byte (Nat.shiftRight (RR r) 12) i < NL) ∧
      ((∀ i < bits (RR r) 2 10, isN TL VL NL (byte (Nat.shiftRight (RR r) 12) i) = true) →
        segProd LT TL VL NL (Nat.shiftRight (RR r) 12) 0 (bits (RR r) 2 10) = ident24) := by
  obtain ⟨hh, he, hl, hN⟩ := relOK_spec h
  have hn : bits (RR r) 2 10 < 1024 := by
    unfold bits
    change ((RR r) >>> 2) &&& (2 ^ 10 - 1) < 1024
    rw [Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_lt _ (by norm_num)
  refine ⟨hh, ?_, ?_, hl, hN⟩
  · rw [← he, wWord_enc hn]
  · rw [← he, wLen_enc hn]

theorem level_hrels {G : Type*} [Group G] (xg : ℕ → G)
    (hrel : ∀ k < 39, bval xg (LceS.wWord (Hsw.sel k)) (LceS.wLen (Hsw.sel k)) = 1)
    {RR : ℕ → ℕ} {LT LC TL VL NL RH NR : ℕ} (h : relsOK RR LT LC TL VL NL RH NR = true) :
    ∀ r < NR, rval (xl xg LC) (RR r) = 1 := by
  intro r hr
  obtain ⟨hh, hW, hn, -, -⟩ := relOK_enc (relsOK_spec h r hr)
  have hsel := hrel _ hh
  rw [hW, hn, bval_eq_wv, wv_mapW] at hsel
  exact hsel

@[expose] def lcB : ℕ := 20011376718272490338853433276725592320

@[expose] def rhB : ℕ :=
  1243246491195555662985712545119472705112553111610534931758030933907000127540406711912033812736

theorem lcB_byte : ∀ c < 16, byte lcB c = c := by
  decide +kernel

theorem rhB_byte : ∀ r < 39, byte rhB r = r := by
  decide +kernel

theorem hsw_letters14 : ∀ k < 27, ∀ i < LceS.wLen (Hsw.sel k),
    byte (LceS.wWord (Hsw.sel k)) i < 14 := by
  decide +kernel

theorem bLetters {LT LC LI TL VL NL : ℕ} (hL : LetOK LT LC LI TL VL NL) (hNL : NL = 16)
    (hLC : LC = lcB) :
    TL = 14 ∧ VL = 15 ∧ (∀ c, isN TL VL NL c = true ↔ c < 14) ∧
      ∀ c < 14, byte LI c = Nat.xor c 1 := by
  subst hLC hNL
  have hTL : TL = 14 := by
    have := hL.tc
    rw [lcB_byte TL hL.tl] at this
    exact this
  have hVL : VL = 15 := by
    have := hL.vc
    rw [lcB_byte VL hL.vl] at this
    exact this
  refine ⟨hTL, hVL, fun c => ?_, fun c hc => ?_⟩
  · rw [isN_iff, hTL, hVL]
    omega
  · obtain ⟨-, hlt, hcode⟩ := hL.inv c (by omega)
    rw [lcB_byte _ hlt, lcB_byte c (by omega)] at hcode
    exact hcode

theorem Lm_inv {LT LC LI TL VL NL : ℕ} (hL : LetOK LT LC LI TL VL NL) {c : ℕ}
    (hN : isN TL VL NL c = true) :
    Lm LT LI TL VL NL (byte LI c) = (Lm LT LI TL VL NL c)⁻¹ := by
  have hN' := hL.isN_inv hN
  apply eq_inv_of_mul_eq_one_right
  apply Units.ext
  rw [Units.val_mul, Lm_val hL hN, Lm_val hL hN', ← toMat_mul24, (hL.nval c hN).2, toMat_ident24]
  rfl

@[expose] noncomputable def Lgen (LT LI TL VL NL g : ℕ) : Mat24ˣ := Lm LT LI TL VL NL (2 * g)

@[expose] noncomputable abbrev Mgrp (LT LI TL VL NL : ℕ) : Subgroup Mat24ˣ :=
  Subgroup.closure (Lgen LT LI TL VL NL '' {g | g < 7})

theorem letV_Lgen {LT LC LI TL VL NL : ℕ} (hL : LetOK LT LC LI TL VL NL)
    (hl : ∀ c, isN TL VL NL c = true ↔ c < 14) (hli : ∀ c < 14, byte LI c = Nat.xor c 1) {c : ℕ}
    (hc : c < 14) : letV (Lgen LT LI TL VL NL) c = Lm LT LI TL VL NL c := by
  have hx : ∀ g < 7, Nat.xor (2 * g) 1 = 2 * g + 1 := by decide
  unfold letV
  rw [if_neg (by omega)]
  by_cases hp : c % 2 = 0
  · rw [if_pos hp]
    unfold Lgen
    congr 2
    omega
  · rw [if_neg hp]
    have hg : 2 * (c / 2) + 1 = c := by omega
    have h2 : isN TL VL NL (2 * (c / 2)) = true := (hl _).2 (by omega)
    have := Lm_inv hL h2
    rw [hli _ (by omega), hx _ (by omega), hg] at this
    unfold Lgen
    rw [← this]

theorem wv_Lm_of_segProd {LT LC LI TL VL NL : ℕ} (hL : LetOK LT LC LI TL VL NL) (Wd n : ℕ)
    (hN : ∀ i < n, isN TL VL NL (byte Wd i) = true)
    (h : segProd LT TL VL NL Wd 0 n = ident24) : wv (Lm LT LI TL VL NL) Wd n = 1 := by
  classical
  let x0 : ℕ → Mat24ˣ := fun c => if isN TL VL NL c = true then Lm LT LI TL VL NL c else 1
  have hC : MCtx (⊤ : Subgroup Mat24ˣ) LT LC LI TL VL NL x0 (Subgroup.subtype ⊤) :=
    { hL := hL
      hM := fun c _ => Subgroup.mem_top _
      hφ := fun c hc => by
        simp only [x0, if_pos hc]
        rfl
      hu := by
        have h1 : isN TL VL NL TL = false := by
          cases e : isN TL VL NL TL
          · rfl
          · exact absurd rfl (isN_iff.1 e).2.1
        have h2 : isN TL VL NL VL = false := by
          cases e : isN TL VL NL VL
          · rfl
          · exact absurd rfl (isN_iff.1 e).2.2
        simp [x0, h1, h2] }
  have hne : segProd LT TL VL NL Wd 0 n ≠ 0 := by
    rw [h]
    exact ident24_ne_zero
  obtain ⟨-, -, hv⟩ := rc_segProd hC Wd 0 n hne
  rw [h, rc_one] at hv
  unfold wv
  have e : (List.map (fun i => Lm LT LI TL VL NL (byteG Wd i)) (List.range n)).prod =
      (List.map (fun k => x0 (byte Wd (0 + k))) (List.range n)).prod := by
    congr 1
    apply List.map_congr_left
    intro i hi
    have hi' := List.mem_range.1 hi
    rw [Nat.zero_add, ← byte_eq_byteG]
    simp only [x0, if_pos (hN i hi')]
  rw [e, ← hv]

theorem Lgen_rel {RR : ℕ → ℕ} {LT LC LI TL VL NL RH NR : ℕ} (hL : LetOK LT LC LI TL VL NL)
    (hNL : NL = 16)
    (hLC : LC = lcB) (hNR : NR = 39)
    (hRH : RH = rhB)
    (hrels : relsOK RR LT LC TL VL NL RH NR = true) :
    ∀ k < 27, bval (Lgen LT LI TL VL NL) (LceS.wWord (Hsw.sel k)) (LceS.wLen (Hsw.sel k)) = 1 := by
  intro k hk
  obtain ⟨h14, h15, hl, hli⟩ := bLetters hL hNL hLC
  obtain ⟨hh, hW, hn, hlt, hseg⟩ := relOK_enc (relsOK_spec hrels k (by omega))
  have hRHk : byte RH k = k := by
    rw [hRH]
    exact rhB_byte k (by omega)
  rw [hRHk] at hW hn
  have hlet14 : ∀ i < bits (RR k) 2 10, byte (Nat.shiftRight (RR k) 12) i < 14 := by
    intro i hi
    have h1 := hsw_letters14 k hk i (by rw [hn]; exact hi)
    rw [hW, (mapW_spec LC _ _).2 i hi, hLC, lcB_byte _ (by have := hlt i hi; omega)] at h1
    exact h1
  rw [hW, hn, bval_eq_wv, wv_mapW]
  have e : wv (fun c => letV (Lgen LT LI TL VL NL) (byte LC c)) (Nat.shiftRight (RR k) 12)
      (bits (RR k) 2 10) =
        wv (Lm LT LI TL VL NL) (Nat.shiftRight (RR k) 12) (bits (RR k) 2 10) := by
    unfold wv
    congr 1
    apply List.map_congr_left
    intro i hi
    have hi' := List.mem_range.1 hi
    have hlt' := hlet14 i hi'
    simp only []
    rw [← byte_eq_byteG, hLC, lcB_byte _ (by omega)]
    exact letV_Lgen hL hl hli hlt'
  rw [e]
  have hN : ∀ i < bits (RR k) 2 10, isN TL VL NL (byte (Nat.shiftRight (RR k) 12) i) = true :=
    fun i hi => (hl _).2 (hlet14 i hi)
  exact wv_Lm_of_segProd hL _ _ hN (hseg hN)

theorem letV_mem {G : Type*} [Group G] (y : ℕ → G) {c : ℕ} (hc : c < 14) :
    letV y c ∈ Subgroup.closure (y '' {g | g < 7}) := by
  unfold letV
  rw [if_neg (by omega)]
  have hg : y (c / 2) ∈ Subgroup.closure (y '' {g | g < 7}) :=
    Subgroup.subset_closure ⟨c / 2, by simp only [Set.mem_setOf_eq]; omega, rfl⟩
  split_ifs
  · exact hg
  · exact Subgroup.inv_mem _ hg

theorem phi_letV {G : Type*} [Group G] {M : Subgroup Mat24ˣ} (φ : M →* G) (y : ℕ → Mat24ˣ)
    (x : ℕ → G) (hy : ∀ g < 7, ∃ h : y g ∈ M, φ ⟨y g, h⟩ = x g) {c : ℕ} (hc : c < 14)
    {z : Mat24ˣ} (hz : z ∈ M) (hzc : z = letV y c) : φ ⟨z, hz⟩ = letV x c := by
  have hc255 : c ≠ 255 := by omega
  unfold letV at hzc ⊢
  rw [if_neg hc255] at hzc ⊢
  obtain ⟨hm, hφ⟩ := hy (c / 2) (by omega)
  by_cases hp : c % 2 = 0
  · rw [if_pos hp] at hzc ⊢
    subst hzc
    exact hφ
  · rw [if_neg hp] at hzc ⊢
    subst hzc
    have : (⟨(y (c / 2))⁻¹, hz⟩ : M) = (⟨y (c / 2), hm⟩ : M)⁻¹ := rfl
    rw [this, map_inv, hφ]

theorem model_hom {G : Type*} [Group G] (xg : ℕ → G)
    (hrel : ∀ k < 39, bval xg (LceS.wWord (Hsw.sel k)) (LceS.wLen (Hsw.sel k)) = 1)
    {RR : ℕ → ℕ} {LT LC LI TL VL NL RH NR NORD : ℕ} (hL : LetOK LT LC LI TL VL NL)
    (hNL : NL = 16) (hLC : LC = lcB) (hNR : NR = 39)
    (hRH : RH = rhB)
    (hrels : relsOK RR LT LC TL VL NL RH NR = true)
    (hN : ∀ (H : Type) [Group H] (y : ℕ → H),
      (∀ k < 27, bval y (LceS.wWord (Hsw.sel k)) (LceS.wLen (Hsw.sel k)) = 1) →
        Finite (Subgroup.closure (y '' {g | g < 7})) ∧
          Nat.card (Subgroup.closure (y '' {g | g < 7})) ≤ NORD)
    (hM : NORD ≤ Nat.card (Mgrp LT LI TL VL NL)) :
    ∃ φ : Mgrp LT LI TL VL NL →* G, MCtx (Mgrp LT LI TL VL NL) LT LC LI TL VL NL (xl xg LC) φ ∧
      (∀ m, φ m ∈ Subgroup.closure (xg '' {g | g < 7})) ∧
      ∀ n ∈ Subgroup.closure (xg '' {g | g < 7}), ∃ m, φ m = n := by
  obtain ⟨h14, h15, hl, hli⟩ := bLetters hL hNL hLC
  obtain ⟨φ, hφ, hφN, hNφ⟩ := lift_hom RelSet {g | g < 7} NORD
    (fun H _ y hy => hN H y ((relSet_iff y).1 hy)) (Lgen LT LI TL VL NL)
    ((relSet_iff _).2 (Lgen_rel hL hNL hLC hNR hRH hrels)) hM xg
    ((relSet_iff _).2 (fun k hk => hrel k (by omega)))
  refine ⟨φ, ?_, hφN, hNφ⟩
  have hMem : ∀ c, isN TL VL NL c = true → Lm LT LI TL VL NL c ∈ Mgrp LT LI TL VL NL := by
    intro c hc
    have hc14 := (hl c).1 hc
    rw [← letV_Lgen hL hl hli hc14]
    exact letV_mem _ hc14
  refine ⟨hL, hMem, fun c hc => ?_, ?_⟩
  · have hc14 := (hl c).1 hc
    have h := phi_letV φ (Lgen LT LI TL VL NL) xg (fun g hg => ⟨Subgroup.subset_closure
      ⟨g, hg, rfl⟩, hφ g hg⟩) hc14 (hMem c hc) (letV_Lgen hL hl hli hc14).symm
    rw [h]
    unfold xl
    rw [hLC, lcB_byte c (by omega)]
  · obtain ⟨h1, h2⟩ := xl_u xg hL
    rw [h1, h2]

end CFSG.KC.Th.Spec.Dce

end
