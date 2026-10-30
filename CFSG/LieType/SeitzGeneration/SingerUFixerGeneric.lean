module

public import CFSG.LieType.SeitzGeneration.SingerUCayley
public import CFSG.LieType.SeitzGeneration.SingerUNorms

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open scoped Fin.NatCast

variable {ℓ f : ℕ} {K : Type} [Field K]

theorem singerUG_val_natCast {p : ℕ} [NeZero p] {k : ℕ} (hk : k < p) :
    ((k : Fin p) : ℕ) = k := by
  rw [Fin.val_natCast, Nat.mod_eq_of_lt hk]

theorem singerUG_natCast_ne_zero {p : ℕ} [NeZero p] {k : ℕ} (hk0 : 0 < k) (hk : k < p) :
    (k : Fin p) ≠ 0 := by
  intro h0
  have := congrArg Fin.val h0
  rw [singerUG_val_natCast hk] at this
  simp at this
  omega

theorem singerUG_val_sub_one {p : ℕ} [NeZero p] (x : Fin p) (hp : 1 < p) :
    ((x - 1 : Fin p) : ℕ) = if (x : ℕ) = 0 then p - 1 else (x : ℕ) - 1 := by
  rw [Fin.val_sub, Fin.val_one', Nat.mod_eq_of_lt hp]
  have hx := x.isLt
  split_ifs with h0
  · rw [h0, add_zero, Nat.mod_eq_of_lt (by omega)]
  · rw [show p - 1 + (x : ℕ) = ((x : ℕ) - 1) + p by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]

theorem singerUG_natCast_sub_one {p : ℕ} [NeZero p] {k : ℕ} (hk : 1 ≤ k) (hkp : k < p) :
    (k : Fin p) - 1 = ((k - 1 : ℕ) : Fin p) := by
  apply Fin.ext
  rw [singerUG_val_sub_one _ (by omega), singerUG_val_natCast hkp,
    singerUG_val_natCast (by omega : k - 1 < p), if_neg (by omega)]

theorem singerUG_zero_sub_one {p : ℕ} [NeZero p] (hp : 2 ≤ p) :
    (0 : Fin p) - 1 = ((p - 1 : ℕ) : Fin p) := by
  apply Fin.ext
  rw [singerUG_val_sub_one _ (by omega), singerUG_val_natCast (by omega), Fin.val_zero,
    if_pos rfl]

theorem singerUG_star_mulVec (h : UnitaryFieldData ℓ f K) {p : ℕ} [NeZero p] (hodd : Odd p)
    {c ε : K} (hc : c ≠ 0) (hE : c + h.bar ε ^ p ≠ 0) (v : Fin p → K) (k : Fin p) :
    (companionMat p c *ᵥ (thmU_cayleyMat h p c ε *ᵥ v)) k +
        h.bar ε * (thmU_cayleyMat h p c ε *ᵥ v) k =
      (companionMat p c *ᵥ v) k + ε * (companionMat p c *ᵥ (companionMat p c *ᵥ v)) k := by
  have hstar := thmU_cayley_star_rel h ε hodd hc hE
  have key : (companionMat p c + h.bar ε • (1 : Matrix (Fin p) (Fin p) K)) *ᵥ
      (thmU_cayleyMat h p c ε *ᵥ v) = (companionMat p c + ε • companionMat p c ^ 2) *ᵥ v := by
    rw [mulVec_mulVec, hstar]
  have hL : (companionMat p c + h.bar ε • (1 : Matrix (Fin p) (Fin p) K)) *ᵥ
      (thmU_cayleyMat h p c ε *ᵥ v) = companionMat p c *ᵥ (thmU_cayleyMat h p c ε *ᵥ v) +
        h.bar ε • (thmU_cayleyMat h p c ε *ᵥ v) := by
    rw [add_mulVec, smul_mulVec, one_mulVec]
  have hR : (companionMat p c + ε • companionMat p c ^ 2) *ᵥ v = companionMat p c *ᵥ v +
      ε • (companionMat p c *ᵥ (companionMat p c *ᵥ v)) := by
    rw [add_mulVec, smul_mulVec, pow_two, ← mulVec_mulVec]
  have := congrFun (hL.symm.trans (key.trans hR)) k
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
  linear_combination this

theorem singerUG_rhs_natCast {p : ℕ} [NeZero p] (c e : K) (v : Fin p → K) {l : ℕ}
    (hl2 : 2 ≤ l) (hlp : l < p) :
    (companionMat p c *ᵥ v) (l : Fin p) +
        e * (companionMat p c *ᵥ (companionMat p c *ᵥ v)) (l : Fin p) =
      v ((l - 1 : ℕ) : Fin p) + e * v ((l - 2 : ℕ) : Fin p) := by
  have h1 : (l : Fin p) ≠ 0 := singerUG_natCast_ne_zero (by omega) hlp
  have h1' : (l : Fin p) - 1 = ((l - 1 : ℕ) : Fin p) := singerUG_natCast_sub_one (by omega) hlp
  have h2 : ((l - 1 : ℕ) : Fin p) ≠ 0 := singerUG_natCast_ne_zero (by omega) (by omega)
  have h2' : ((l - 1 : ℕ) : Fin p) - 1 = ((l - 2 : ℕ) : Fin p) := by
    rw [singerUG_natCast_sub_one (by omega) (by omega), show l - 1 - 1 = l - 2 by omega]
  rw [thmU_companionMat_mulVec c v (l : Fin p),
    thmU_companionMat_mulVec c (companionMat p c *ᵥ v) (l : Fin p), if_neg h1]
  simp only [one_mul]
  rw [h1', thmU_companionMat_mulVec c v ((l - 1 : ℕ) : Fin p), if_neg h2, one_mul, h2']

theorem singerUG_rhs_zero {p : ℕ} [NeZero p] (c e : K) (v : Fin p → K) (hp : 3 ≤ p) :
    (companionMat p c *ᵥ v) 0 + e * (companionMat p c *ᵥ (companionMat p c *ᵥ v)) 0 =
      c * v ((p - 1 : ℕ) : Fin p) + e * (c * v ((p - 2 : ℕ) : Fin p)) := by
  have hz : (0 : Fin p) - 1 = ((p - 1 : ℕ) : Fin p) := singerUG_zero_sub_one (by omega)
  have hz0 : ((p - 1 : ℕ) : Fin p) ≠ 0 := singerUG_natCast_ne_zero (by omega) (by omega)
  have hz2 : ((p - 1 : ℕ) : Fin p) - 1 = ((p - 2 : ℕ) : Fin p) := by
    rw [singerUG_natCast_sub_one (by omega) (by omega), show p - 1 - 1 = p - 2 by omega]
  rw [thmU_companionMat_mulVec c v 0, thmU_companionMat_mulVec c (companionMat p c *ᵥ v) 0,
    if_pos rfl, hz]
  rw [thmU_companionMat_mulVec c v ((p - 1 : ℕ) : Fin p), if_neg hz0, one_mul, hz2]

theorem singerUG_rhs_one {p : ℕ} [NeZero p] (c e : K) (v : Fin p → K) (hp : 3 ≤ p) :
    (companionMat p c *ᵥ v) 1 + e * (companionMat p c *ᵥ (companionMat p c *ᵥ v)) 1 =
      v 0 + e * (c * v ((p - 1 : ℕ) : Fin p)) := by
  have hz : (0 : Fin p) - 1 = ((p - 1 : ℕ) : Fin p) := singerUG_zero_sub_one (by omega)
  have h1 : (1 : Fin p) ≠ 0 := by
    intro h0
    have := congrArg Fin.val h0
    rw [Fin.val_one', Fin.val_zero, Nat.mod_eq_of_lt (by omega : 1 < p)] at this
    omega
  rw [thmU_companionMat_mulVec c v 1, if_neg h1, one_mul, sub_self,
    thmU_companionMat_mulVec c (companionMat p c *ᵥ v) 1, if_neg h1, one_mul, sub_self,
    thmU_companionMat_mulVec c v 0, if_pos rfl, hz]

theorem singerUG_beta_zero (h : UnitaryFieldData ℓ f K) {p : ℕ} [NeZero p] (hodd : Odd p)
    (hp3 : 3 ≤ p) {c ε : K} (hc : c ≠ 0) (hE : h.bar ε ^ p + c ≠ 0) :
    thmU_cayleyMat h p c ε 0 0 = c * (1 - h.bar ε * ε) / (h.bar ε ^ p + c) := by
  rw [thmU_cayleyMat_apply_zero h hodd hp3 hc hE 0]
  simp

theorem singerUG_beta_natCast (h : UnitaryFieldData ℓ f K) {p : ℕ} [NeZero p] (hodd : Odd p)
    (hp3 : 3 ≤ p) {c ε : K} (hc : c ≠ 0) (hE : h.bar ε ^ p + c ≠ 0) {k : ℕ} (hk2 : 2 ≤ k)
    (hkp : k < p) :
    thmU_cayleyMat h p c ε (k : Fin p) 0 =
      (-1) ^ (k - 1) * h.bar ε ^ (p - k) * (1 - h.bar ε * ε) / (h.bar ε ^ p + c) := by
  rw [thmU_cayleyMat_apply_zero h hodd hp3 hc hE (k : Fin p), singerUG_val_natCast hkp,
    if_neg (by omega), if_neg (by omega)]

theorem singerUG_beta_succ (h : UnitaryFieldData ℓ f K) {p : ℕ} [NeZero p] (hodd : Odd p)
    (hp3 : 3 ≤ p) {c ε : K} (hc : c ≠ 0) (hE : h.bar ε ^ p + c ≠ 0) (hd : h.bar ε ≠ 0)
    {k : ℕ} (hk2 : 2 ≤ k) (hkp : k + 1 < p) :
    thmU_cayleyMat h p c ε ((k + 1 : ℕ) : Fin p) 0 =
      -(h.bar ε)⁻¹ * thmU_cayleyMat h p c ε (k : Fin p) 0 := by
  rw [singerUG_beta_natCast h hodd hp3 hc hE (by omega) hkp,
    singerUG_beta_natCast h hodd hp3 hc hE hk2 (by omega)]
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  have e2 : j + 2 + 1 - 1 = (j + 2) := by omega
  have e3 : j + 2 - 1 = j + 1 := by omega
  rw [e2, e3]
  have e4 : p - (j + 2) = (p - (j + 2 + 1)) + 1 := by omega
  rw [e4, pow_succ, pow_succ]
  field_simp
  ring

theorem singerUG_step_eq {s0 s1 β0 β1 d e : K} (hd : d ≠ 0) (hβ0 : β0 ≠ 0)
    (hβ : β1 = -(d⁻¹) * β0) (hrel : s1 * β1 + e * (s0 * β0) = 0) : s1 = d * e * s0 := by
  subst hβ
  have h2 : β0 * (-(d⁻¹) * s1 + e * s0) = 0 := by linear_combination hrel
  have h3 : -(d⁻¹) * s1 + e * s0 = 0 := (mul_eq_zero.mp h2).resolve_left hβ0
  have hdd : d * d⁻¹ = 1 := mul_inv_cancel₀ hd
  linear_combination (-d) * h3 - s1 * hdd

theorem singerUG_norm_false (h : UnitaryFieldData ℓ f K) {n s0 s1 : K} (hn : h.bar n = n)
    (hn2 : n * n ≠ 1) (hs0 : h.norm s0 = 1) (hs1 : h.norm s1 = 1) (hrel : s1 = n * s0) :
    False := by
  have h1 : h.norm s1 = (n * n) * h.norm s0 := by
    rw [hrel, singerU_norm_mul, UnitaryFieldData.norm, hn]
  rw [hs0, hs1, mul_one] at h1
  exact hn2 h1.symm

theorem singerUG_beta_zero_rel (h : UnitaryFieldData ℓ f K) {p : ℕ} [NeZero p] (hodd : Odd p)
    (hp3 : 3 ≤ p) {c ε : K} (hc : c ≠ 0) (hE : h.bar ε ^ p + c ≠ 0) (hd : h.bar ε ≠ 0) :
    thmU_cayleyMat h p c ε 0 0 =
      -(c * (h.bar ε)⁻¹) * thmU_cayleyMat h p c ε ((p - 1 : ℕ) : Fin p) 0 := by
  have hodd2 : Odd (p - 2) := Nat.odd_iff.mpr (by have := Nat.odd_iff.mp hodd; omega)
  rw [singerUG_beta_zero h hodd hp3 hc hE,
    singerUG_beta_natCast h hodd hp3 hc hE (by omega : 2 ≤ p - 1) (by omega : p - 1 < p)]
  have e1 : p - 1 - 1 = p - 2 := by omega
  have e2 : p - (p - 1) = 1 := by omega
  rw [e1, e2, hodd2.neg_one_pow, pow_one]
  field_simp

theorem singerUG_p5_alg (h : UnitaryFieldData ℓ f K) {n s2 s3 s4 : K} (hn : h.bar n = n)
    (hn0 : n ≠ 0) (hn1 : n ≠ 1) (h2 : h.norm s2 = 1) (h3 : h.norm s3 = 1)
    (h4 : h.norm s4 = 1) (hrel : s4 + (1 - n) * s3 = n * s2) : s2 + s3 = 0 := by
  have hs2 : s2 * h.bar s2 = 1 := h2
  have hs3 : s3 * h.bar s3 = 1 := h3
  have hs4 : s4 * h.bar s4 = 1 := h4
  have hbar : h.bar s4 + (1 - n) * h.bar s3 = n * h.bar s2 := by
    have := congrArg h.bar hrel
    simp only [map_add, map_mul, map_sub, map_one, hn] at this
    exact this
  have hN : (s4 + (1 - n) * s3) * (h.bar s4 + (1 - n) * h.bar s3) =
      (n * s2) * (n * h.bar s2) := by
    rw [hrel, hbar]
  have key : (1 - n) * (s4 * h.bar s3 + h.bar s4 * s3 + 2) = 0 := by
    linear_combination hN - hs4 - (1 - n) ^ 2 * hs3 + n ^ 2 * hs2
  have ht : (1 - n) ≠ 0 := sub_ne_zero.mpr (Ne.symm hn1)
  have hsum : s4 * h.bar s3 + h.bar s4 * s3 = -2 :=
    by linear_combination (mul_eq_zero.mp key).resolve_left ht
  have hξN : h.norm (s4 * h.bar s3) = 1 := by
    show s4 * h.bar s3 * h.bar (s4 * h.bar s3) = 1
    rw [map_mul, h.bar_bar]
    linear_combination (s3 * h.bar s3) * hs4 + hs3
  have hξ' : (s4 * h.bar s3) + (s4 * h.bar s3)⁻¹ = -2 := by
    rw [← singerU_bar_eq_inv_of_norm_one h hξN, map_mul, h.bar_bar]
    linear_combination hsum
  have hξ1 : s4 * h.bar s3 = -1 := singerU_eq_neg_one_of_add_inv h hξN hξ'
  have h43 : s4 = -s3 := by linear_combination s3 * hξ1 - s4 * hs3
  have hm : n * (s2 + s3) = 0 := by linear_combination (-1 : K) * hrel + h43
  exact (mul_eq_zero.mp hm).resolve_left hn0

theorem singerUG_val_one {p : ℕ} [NeZero p] (hp : 1 < p) : ((1 : Fin p) : ℕ) = 1 := by
  rw [Fin.val_one', Nat.mod_eq_of_lt hp]

theorem singerUG_one_ne_zero {p : ℕ} [NeZero p] (hp : 1 < p) : (1 : Fin p) ≠ 0 := by
  intro h0
  have := congrArg Fin.val h0
  rw [singerUG_val_one hp] at this
  simp at this

theorem singerUG_ne_of_val_ne {p : ℕ} {x y : Fin p} (hxy : (x : ℕ) ≠ (y : ℕ)) : x ≠ y :=
  fun e => hxy (by rw [e])

theorem singerUG_beta_zero_ne (h : UnitaryFieldData ℓ f K) {p : ℕ} [NeZero p] (hodd : Odd p)
    (hp3 : 3 ≤ p) {c ε : K} (hc : c ≠ 0) (hE : h.bar ε ^ p + c ≠ 0)
    (hone : 1 - h.bar ε * ε ≠ 0) : thmU_cayleyMat h p c ε 0 0 ≠ 0 := by
  rw [singerUG_beta_zero h hodd hp3 hc hE]
  exact div_ne_zero (mul_ne_zero hc hone) hE

theorem singerUG_beta_natCast_ne (h : UnitaryFieldData ℓ f K) {p : ℕ} [NeZero p] (hodd : Odd p)
    (hp3 : 3 ≤ p) {c ε : K} (hc : c ≠ 0) (hE : h.bar ε ^ p + c ≠ 0) (hd : h.bar ε ≠ 0)
    (hone : 1 - h.bar ε * ε ≠ 0) {k : ℕ} (hk2 : 2 ≤ k) (hkp : k < p) :
    thmU_cayleyMat h p c ε (k : Fin p) 0 ≠ 0 := by
  rw [singerUG_beta_natCast h hodd hp3 hc hE hk2 hkp]
  exact div_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num))
    (pow_ne_zero _ hd)) hone) hE

theorem singerUG_beta_last (h : UnitaryFieldData ℓ f K) {p : ℕ} [NeZero p] (hodd : Odd p)
    (hp5 : 5 ≤ p) {c ε : K} (hc : c ≠ 0) (hE : h.bar ε ^ p + c ≠ 0) (hd : h.bar ε ≠ 0) :
    thmU_cayleyMat h p c ε ((p - 1 : ℕ) : Fin p) 0 =
      -(h.bar ε)⁻¹ * thmU_cayleyMat h p c ε ((p - 2 : ℕ) : Fin p) 0 := by
  have := singerUG_beta_succ h hodd (by omega) hc hE hd (k := p - 2) (by omega) (by omega)
  rwa [show p - 2 + 1 = p - 1 by omega] at this

theorem singerUG_p5_chain {d ε c wA s2 s3 s4 β2 β3 β4 : K} (hd : d ≠ 0) (hc : c ≠ 0)
    (hβ2 : β2 ≠ 0) (hb3 : β3 = -(d⁻¹) * β2) (hb4 : β4 = -(d⁻¹) * β3)
    (hwA : c * wA = c * (s4 * β4) + ε * (c * (s3 * β3)))
    (hdwA : d * wA = s3 * β3 + ε * (s2 * β2)) :
    s4 + (1 - d * ε) * s3 = d * ε * s2 := by
  have hwA' : wA = s4 * β4 + ε * (s3 * β3) := by
    have h0 : c * (wA - (s4 * β4 + ε * (s3 * β3))) = 0 := by linear_combination hwA
    linear_combination (mul_eq_zero.mp h0).resolve_left hc
  have hdd : d * d⁻¹ = 1 := mul_inv_cancel₀ hd
  rw [hwA', hb4, hb3] at hdwA
  have key : β2 * (d⁻¹ * (s4 + (1 - d * ε) * s3 - d * ε * s2)) = 0 := by
    linear_combination hdwA - (β2 * d⁻¹ * s4 + ε * s2 * β2) * hdd
  have h1 := (mul_eq_zero.mp key).resolve_left hβ2
  have h2 := (mul_eq_zero.mp h1).resolve_left (inv_ne_zero hd)
  linear_combination h2

theorem singerUG_three_coords (h : UnitaryFieldData ℓ f K) {p : ℕ} [NeZero p] (hodd : Odd p)
    (hp5 : 5 ≤ p) {c ε : K} (hc : c ≠ 0) (hE : h.bar ε ^ p + c ≠ 0) (hε : ε ≠ 0)
    (hn1 : h.norm ε ≠ 1) (hn2 : h.norm ε ≠ -1)
    {s : Fin p → K} (hs : ∀ k, h.norm (s k) = 1)
    {w v : Fin p → K} (hv : ∀ k, v k = s k * thmU_cayleyMat h p c ε k 0)
    (hw : w = thmU_cayleyMat h p c ε *ᵥ v) (hw0 : w 0 = 0)
    (hsum : p = 5 → s ((2 : ℕ) : Fin p) + s ((3 : ℕ) : Fin p) ≠ 0) :
    ∃ a b' c' : Fin p, a ≠ b' ∧ a ≠ c' ∧ b' ≠ c' ∧ w a ≠ 0 ∧ w b' ≠ 0 ∧ w c' ≠ 0 := by
  have hodd' : p % 2 = 1 := Nat.odd_iff.mp hodd
  have hp3 : 3 ≤ p := by omega
  have hd : h.bar ε ≠ 0 := (map_ne_zero h.bar).mpr hε
  have hd' : h.bar ε * ε = h.norm ε := by rw [UnitaryFieldData.norm, mul_comm]
  have hone : 1 - h.bar ε * ε ≠ 0 := by
    rw [hd']
    exact sub_ne_zero.mpr (Ne.symm hn1)
  have hnn : h.norm ε * h.norm ε ≠ 1 := by
    intro H
    have h0 : (h.norm ε - 1) * (h.norm ε + 1) = 0 := by linear_combination H
    rcases mul_eq_zero.mp h0 with h1 | h1
    · exact hn1 (by linear_combination h1)
    · exact hn2 (by linear_combination h1)
  have hnfix : h.bar (h.norm ε) = h.norm ε := singerU_norm_fixed h ε
  have hnz : h.norm ε ≠ 0 := singerU_norm_ne_zero h hε
  have hEc : c + h.bar ε ^ p ≠ 0 := by rwa [add_comm] at hE
  have hS : ∀ k : Fin p, (companionMat p c *ᵥ w) k + h.bar ε * w k =
      (companionMat p c *ᵥ v) k + ε * (companionMat p c *ᵥ (companionMat p c *ᵥ v)) k := by
    intro k
    rw [hw]
    exact singerUG_star_mulVec h hodd hc hEc v k
  have hcontra : ∀ s0 s1 : K, h.norm s0 = 1 → h.norm s1 = 1 → s1 = h.norm ε * s0 → False :=
    fun s0 s1 h0 h1 hr => singerUG_norm_false h hnfix hnn h0 h1 hr
  have hA : (companionMat p c *ᵥ w) 0 = c * w ((p - 1 : ℕ) : Fin p) := by
    rw [thmU_companionMat_mulVec c w 0, if_pos rfl, singerUG_zero_sub_one (p := p) (by omega)]
  have hP1 : w 1 ≠ 0 := by
    intro hw1
    have hL : (companionMat p c *ᵥ w) 1 + h.bar ε * w 1 = 0 := by
      rw [thmU_companionMat_mulVec c w 1, if_neg (singerUG_one_ne_zero (p := p) (by omega)),
        one_mul, sub_self, hw0, hw1, mul_zero, add_zero]
    have hR := hS 1
    rw [hL, singerUG_rhs_one c ε v hp3, hv 0, hv ((p - 1 : ℕ) : Fin p),
      singerUG_beta_zero_rel h hodd hp3 hc hE hd] at hR
    have hβ1 : thmU_cayleyMat h p c ε ((p - 1 : ℕ) : Fin p) 0 ≠ 0 :=
      singerUG_beta_natCast_ne h hodd hp3 hc hE hd hone (by omega) (by omega)
    have hfac : (c * thmU_cayleyMat h p c ε ((p - 1 : ℕ) : Fin p) 0) *
        (-(h.bar ε)⁻¹ * s 0 + ε * s ((p - 1 : ℕ) : Fin p)) = 0 := by
      linear_combination (-1 : K) * hR
    have hfac2 := (mul_eq_zero.mp hfac).resolve_left (mul_ne_zero hc hβ1)
    have hdd : h.bar ε * (h.bar ε)⁻¹ = 1 := mul_inv_cancel₀ hd
    have hrel : s 0 = h.norm ε * s ((p - 1 : ℕ) : Fin p) := by
      rw [← hd']
      linear_combination (-(h.bar ε)) * hfac2 - s 0 * hdd
    exact hcontra (s ((p - 1 : ℕ) : Fin p)) (s 0) (hs _) (hs _) hrel
  have hPl : w ((p - 1 : ℕ) : Fin p) ≠ 0 := by
    intro hwl
    have hL : (companionMat p c *ᵥ w) 0 + h.bar ε * w 0 = 0 := by
      rw [hA, hwl, hw0, mul_zero, mul_zero, add_zero]
    have hR := hS 0
    rw [hL, singerUG_rhs_zero c ε v hp3, hv ((p - 1 : ℕ) : Fin p),
      hv ((p - 2 : ℕ) : Fin p)] at hR
    have hR2 : c * (s ((p - 1 : ℕ) : Fin p) * thmU_cayleyMat h p c ε ((p - 1 : ℕ) : Fin p) 0 +
        ε * (s ((p - 2 : ℕ) : Fin p) * thmU_cayleyMat h p c ε ((p - 2 : ℕ) : Fin p) 0)) = 0 := by
      linear_combination (-1 : K) * hR
    have hR3 := (mul_eq_zero.mp hR2).resolve_left hc
    have hβ2 : thmU_cayleyMat h p c ε ((p - 2 : ℕ) : Fin p) 0 ≠ 0 :=
      singerUG_beta_natCast_ne h hodd hp3 hc hE hd hone (by omega) (by omega)
    have hrel := singerUG_step_eq hd hβ2 (singerUG_beta_last h hodd hp5 hc hE hd) hR3
    rw [hd'] at hrel
    exact hcontra (s ((p - 2 : ℕ) : Fin p)) (s ((p - 1 : ℕ) : Fin p)) (hs _) (hs _) hrel
  have hP4 : w ((3 : ℕ) : Fin p) ≠ 0 ∨ w ((4 : ℕ) : Fin p) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨h3, h4⟩ := hcon
    have hL : (companionMat p c *ᵥ w) ((4 : ℕ) : Fin p) +
        h.bar ε * w ((4 : ℕ) : Fin p) = 0 := by
      rw [thmU_companionMat_mulVec c w ((4 : ℕ) : Fin p),
        if_neg (singerUG_natCast_ne_zero (k := 4) (by norm_num) (by omega)), one_mul,
        singerUG_natCast_sub_one (k := 4) (by norm_num) (by omega), show 4 - 1 = 3 from rfl,
        h3, h4, mul_zero, add_zero]
    have hR := hS ((4 : ℕ) : Fin p)
    rw [hL, singerUG_rhs_natCast c ε v (l := 4) (by norm_num) (by omega),
      show 4 - 1 = 3 from rfl, show 4 - 2 = 2 from rfl, hv ((3 : ℕ) : Fin p),
      hv ((2 : ℕ) : Fin p)] at hR
    have hβ2 : thmU_cayleyMat h p c ε ((2 : ℕ) : Fin p) 0 ≠ 0 :=
      singerUG_beta_natCast_ne h hodd hp3 hc hE hd hone (by norm_num) (by omega)
    have hb3 : thmU_cayleyMat h p c ε ((3 : ℕ) : Fin p) 0 =
        -(h.bar ε)⁻¹ * thmU_cayleyMat h p c ε ((2 : ℕ) : Fin p) 0 :=
      singerUG_beta_succ h hodd hp3 hc hE hd (k := 2) (by norm_num) (by omega)
    have hrel := singerUG_step_eq hd hβ2 hb3 hR.symm
    rw [hd'] at hrel
    exact hcontra (s ((2 : ℕ) : Fin p)) (s ((3 : ℕ) : Fin p)) (hs _) (hs _) hrel
  rcases (show p = 5 ∨ 7 ≤ p by omega) with hp | hp7
  ·
    by_contra H3
    have hw3 : w ((3 : ℕ) : Fin p) = 0 := by
      by_contra hne
      exact H3 ⟨1, ((p - 1 : ℕ) : Fin p), ((3 : ℕ) : Fin p),
        singerUG_ne_of_val_ne (by rw [singerUG_val_one (p := p) (by omega),
          singerUG_val_natCast (k := p - 1) (by omega)]; omega),
        singerUG_ne_of_val_ne (by rw [singerUG_val_one (p := p) (by omega),
          singerUG_val_natCast (k := 3) (by omega)]; omega),
        singerUG_ne_of_val_ne (by rw [singerUG_val_natCast (k := p - 1) (by omega),
          singerUG_val_natCast (k := 3) (by omega)]; omega),
        hP1, hPl, hne⟩
    have hLA : (companionMat p c *ᵥ w) ((p - 1 : ℕ) : Fin p) = 0 := by
      rw [thmU_companionMat_mulVec c w ((p - 1 : ℕ) : Fin p),
        if_neg (singerUG_natCast_ne_zero (k := p - 1) (by omega) (by omega)), one_mul,
        singerUG_natCast_sub_one (k := p - 1) (by omega) (by omega),
        show p - 1 - 1 = 3 by omega, hw3]
    have hS0 := hS 0
    rw [hA, hw0, mul_zero, add_zero, singerUG_rhs_zero c ε v hp3, hv ((p - 1 : ℕ) : Fin p),
      hv ((p - 2 : ℕ) : Fin p)] at hS0
    have hS4 := hS ((p - 1 : ℕ) : Fin p)
    rw [hLA, zero_add, singerUG_rhs_natCast c ε v (l := p - 1) (by omega) (by omega),
      show p - 1 - 1 = p - 2 by omega, show p - 1 - 2 = p - 3 by omega, hv ((p - 2 : ℕ) : Fin p),
      hv ((p - 3 : ℕ) : Fin p)] at hS4
    have hb3 := singerUG_beta_succ h hodd (by omega) hc hE hd (k := p - 3) (by omega) (by omega)
    rw [show p - 3 + 1 = p - 2 by omega] at hb3
    have hβ2 : thmU_cayleyMat h p c ε ((p - 3 : ℕ) : Fin p) 0 ≠ 0 :=
      singerUG_beta_natCast_ne h hodd hp3 hc hE hd hone (by omega) (by omega)
    have hrel := singerUG_p5_chain hd hc hβ2 hb3 (singerUG_beta_last h hodd hp5 hc hE hd) hS0
      hS4
    rw [hd'] at hrel
    have hfin := singerUG_p5_alg h hnfix hnz hn1 (hs ((p - 3 : ℕ) : Fin p))
      (hs ((p - 2 : ℕ) : Fin p)) (hs ((p - 1 : ℕ) : Fin p)) hrel
    rw [show p - 3 = 2 by omega, show p - 2 = 3 by omega] at hfin
    exact hsum hp hfin
  · rcases hP4 with h3 | h4
    · exact ⟨1, ((p - 1 : ℕ) : Fin p), ((3 : ℕ) : Fin p),
        singerUG_ne_of_val_ne (by rw [singerUG_val_one (p := p) (by omega),
          singerUG_val_natCast (k := p - 1) (by omega)]; omega),
        singerUG_ne_of_val_ne (by rw [singerUG_val_one (p := p) (by omega),
          singerUG_val_natCast (k := 3) (by omega)]; omega),
        singerUG_ne_of_val_ne (by rw [singerUG_val_natCast (k := p - 1) (by omega),
          singerUG_val_natCast (k := 3) (by omega)]; omega),
        hP1, hPl, h3⟩
    · exact ⟨1, ((p - 1 : ℕ) : Fin p), ((4 : ℕ) : Fin p),
        singerUG_ne_of_val_ne (by rw [singerUG_val_one (p := p) (by omega),
          singerUG_val_natCast (k := p - 1) (by omega)]; omega),
        singerUG_ne_of_val_ne (by rw [singerUG_val_one (p := p) (by omega),
          singerUG_val_natCast (k := 4) (by omega)]; omega),
        singerUG_ne_of_val_ne (by rw [singerUG_val_natCast (k := p - 1) (by omega),
          singerUG_val_natCast (k := 4) (by omega)]; omega),
        hP1, hPl, h4⟩

theorem singerUG_val_two {p : ℕ} [NeZero p] (hp : 3 ≤ p) : ((2 : Fin p) : ℕ) = 2 := by
  rw [show (2 : Fin p) = ((2 : ℕ) : Fin p) from rfl, singerUG_val_natCast (by omega)]

theorem singerUG_ne_iff_val {p : ℕ} {x y : Fin p} {k : ℕ} (hy : (y : ℕ) = k) :
    x ≠ y ↔ (x : ℕ) ≠ k :=
  ⟨fun h e => h (Fin.ext (e.trans hy.symm)), fun h e => h (by rw [e, hy])⟩

def singerUG_mid (K : Type) [Field K] {p : ℕ} (j : Fin p) : K :=
  if 2 * (j : ℕ) < p then 1 else -1

def singerUG_rest (p : ℕ) [NeZero p] : Finset (Fin p) :=
  ((((Finset.univ.erase 0).erase 1).erase ((p - 1 : ℕ) : Fin p)).erase 2).erase
    ((p - 2 : ℕ) : Fin p)

def singerUG_s (K : Type) [Field K] {p : ℕ} [NeZero p] (A ρ E : K) (j : Fin p) : K :=
  if j = 0 then A * E⁻¹ else if j = 1 then E ^ 2 else if j = 2 then E⁻¹
  else if j = ((p - 1 : ℕ) : Fin p) then -(E ^ 2)
  else if j = ((p - 2 : ℕ) : Fin p) then ρ * E⁻¹ else singerUG_mid K j

theorem singerUG_mem_rest {p : ℕ} [NeZero p] (hp : 5 ≤ p) (j : Fin p) :
    j ∈ singerUG_rest p ↔ 3 ≤ (j : ℕ) ∧ (j : ℕ) ≤ p - 3 := by
  unfold singerUG_rest
  simp only [Finset.mem_erase, Finset.mem_univ, and_true]
  have hj := j.isLt
  rw [singerUG_ne_iff_val (y := ((p - 2 : ℕ) : Fin p)) (singerUG_val_natCast (by omega)),
    singerUG_ne_iff_val (y := 2) (singerUG_val_two (by omega)),
    singerUG_ne_iff_val (y := ((p - 1 : ℕ) : Fin p)) (singerUG_val_natCast (by omega)),
    singerUG_ne_iff_val (y := 1) (singerUG_val_one (by omega)),
    singerUG_ne_iff_val (y := 0) (Fin.val_zero p)]
  omega

theorem singerUG_sum_split {M : Type} [AddCommMonoid M] {p : ℕ} [NeZero p] (hp : 5 ≤ p)
    (F : Fin p → M) :
    ∑ j, F j = F 0 + F 1 + F ((p - 1 : ℕ) : Fin p) + F 2 + F ((p - 2 : ℕ) : Fin p) +
      ∑ j ∈ singerUG_rest p, F j := by
  have m1 : (1 : Fin p) ∈ Finset.univ.erase (0 : Fin p) :=
    Finset.mem_erase.mpr ⟨(singerUG_ne_iff_val (y := 0) (Fin.val_zero p)).mpr (by
      rw [singerUG_val_one (by omega)]; omega), Finset.mem_univ _⟩
  have m2 : ((p - 1 : ℕ) : Fin p) ∈ (Finset.univ.erase (0 : Fin p)).erase 1 :=
    Finset.mem_erase.mpr ⟨(singerUG_ne_iff_val (y := 1) (singerUG_val_one (by omega))).mpr (by
      rw [singerUG_val_natCast (by omega)]; omega), Finset.mem_erase.mpr ⟨
        (singerUG_ne_iff_val (y := 0) (Fin.val_zero p)).mpr (by
          rw [singerUG_val_natCast (by omega)]; omega), Finset.mem_univ _⟩⟩
  have m3 : (2 : Fin p) ∈ (((Finset.univ.erase (0 : Fin p)).erase 1).erase
      ((p - 1 : ℕ) : Fin p)) := by
    refine Finset.mem_erase.mpr ⟨(singerUG_ne_iff_val (y := ((p - 1 : ℕ) : Fin p))
      (singerUG_val_natCast (by omega))).mpr (by rw [singerUG_val_two (by omega)]; omega),
      Finset.mem_erase.mpr ⟨(singerUG_ne_iff_val (y := 1) (singerUG_val_one (by omega))).mpr (by
        rw [singerUG_val_two (by omega)]; omega), Finset.mem_erase.mpr ⟨
          (singerUG_ne_iff_val (y := 0) (Fin.val_zero p)).mpr (by
            rw [singerUG_val_two (by omega)]; omega), Finset.mem_univ _⟩⟩⟩
  have m4 : ((p - 2 : ℕ) : Fin p) ∈ ((((Finset.univ.erase (0 : Fin p)).erase 1).erase
      ((p - 1 : ℕ) : Fin p)).erase 2) := by
    refine Finset.mem_erase.mpr ⟨(singerUG_ne_iff_val (y := 2) (singerUG_val_two (by omega))).mpr
      (by rw [singerUG_val_natCast (by omega)]; omega), Finset.mem_erase.mpr ⟨
      (singerUG_ne_iff_val (y := ((p - 1 : ℕ) : Fin p)) (singerUG_val_natCast (by omega))).mpr
        (by rw [singerUG_val_natCast (by omega)]; omega), Finset.mem_erase.mpr ⟨
        (singerUG_ne_iff_val (y := 1) (singerUG_val_one (by omega))).mpr (by
          rw [singerUG_val_natCast (by omega)]; omega), Finset.mem_erase.mpr ⟨
          (singerUG_ne_iff_val (y := 0) (Fin.val_zero p)).mpr (by
            rw [singerUG_val_natCast (by omega)]; omega), Finset.mem_univ _⟩⟩⟩⟩
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin p)),
    ← Finset.add_sum_erase _ _ m1, ← Finset.add_sum_erase _ _ m2,
    ← Finset.add_sum_erase _ _ m3, ← Finset.add_sum_erase _ _ m4]
  unfold singerUG_rest
  abel

theorem singerUG_prod_split {M : Type} [CommMonoid M] {p : ℕ} [NeZero p] (hp : 5 ≤ p)
    (F : Fin p → M) :
    ∏ j, F j = F 0 * F 1 * F ((p - 1 : ℕ) : Fin p) * F 2 * F ((p - 2 : ℕ) : Fin p) *
      ∏ j ∈ singerUG_rest p, F j := by
  have m1 : (1 : Fin p) ∈ Finset.univ.erase (0 : Fin p) :=
    Finset.mem_erase.mpr ⟨(singerUG_ne_iff_val (y := 0) (Fin.val_zero p)).mpr (by
      rw [singerUG_val_one (by omega)]; omega), Finset.mem_univ _⟩
  have m2 : ((p - 1 : ℕ) : Fin p) ∈ (Finset.univ.erase (0 : Fin p)).erase 1 :=
    Finset.mem_erase.mpr ⟨(singerUG_ne_iff_val (y := 1) (singerUG_val_one (by omega))).mpr (by
      rw [singerUG_val_natCast (by omega)]; omega), Finset.mem_erase.mpr ⟨
        (singerUG_ne_iff_val (y := 0) (Fin.val_zero p)).mpr (by
          rw [singerUG_val_natCast (by omega)]; omega), Finset.mem_univ _⟩⟩
  have m3 : (2 : Fin p) ∈ (((Finset.univ.erase (0 : Fin p)).erase 1).erase
      ((p - 1 : ℕ) : Fin p)) := by
    refine Finset.mem_erase.mpr ⟨(singerUG_ne_iff_val (y := ((p - 1 : ℕ) : Fin p))
      (singerUG_val_natCast (by omega))).mpr (by rw [singerUG_val_two (by omega)]; omega),
      Finset.mem_erase.mpr ⟨(singerUG_ne_iff_val (y := 1) (singerUG_val_one (by omega))).mpr (by
        rw [singerUG_val_two (by omega)]; omega), Finset.mem_erase.mpr ⟨
          (singerUG_ne_iff_val (y := 0) (Fin.val_zero p)).mpr (by
            rw [singerUG_val_two (by omega)]; omega), Finset.mem_univ _⟩⟩⟩
  have m4 : ((p - 2 : ℕ) : Fin p) ∈ ((((Finset.univ.erase (0 : Fin p)).erase 1).erase
      ((p - 1 : ℕ) : Fin p)).erase 2) := by
    refine Finset.mem_erase.mpr ⟨(singerUG_ne_iff_val (y := 2) (singerUG_val_two (by omega))).mpr
      (by rw [singerUG_val_natCast (by omega)]; omega), Finset.mem_erase.mpr ⟨
      (singerUG_ne_iff_val (y := ((p - 1 : ℕ) : Fin p)) (singerUG_val_natCast (by omega))).mpr
        (by rw [singerUG_val_natCast (by omega)]; omega), Finset.mem_erase.mpr ⟨
        (singerUG_ne_iff_val (y := 1) (singerUG_val_one (by omega))).mpr (by
          rw [singerUG_val_natCast (by omega)]; omega), Finset.mem_erase.mpr ⟨
          (singerUG_ne_iff_val (y := 0) (Fin.val_zero p)).mpr (by
            rw [singerUG_val_natCast (by omega)]; omega), Finset.mem_univ _⟩⟩⟩⟩
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ (0 : Fin p)),
    ← Finset.mul_prod_erase _ _ m1, ← Finset.mul_prod_erase _ _ m2,
    ← Finset.mul_prod_erase _ _ m3, ← Finset.mul_prod_erase _ _ m4]
  unfold singerUG_rest
  simp only [mul_assoc]

theorem singerUG_mid_norm (h : UnitaryFieldData ℓ f K) {p : ℕ} (j : Fin p) :
    h.norm (singerUG_mid K j) = 1 := by
  unfold singerUG_mid
  split_ifs <;> simp [UnitaryFieldData.norm]

theorem singerUG_norm_neg (h : UnitaryFieldData ℓ f K) (x : K) : h.norm (-x) = h.norm x := by
  simp [UnitaryFieldData.norm]

theorem singerUG_s_norm (h : UnitaryFieldData ℓ f K) {p : ℕ} [NeZero p] {A ρ E : K}
    (hA : h.norm A = 1) (hρ : h.norm ρ = 1) (hE : h.norm E = 1) (j : Fin p) :
    h.norm (singerUG_s K A ρ E j) = 1 := by
  unfold singerUG_s
  split_ifs
  · rw [singerU_norm_mul, norm_inv_eq, hA, hE, inv_one, mul_one]
  · rw [singerU_norm_pow, hE, one_pow]
  · rw [norm_inv_eq, hE, inv_one]
  · rw [singerUG_norm_neg, singerU_norm_pow, hE, one_pow]
  · rw [singerU_norm_mul, norm_inv_eq, hρ, hE, inv_one, mul_one]
  · exact singerUG_mid_norm h j

theorem singerUG_two_ne_zero {p : ℕ} [NeZero p] (hp : 3 ≤ p) : (2 : Fin p) ≠ 0 :=
  (singerUG_ne_iff_val (x := (2 : Fin p)) (y := 0) (Fin.val_zero p)).mpr
    (by rw [singerUG_val_two hp]; omega)

theorem singerUG_two_ne_one {p : ℕ} [NeZero p] (hp : 3 ≤ p) : (2 : Fin p) ≠ 1 :=
  (singerUG_ne_iff_val (x := (2 : Fin p)) (y := 1) (singerUG_val_one (by omega))).mpr
    (by rw [singerUG_val_two hp]; omega)

theorem singerUG_pm1_ne (p : ℕ) [NeZero p] (hp : 5 ≤ p) :
    ((p - 1 : ℕ) : Fin p) ≠ 0 ∧ ((p - 1 : ℕ) : Fin p) ≠ 1 ∧ ((p - 1 : ℕ) : Fin p) ≠ 2 := by
  refine ⟨(singerUG_ne_iff_val (y := 0) (Fin.val_zero p)).mpr ?_,
    (singerUG_ne_iff_val (y := 1) (singerUG_val_one (by omega))).mpr ?_,
    (singerUG_ne_iff_val (y := 2) (singerUG_val_two (by omega))).mpr ?_⟩ <;>
    rw [singerUG_val_natCast (by omega)] <;> omega

theorem singerUG_pm2_ne (p : ℕ) [NeZero p] (hp : 5 ≤ p) :
    ((p - 2 : ℕ) : Fin p) ≠ 0 ∧ ((p - 2 : ℕ) : Fin p) ≠ 1 ∧ ((p - 2 : ℕ) : Fin p) ≠ 2 ∧
      ((p - 2 : ℕ) : Fin p) ≠ ((p - 1 : ℕ) : Fin p) := by
  refine ⟨(singerUG_ne_iff_val (y := 0) (Fin.val_zero p)).mpr ?_,
    (singerUG_ne_iff_val (y := 1) (singerUG_val_one (by omega))).mpr ?_,
    (singerUG_ne_iff_val (y := 2) (singerUG_val_two (by omega))).mpr ?_,
    (singerUG_ne_iff_val (y := ((p - 1 : ℕ) : Fin p)) (singerUG_val_natCast (by omega))).mpr ?_⟩ <;>
    rw [singerUG_val_natCast (by omega)] <;> omega

theorem singerUG_s_zero (A ρ E : K) {p : ℕ} [NeZero p] :
    singerUG_s K A ρ E (0 : Fin p) = A * E⁻¹ := by
  unfold singerUG_s
  rw [if_pos rfl]

theorem singerUG_s_one {p : ℕ} [NeZero p] (hp : 5 ≤ p) (A ρ E : K) :
    singerUG_s K A ρ E (1 : Fin p) = E ^ 2 := by
  unfold singerUG_s
  rw [if_neg (singerUG_one_ne_zero (by omega)), if_pos rfl]

theorem singerUG_s_two {p : ℕ} [NeZero p] (hp : 5 ≤ p) (A ρ E : K) :
    singerUG_s K A ρ E (2 : Fin p) = E⁻¹ := by
  unfold singerUG_s
  rw [if_neg (singerUG_two_ne_zero (by omega)), if_neg (singerUG_two_ne_one (by omega)),
    if_pos rfl]

theorem singerUG_s_pm1 {p : ℕ} [NeZero p] (hp : 5 ≤ p) (A ρ E : K) :
    singerUG_s K A ρ E ((p - 1 : ℕ) : Fin p) = -(E ^ 2) := by
  obtain ⟨h0, h1, h2⟩ := singerUG_pm1_ne p hp
  unfold singerUG_s
  rw [if_neg h0, if_neg h1, if_neg h2, if_pos rfl]

theorem singerUG_s_pm2 {p : ℕ} [NeZero p] (hp : 5 ≤ p) (A ρ E : K) :
    singerUG_s K A ρ E ((p - 2 : ℕ) : Fin p) = ρ * E⁻¹ := by
  obtain ⟨h0, h1, h2, h3⟩ := singerUG_pm2_ne p hp
  unfold singerUG_s
  rw [if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_pos rfl]

theorem singerUG_s_rest {p : ℕ} [NeZero p] (A ρ E : K) {j : Fin p}
    (hj : j ∈ singerUG_rest p) : singerUG_s K A ρ E j = singerUG_mid K j := by
  simp only [singerUG_rest, Finset.mem_erase, Finset.mem_univ, and_true] at hj
  obtain ⟨h1, h2, h3, h4, h5⟩ := hj
  unfold singerUG_s
  rw [if_neg h5, if_neg h4, if_neg h2, if_neg h3, if_neg h1]

theorem singerUG_neg_mem_rest {p : ℕ} [NeZero p] (hp : 5 ≤ p) {j : Fin p}
    (hj : j ∈ singerUG_rest p) : -j ∈ singerUG_rest p := by
  rw [singerUG_mem_rest hp] at hj ⊢
  have hjne : j ≠ 0 := fun e => by rw [e, Fin.val_zero] at hj; omega
  have hval : ((-j : Fin p) : ℕ) = p - (j : ℕ) := by rw [Fin.val_neg, if_neg hjne]
  rw [hval]
  have hj' := j.isLt
  omega

theorem singerUG_mid_neg {p : ℕ} [NeZero p] (hodd : p % 2 = 1) (hp : 5 ≤ p) {j : Fin p}
    (hj : j ∈ singerUG_rest p) : singerUG_mid K (-j) = -singerUG_mid K j := by
  rw [singerUG_mem_rest hp] at hj
  have hjne : j ≠ 0 := fun e => by rw [e, Fin.val_zero] at hj; omega
  have hval : ((-j : Fin p) : ℕ) = p - (j : ℕ) := by rw [Fin.val_neg, if_neg hjne]
  unfold singerUG_mid
  rw [hval]
  split_ifs <;> first | (exfalso; omega) | norm_num

theorem singerUG_s_neg_rest {p : ℕ} [NeZero p] (hodd : p % 2 = 1) (hp : 5 ≤ p) (A ρ E : K)
    {j : Fin p} (hj : j ∈ singerUG_rest p) :
    singerUG_s K A ρ E (-j) = -singerUG_s K A ρ E j := by
  rw [singerUG_s_rest A ρ E (singerUG_neg_mem_rest hp hj), singerUG_s_rest A ρ E hj,
    singerUG_mid_neg hodd hp hj]

theorem singerUG_prod_s {p : ℕ} [NeZero p] (hp : 5 ≤ p) (A ρ E : K) (hE : E ≠ 0) :
    ∏ j : Fin p, singerUG_s K A ρ E j =
      -(A * ρ * E) * ∏ j ∈ singerUG_rest p, singerUG_mid K j := by
  rw [singerUG_prod_split hp]
  simp only [singerUG_s_zero, singerUG_s_one hp, singerUG_s_two hp, singerUG_s_pm1 hp,
    singerUG_s_pm2 hp]
  rw [Finset.prod_congr rfl (fun j hj => singerUG_s_rest A ρ E hj)]
  field_simp

theorem singerUG_mulVec_single0 {p : ℕ} [NeZero p] (M : Matrix (Fin p) (Fin p) K) (j : Fin p) :
    (M *ᵥ Pi.single 0 1) j = M j 0 := by
  rw [mulVec_single_one, col_apply]

theorem singerUG_zero_sub_two {p : ℕ} [NeZero p] (hp : 3 ≤ p) :
    (0 : Fin p) - 2 = ((p - 2 : ℕ) : Fin p) := by
  apply Fin.ext
  rw [Fin.val_sub, singerUG_val_two hp, Fin.val_zero, singerUG_val_natCast (by omega), add_zero,
    Nat.mod_eq_of_lt (by omega)]

theorem singerUG_w0_decomp {p : ℕ} [NeZero p] (hodd : p % 2 = 1) (hp : 5 ≤ p) {c : K}
    {b : Matrix (Fin p) (Fin p) K} (hb : b * companionMat p c = companionMat p c * b)
    (s : Fin p → K) (hs : ∀ j ∈ singerUG_rest p, s (-j) = -s j) :
    ((b * diagonal s * b) *ᵥ Pi.single 0 1) 0 =
      b 0 0 * b 0 0 * s 0 + b 0 1 * b 1 0 * (s 1 + s ((p - 1 : ℕ) : Fin p)) +
        b 0 2 * b 2 0 * (s 2 + s ((p - 2 : ℕ) : Fin p)) := by
  have hpair : ∀ j : Fin p, b 0 (-j) * b (-j) 0 = b 0 j * b j 0 := by
    intro j
    have := thmU_pairing_symm c hb 0 j
    simp only [singerUG_mulVec_single0, zero_sub] at this
    exact this.symm
  have hz : ∀ j : Fin p, j ∈ singerUG_rest p →
      b 0 j * b j 0 * s j + b 0 (-j) * b (-j) 0 * s (-j) = 0 := by
    intro j hj
    rw [hpair j, hs j hj]
    ring
  have hne : ∀ j : Fin p, j ∈ singerUG_rest p → -j ≠ j := by
    intro j hj e
    rw [singerUG_mem_rest (by omega)] at hj
    have hjne : j ≠ 0 := fun e0 => by rw [e0, Fin.val_zero] at hj; omega
    have hval : ((-j : Fin p) : ℕ) = p - (j : ℕ) := by rw [Fin.val_neg, if_neg hjne]
    have := congrArg Fin.val e
    rw [hval] at this
    omega
  have hrest : ∑ j ∈ singerUG_rest p, b 0 j * b j 0 * s j = 0 := by
    apply Finset.sum_involution (fun j _ => -j)
    · intro a ha
      exact hz a ha
    · intro a ha _
      exact hne a ha
    · intro a _
      exact neg_neg a
    · intro a ha
      exact singerUG_neg_mem_rest hp ha
  have hG1 : b 0 ((p - 1 : ℕ) : Fin p) * b ((p - 1 : ℕ) : Fin p) 0 = b 0 1 * b 1 0 := by
    have e1 : (-1 : Fin p) = ((p - 1 : ℕ) : Fin p) :=
      (zero_sub (1 : Fin p)).symm.trans (singerUG_zero_sub_one (by omega))
    have := hpair 1
    rw [e1] at this
    exact this
  have hG2 : b 0 ((p - 2 : ℕ) : Fin p) * b ((p - 2 : ℕ) : Fin p) 0 = b 0 2 * b 2 0 := by
    have e2 : (-2 : Fin p) = ((p - 2 : ℕ) : Fin p) :=
      (zero_sub (2 : Fin p)).symm.trans (singerUG_zero_sub_two (by omega))
    have := hpair 2
    rw [e2] at this
    exact this
  rw [thmU_pairing_apply]
  simp only [singerUG_mulVec_single0]
  have hsplit := singerUG_sum_split hp (fun j => b 0 j * b j 0 * s j)
  rw [hsplit, hrest, hG1, hG2]
  ring

theorem singerUG_w0_zero (h : UnitaryFieldData ℓ f K) {p : ℕ} [NeZero p] (hodd : Odd p)
    (hp : 5 ≤ p) {c ε : K} (hc : c ≠ 0) (hE : h.bar ε ^ p + c ≠ 0)
    (hb : thmU_cayleyMat h p c ε * companionMat p c = companionMat p c * thmU_cayleyMat h p c ε)
    {A ρ E : K} (hA : c * A = h.bar ε ^ p * (1 + ρ)) :
    ((thmU_cayleyMat h p c ε * diagonal (singerUG_s K A ρ E) * thmU_cayleyMat h p c ε) *ᵥ
      Pi.single 0 1) 0 = 0 := by
  have hodd' : p % 2 = 1 := Nat.odd_iff.mp hodd
  have hp3 : 3 ≤ p := by omega
  rw [singerUG_w0_decomp hodd' hp hb (singerUG_s K A ρ E)
    (fun j hj => singerUG_s_neg_rest hodd' hp A ρ E hj)]
  rw [singerUG_s_zero, singerUG_s_one hp, singerUG_s_two hp, singerUG_s_pm1 hp,
    singerUG_s_pm2 hp]
  have hb02 : thmU_cayleyMat h p c ε 0 2 =
      c * thmU_cayleyMat h p c ε ((p - 2 : ℕ) : Fin p) 0 := by
    rw [thmU_commute_companion_entry c hb 0 2,
      if_neg (show ¬ (((2 : Fin p) : ℕ) ≤ ((0 : Fin p) : ℕ)) by
        rw [singerUG_val_two hp3, Fin.val_zero]; omega),
      singerUG_mulVec_single0, singerUG_zero_sub_two hp3]
  have hb00 : thmU_cayleyMat h p c ε 0 0 = c * (1 - h.bar ε * ε) / (h.bar ε ^ p + c) :=
    singerUG_beta_zero h hodd hp3 hc hE
  have hb2 : thmU_cayleyMat h p c ε (2 : Fin p) 0 =
      (-1) ^ (2 - 1) * h.bar ε ^ (p - 2) * (1 - h.bar ε * ε) / (h.bar ε ^ p + c) :=
    singerUG_beta_natCast h hodd hp3 hc hE (k := 2) (by norm_num) (by omega)
  have hbp : thmU_cayleyMat h p c ε ((p - 2 : ℕ) : Fin p) 0 =
      (-1) ^ (p - 2 - 1) * h.bar ε ^ (p - (p - 2)) * (1 - h.bar ε * ε) /
        (h.bar ε ^ p + c) :=
    singerUG_beta_natCast h hodd hp3 hc hE (k := p - 2) (by omega) (by omega)
  have e1 : (-1 : K) ^ (2 - 1) = -1 := by norm_num
  have e2 : (-1 : K) ^ (p - 2 - 1) = 1 :=
    (Nat.even_iff.mpr (by omega : (p - 2 - 1) % 2 = 0)).neg_one_pow
  have e3 : p - (p - 2) = 2 := by omega
  have e4 : h.bar ε ^ (p - 2) * h.bar ε ^ 2 = h.bar ε ^ p := by
    rw [← pow_add]
    congr 1
    omega
  rw [hb02, hb00, hb2, hbp, e1, e2, e3]
  linear_combination (c * ((1 - h.bar ε * ε) / (h.bar ε ^ p + c)) ^ 2 * (E⁻¹)) * hA -
    (c * ((1 - h.bar ε * ε) / (h.bar ε ^ p + c)) ^ 2 * (E⁻¹) * (1 + ρ)) * e4

theorem singerUG_diag_unit (h : UnitaryFieldData ℓ f K) {p : ℕ} (t : Fin p → K)
    (ht : ∀ j, h.norm (t j) = 1) : ((diagonal t).map h.bar)ᵀ * diagonal t = 1 := by
  rw [Matrix.diagonal_map (map_zero h.bar), Matrix.diagonal_transpose,
    Matrix.diagonal_mul_diagonal]
  have hfun : (fun j => h.bar (t j) * t j) = (1 : Fin p → K) := by
    funext j
    rw [Pi.one_apply, mul_comm]
    exact ht j
  rw [hfun]
  exact Matrix.diagonal_one

theorem singerUG_prod_mid_norm (h : UnitaryFieldData ℓ f K) {p : ℕ} [NeZero p] :
    h.norm (∏ j ∈ singerUG_rest p, singerUG_mid K j) = 1 :=
  Finset.prod_induction (singerUG_mid K) (fun x => h.norm x = 1)
    (fun a b ha hb => by rw [singerU_norm_mul, ha, hb, mul_one])
    (by simp [UnitaryFieldData.norm])
    (fun x _ => singerUG_mid_norm h x)

theorem singerUG_A_exists (h : UnitaryFieldData ℓ f K) {p : ℕ} {c ε ρ n : K}
    (hc0 : c ≠ 0) (hcn : h.norm c = 1) (hεn : h.norm ε = n) (hn0 : n ≠ 0)
    (hinv : n⁻¹ ^ p = h.norm (1 + ρ)) :
    ∃ A : K, c * A = h.bar ε ^ p * (1 + ρ) ∧ h.norm A = 1 := by
  refine ⟨h.bar ε ^ p * (1 + ρ) / c, by field_simp, ?_⟩
  rw [div_eq_mul_inv, singerU_norm_mul, singerU_norm_mul, singerU_norm_pow, norm_inv_eq, hcn,
    inv_one, mul_one]
  have hbar : h.norm (h.bar ε) = n := by
    rw [← hεn]
    simp [UnitaryFieldData.norm, h.bar_bar, mul_comm]
  rw [hbar, ← hinv, ← mul_pow, mul_inv_cancel₀ hn0, one_pow]

theorem singerUG_E_norm (h : UnitaryFieldData ℓ f K) {A ρ M : K} (hA : h.norm A = 1)
    (hρ : h.norm ρ = 1) (hM : h.norm M = 1) : h.norm (-(A * ρ * M)⁻¹) = 1 := by
  rw [singerUG_norm_neg, norm_inv_eq, singerU_norm_mul, singerU_norm_mul, hA, hρ, hM]
  simp

theorem singerUG_prod_one {p : ℕ} [NeZero p] (hp : 5 ≤ p) (A ρ M : K) (hX : A * ρ * M ≠ 0)
    (hM : M = ∏ j ∈ singerUG_rest p, singerUG_mid K j) :
    ∏ j : Fin p, singerUG_s K A ρ (-(A * ρ * M)⁻¹) j = 1 := by
  have hE : -(A * ρ * M)⁻¹ ≠ 0 := neg_ne_zero.mpr (inv_ne_zero hX)
  rw [singerUG_prod_s hp A ρ _ hE, ← hM]
  calc -(A * ρ * -(A * ρ * M)⁻¹) * M = (A * ρ * M) * (A * ρ * M)⁻¹ := by ring
    _ = 1 := mul_inv_cancel₀ hX

theorem singerUG_conj_entry (h : UnitaryFieldData ℓ f K) {p : ℕ} [NeZero p]
    (Y : Matrix (Fin p) (Fin p) K) (hY : (Y.map h.bar)ᵀ * Y = 1) (κ σ : K) (i j : Fin p) :
    ((Y * diagonal (fun k => κ * (if k = 0 then σ else 1)) * (Y.map h.bar)ᵀ :
      Matrix (Fin p) (Fin p) K)) i j =
      κ * (1 : Matrix (Fin p) (Fin p) K) i j + κ * (σ - 1) * Y i 0 * h.bar (Y j 0) := by
  have hYY : Y * (Y.map h.bar)ᵀ = 1 := mul_eq_one_comm.mp hY
  set u : Fin p → K := fun k => if k = 0 then κ * (σ - 1) else 0 with hu
  have hsplit : diagonal (fun k => κ * (if k = 0 then σ else 1)) =
      κ • (1 : Matrix (Fin p) (Fin p) K) + diagonal u := by
    ext a b
    by_cases hab : a = b
    · subst hab
      by_cases ha : a = 0
      · simp [u, ha]
        ring
      · simp [u, ha]
    · simp [Matrix.diagonal_apply_ne _ hab, Matrix.one_apply_ne hab]
  have hterm : (Y * diagonal u * (Y.map h.bar)ᵀ) i j = Y i 0 * u 0 * (Y.map h.bar)ᵀ 0 j := by
    rw [Matrix.mul_apply, Finset.sum_eq_single (0 : Fin p)]
    · simp [Matrix.mul_diagonal]
    · intro k _ hk
      simp [Matrix.mul_diagonal, u, hk]
    · intro h0
      exact absurd (Finset.mem_univ _) h0
  rw [hsplit, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
    hYY, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, hterm]
  have hu0 : u 0 = κ * (σ - 1) := by simp [u]
  have hH : (Y.map h.bar)ᵀ 0 j = h.bar (Y j 0) := by
    simp [Matrix.transpose_apply, Matrix.map_apply]
  rw [hu0, hH]
  ring

theorem singerUG_Y_unit (h : UnitaryFieldData ℓ f K) {p : ℕ} [NeZero p]
    (b : Matrix (Fin p) (Fin p) K) (hb : (b.map h.bar)ᵀ * b = 1) (s : Fin p → K)
    (hs : ∀ j, h.norm (s j) = 1) :
    ((b * diagonal s * b).map h.bar)ᵀ * (b * diagonal s * b) = 1 := by
  have hD := singerUG_diag_unit h s hs
  have key : ((b * diagonal s * b).map h.bar)ᵀ =
      (b.map h.bar)ᵀ * ((diagonal s).map h.bar)ᵀ * (b.map h.bar)ᵀ := by
    simp only [Matrix.map_mul, Matrix.transpose_mul, Matrix.mul_assoc]
  rw [key]
  calc (b.map h.bar)ᵀ * ((diagonal s).map h.bar)ᵀ * (b.map h.bar)ᵀ * (b * diagonal s * b)
      = (b.map h.bar)ᵀ * ((diagonal s).map h.bar)ᵀ * ((b.map h.bar)ᵀ * b) * diagonal s * b := by
        simp only [Matrix.mul_assoc]
    _ = (b.map h.bar)ᵀ * ((diagonal s).map h.bar)ᵀ * diagonal s * b := by
        rw [hb, Matrix.mul_one]
    _ = (b.map h.bar)ᵀ * (((diagonal s).map h.bar)ᵀ * diagonal s) * b := by
        simp only [Matrix.mul_assoc]
    _ = (b.map h.bar)ᵀ * b := by rw [hD, Matrix.mul_one]
    _ = 1 := hb

theorem singerUG_fixer_entries (h : UnitaryFieldData ℓ f K) {p : ℕ} [NeZero p]
    (Y : Matrix (Fin p) (Fin p) K) (hY : (Y.map h.bar)ᵀ * Y = 1) (κ σ : K) (hκ : κ ≠ 0)
    (hσ : σ - 1 ≠ 0) (hY00 : Y 0 0 = 0) {a b' c' : Fin p} (hab : b' ≠ a) (hac : c' ≠ a)
    (hbc : b' ≠ c') (hb' : Y b' 0 ≠ 0) (hc' : Y c' 0 ≠ 0) (ha : Y a 0 ≠ 0) :
    (∀ i, i ≠ 0 → (Y * diagonal (fun k => κ * (if k = 0 then σ else 1)) *
      (Y.map h.bar)ᵀ : Matrix (Fin p) (Fin p) K) i 0 = 0) ∧
    ¬ IsMonomialMat (Y * diagonal (fun k => κ * (if k = 0 then σ else 1)) * (Y.map h.bar)ᵀ) := by
  refine ⟨fun i hi => ?_, fun hmon => ?_⟩
  · rw [singerUG_conj_entry h Y hY κ σ, Matrix.one_apply_ne hi, hY00, map_zero]
    ring
  · have h1 : ((Y * diagonal (fun k => κ * (if k = 0 then σ else 1)) *
        (Y.map h.bar)ᵀ : Matrix (Fin p) (Fin p) K)) b' a ≠ 0 := by
      rw [singerUG_conj_entry h Y hY κ σ, Matrix.one_apply_ne hab, mul_zero, zero_add]
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero hκ hσ) hb') ((map_ne_zero h.bar).mpr ha)
    have h2 : ((Y * diagonal (fun k => κ * (if k = 0 then σ else 1)) *
        (Y.map h.bar)ᵀ : Matrix (Fin p) (Fin p) K)) c' a ≠ 0 := by
      rw [singerUG_conj_entry h Y hY κ σ, Matrix.one_apply_ne hac, mul_zero, zero_add]
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero hκ hσ) hc') ((map_ne_zero h.bar).mpr ha)
    exact hbc (hmon a b' c' h1 h2)

theorem singerUG_unit_exists (h : UnitaryFieldData ℓ f K) {p : ℕ} [NeZero p]
    (M : Matrix (Fin p) (Fin p) K) (hM : (M.map h.bar)ᵀ * M = 1) :
    ∃ G : GL (Fin p) K, (G : Matrix (Fin p) (Fin p) K) = M ∧
      ((G⁻¹ : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) = (M.map h.bar)ᵀ :=
  ⟨⟨M, (M.map h.bar)ᵀ, mul_eq_one_comm.mp hM, hM⟩, rfl, rfl⟩

theorem singerUG_prod_t {p : ℕ} [NeZero p] (κ σ : K) :
    ∏ j : Fin p, κ * (if j = 0 then σ else 1) = κ ^ p * σ := by
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1
  simp [Finset.prod_ite_eq']

theorem exists_outer_fixer_generic (h : UnitaryFieldData ℓ f K) {p : ℕ} [Fact p.Prime]
    (hp : 5 ≤ p) (hpq : p ∣ ℓ ^ f + 1) (hne : ℓ ^ f + 1 ≠ p) {c : K} (hcu : h.bar c * c = 1)
    (hc : ¬ ∃ μ : K, μ ^ p = c) (H : Subgroup (GL (Fin p) K))
    (hT : ∀ g ∈ unitarySU ℓ f K p, (∃ t, (g : Matrix (Fin p) (Fin p) K) = diagonal t) → g ∈ H)
    (hL : ∀ g ∈ unitarySU ℓ f K p,
      (g : Matrix (Fin p) (Fin p) K) * companionMat p c = companionMat p c * g → g ∈ H) :
    ∃ g ∈ H, (∀ i, i ≠ 0 → (g : Matrix (Fin p) (Fin p) K) i 0 = 0) ∧
      ¬ IsMonomialMat (g : Matrix (Fin p) (Fin p) K) := by
  have hprime : p.Prime := Fact.out
  have hodd : Odd p := hprime.odd_of_ne_two (by omega)
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hc ⟨0, zero_pow (by omega)⟩
  have hcn : h.norm c = 1 := by
    rw [UnitaryFieldData.norm, mul_comm]
    exact hcu
  have hq10 : 10 ≤ ℓ ^ f + 1 := by
    obtain ⟨k, hk⟩ := hpq
    have hk0 : k ≠ 0 := by
      rintro rfl
      simp at hk
    have hk1 : k ≠ 1 := by
      rintro rfl
      exact hne (by simpa using hk)
    calc 10 ≤ p * 2 := by omega
      _ ≤ p * k := Nat.mul_le_mul_left p (by omega)
      _ = ℓ ^ f + 1 := hk.symm
  obtain ⟨ρ, hρ, hρ1, hρ2, hρ3⟩ := singerU_exists_norm_one_good h hq10
  have hρ1' : 1 + ρ ≠ 0 := fun e => hρ1 (by rw [e]; simp [UnitaryFieldData.norm])
  have hρ0 : ρ ≠ 0 := fun e => by
    rw [e] at hρ
    simp [UnitaryFieldData.norm] at hρ
  obtain ⟨n, hnfix, hn0, hnM⟩ := (singerU_exists_unique_inv_pow h Fact.out hp hpq
    (singerU_norm_fixed h (1 + ρ)) hρ1).exists
  obtain ⟨hn1, hn2⟩ := singerU_ne_one_neg_one_of_inv_pow Fact.out hp hρ2 hρ3 hnM
  obtain ⟨ε, hε0, hεn⟩ := singerU_exists_norm_eq_of_fixed h hnfix hn0
  have hn1' : h.norm ε ≠ 1 := by
    rw [hεn]
    exact hn1
  have hn2' : h.norm ε ≠ -1 := by
    rw [hεn]
    exact hn2
  have hEc : c + h.bar ε ^ p ≠ 0 := thmU_add_pow_ne h hodd hc ε
  have hE : h.bar ε ^ p + c ≠ 0 := by
    rw [add_comm]
    exact hEc
  obtain ⟨A, hA, hAn⟩ := singerUG_A_exists h hc0 hcn hεn hn0 hnM
  have hA0 : A ≠ 0 := fun e => by
    rw [e] at hAn
    simp [UnitaryFieldData.norm] at hAn
  obtain ⟨M, hMdef⟩ : ∃ M : K, M = ∏ j ∈ singerUG_rest p, singerUG_mid K j := ⟨_, rfl⟩
  have hMn : h.norm M = 1 := by
    rw [hMdef]
    exact singerUG_prod_mid_norm h
  have hM0 : M ≠ 0 := fun e => by
    rw [e] at hMn
    simp [UnitaryFieldData.norm] at hMn
  have hX : A * ρ * M ≠ 0 := mul_ne_zero (mul_ne_zero hA0 hρ0) hM0
  obtain ⟨E, hEdef⟩ : ∃ E : K, E = -(A * ρ * M)⁻¹ := ⟨_, rfl⟩
  have hEn : h.norm E = 1 := by
    rw [hEdef]
    exact singerUG_E_norm h hAn hρ hMn
  have hE0 : E ≠ 0 := by
    rw [hEdef]
    exact neg_ne_zero.mpr (inv_ne_zero hX)
  have hdet : ∏ j : Fin p, singerUG_s K A ρ E j = 1 := by
    rw [hEdef]
    exact singerUG_prod_one hp A ρ M hX hMdef
  have hs : ∀ j : Fin p, h.norm (singerUG_s K A ρ E j) = 1 := fun j => singerUG_s_norm h hAn hρ hEn j
  have hbC : thmU_cayleyMat h p c ε * companionMat p c =
      companionMat p c * thmU_cayleyMat h p c ε :=
    ((thmU_cayley_commute h ε hodd hc0 hEc).eq).symm
  have hw0 : ((thmU_cayleyMat h p c ε * diagonal (singerUG_s K A ρ E) *
      thmU_cayleyMat h p c ε) *ᵥ Pi.single 0 1) 0 = 0 :=
    singerUG_w0_zero h hodd hp hc0 hE hbC hA
  have hbunit : ((thmU_cayleyMat h p c ε).map h.bar)ᵀ * thmU_cayleyMat h p c ε = 1 :=
    thmU_cayley_unitary h ε hodd hcu hc0 hEc
  obtain ⟨Y, hYdef⟩ : ∃ Y : Matrix (Fin p) (Fin p) K,
      Y = thmU_cayleyMat h p c ε * diagonal (singerUG_s K A ρ E) * thmU_cayleyMat h p c ε :=
    ⟨_, rfl⟩
  have hYU : (Y.map h.bar)ᵀ * Y = 1 := by
    rw [hYdef]
    exact singerUG_Y_unit h _ hbunit _ hs
  have hY00 : Y 0 0 = 0 := by
    rw [← singerUG_mulVec_single0 Y 0, hYdef]
    exact hw0
  obtain ⟨w, hwdef⟩ : ∃ w : Fin p → K, w = thmU_cayleyMat h p c ε *ᵥ
      (fun k => singerUG_s K A ρ E k * thmU_cayleyMat h p c ε k 0) := ⟨_, rfl⟩
  have hwY : Y *ᵥ Pi.single 0 1 = w := by
    rw [hwdef, hYdef, ← mulVec_mulVec, ← mulVec_mulVec]
    congr 1
    funext k
    rw [mulVec_diagonal, singerUG_mulVec_single0]
  have hwi : ∀ i, w i = Y i 0 := by
    intro i
    rw [← hwY, singerUG_mulVec_single0]
  have hw0' : w 0 = 0 := by
    rw [hwi 0, hY00]
  have hsum : p = 5 → singerUG_s K A ρ E ((2 : ℕ) : Fin p) +
      singerUG_s K A ρ E ((3 : ℕ) : Fin p) ≠ 0 := by
    intro hp5
    have h2 : singerUG_s K A ρ E ((2 : ℕ) : Fin p) = E⁻¹ := singerUG_s_two hp A ρ E
    have h3 : singerUG_s K A ρ E ((3 : ℕ) : Fin p) = ρ * E⁻¹ := by
      have e : ((3 : ℕ) : Fin p) = ((p - 2 : ℕ) : Fin p) := by
        rw [show p - 2 = 3 by omega]
      rw [e]
      exact singerUG_s_pm2 hp A ρ E
    rw [h2, h3]
    have e' : E⁻¹ + ρ * E⁻¹ = (1 + ρ) * E⁻¹ := by ring
    rw [e']
    exact mul_ne_zero hρ1' (inv_ne_zero hE0)
  obtain ⟨a, b', c', hab, hac, hbc, hwa, hwb, hwc⟩ :=
    singerUG_three_coords h hodd hp hc0 hE hε0 hn1' hn2' hs
      (v := fun k => singerUG_s K A ρ E k * thmU_cayleyMat h p c ε k 0) (fun k => rfl) hwdef
      hw0' hsum
  have hwa' : Y a 0 ≠ 0 := by
    rw [← hwi a]
    exact hwa
  have hwb' : Y b' 0 ≠ 0 := by
    rw [← hwi b']
    exact hwb
  have hwc' : Y c' 0 ≠ 0 := by
    rw [← hwi c']
    exact hwc
  obtain ⟨κ, hκn, hκp⟩ := singerU_exists_norm_one_pow_ne_one h Fact.out hpq hne
  have hκ0 : κ ≠ 0 := fun e => by
    rw [e] at hκn
    simp [UnitaryFieldData.norm] at hκn
  obtain ⟨σ, hσdef⟩ : ∃ σ : K, σ = (κ ^ p)⁻¹ := ⟨_, rfl⟩
  have hσ1 : σ - 1 ≠ 0 := by
    intro e
    have h1 : (κ ^ p)⁻¹ = 1 := by
      rw [hσdef] at e
      linear_combination e
    exact hκp (inv_eq_one.mp h1)
  have hσn : h.norm σ = 1 := by
    rw [hσdef, norm_inv_eq, singerU_norm_pow, hκn, one_pow, inv_one]
  have htn : ∀ j : Fin p, h.norm (κ * (if j = 0 then σ else 1)) = 1 := by
    intro j
    split_ifs
    · rw [singerU_norm_mul, hκn, hσn, one_mul]
    · rw [singerU_norm_mul, hκn]
      simp [UnitaryFieldData.norm]
  have hdetZ : (diagonal (fun k : Fin p => κ * (if k = 0 then σ else 1))).det = 1 := by
    rw [Matrix.det_diagonal, singerUG_prod_t, hσdef, mul_inv_cancel₀ (pow_ne_zero p hκ0)]
  obtain ⟨bG, hbG, -⟩ := singerUG_unit_exists h (thmU_cayleyMat h p c ε) hbunit
  obtain ⟨sG, hsG, -⟩ :=
    singerUG_unit_exists h (diagonal (singerUG_s K A ρ E)) (singerUG_diag_unit h _ hs)
  obtain ⟨zG, hzG, -⟩ := singerUG_unit_exists h
    (diagonal (fun k : Fin p => κ * (if k = 0 then σ else 1))) (singerUG_diag_unit h _ htn)
  obtain ⟨cG, hcG, -⟩ :=
    singerUG_unit_exists h (companionMat p c) (thmU_companionMat_unitary h hcu)
  have hsGmem : sG ∈ unitarySU ℓ f K p := (mem_unitarySU_iff h).mpr
    ⟨by rw [hsG, Matrix.det_diagonal, hdet], by rw [hsG]; exact singerUG_diag_unit h _ hs⟩
  have hzGmem : zG ∈ unitarySU ℓ f K p := (mem_unitarySU_iff h).mpr
    ⟨by rw [hzG]; exact hdetZ, by rw [hzG]; exact singerUG_diag_unit h _ htn⟩
  have hbGmem : ((bG : Matrix (Fin p) (Fin p) K).map h.bar)ᵀ * (bG : Matrix (Fin p) (Fin p) K) =
      1 := by
    rw [hbG]
    exact hbunit
  have hbGC : (bG : Matrix (Fin p) (Fin p) K) * companionMat p c =
      companionMat p c * (bG : Matrix (Fin p) (Fin p) K) := by
    rw [hbG]
    exact hbC
  obtain ⟨-, hmem⟩ := thmU_sq_conj_mem h hodd hcu hc H hT hL cG hcG bG hbGmem hbGC sG hsGmem
    ⟨_, hsG⟩ zG hzGmem ⟨_, hzG⟩
  have hinvY : (((bG * sG * bG)⁻¹ : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) =
      (Y.map h.bar)ᵀ := by
    rw [Matrix.coe_units_inv, Units.val_mul, Units.val_mul, hbG, hsG, ← hYdef]
    exact inv_eq_left_inv hYU
  have hgmat : ((bG * sG * bG * zG * (bG * sG * bG)⁻¹ : GL (Fin p) K) :
      Matrix (Fin p) (Fin p) K) =
      Y * diagonal (fun k : Fin p => κ * (if k = 0 then σ else 1)) * (Y.map h.bar)ᵀ := by
    rw [Units.val_mul, Units.val_mul, Units.val_mul, Units.val_mul, hinvY, hbG, hsG, hzG,
      hYdef]
  obtain ⟨hcol, hnm⟩ := singerUG_fixer_entries h Y hYU κ σ hκ0 hσ1 hY00 (Ne.symm hab)
    (Ne.symm hac) hbc hwb' hwc' hwa'
  refine ⟨_, hmem, ?_, ?_⟩
  · intro i hi
    rw [hgmat]
    exact hcol i hi
  · rw [hgmat]
    exact hnm

end CFSG.LieType.SeitzGeneration
