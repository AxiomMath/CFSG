module

public import CFSG.GH74.Generic.BProg.B3.S3Sec29D1
public import CFSG.GH74.Generic.BProg.B3.S3Sec29D

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.LocalCores CFSG.ClassicalInvolution.Balance Subgroup
  CFSG.ABGLocalTools
open scoped commutatorElement

namespace S3Sec29D2

variable {G : Type} [Group G] [Finite G] {x y b : G} {K A B Q D J : Subgroup G}

theorem exists_E (h : Ctx29w G x K A B Q y b D J) :
    ∃ E : Subgroup G, E ≤ K ∧ A = E ⊔ zpowers x ∧ x ∉ E ∧ CFSG.IsElementaryAbelian 2 ↥E ∧
      Nat.card ↥E = 4 ∧ y ∈ E := by
  have hx : orderOf x = 2 := h.circ.1.1.1.1
  have hK : IsPCompIn 2 (centralizer ({x} : Set G)) K := h.circ.1.1.1.2.2
  have hZ := B1.PilotS3.center_trivial_of_shape3 hK h.shape.qShape3
  obtain ⟨E, hEK, hAE, hxE, hEel, hE4⟩ := S3Theta52.exists_E_of_src h.src hZ
  have hxK : x ∉ K := B1.PilotS5.not_mem_of_center_trivial hx hK.1 hZ
  refine ⟨E, hEK, hAE, hxE, hEel, hE4, ?_⟩
  obtain ⟨hyA, hyK⟩ := Subgroup.mem_inf.1 h.y_mem
  have hc : ∀ e ∈ E, ∀ k ∈ zpowers x, e * k = k * e := by
    intro e he k hk
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
    exact (Commute.zpow_right (show Commute e x from
      Subgroup.mem_centralizer_singleton_iff.1 (hK.1 (hEK he))) n).eq
  rw [hAE] at hyA
  obtain ⟨e, he, k, hk, rfl⟩ := S3Theta52.exists_mul_of_mem_sup hc hyA
  have hkK : k ∈ K := by
    have := K.mul_mem (K.inv_mem (hEK he)) hyK
    simpa using this
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
  have hmod : x ^ (n % 2) = x ^ n := by
    have := zpow_mod_orderOf x n
    rwa [hx, Nat.cast_ofNat] at this
  rcases Int.emod_two_eq_zero_or_one n with h0 | h1
  · rw [← hmod, h0, zpow_zero, mul_one]
    exact he
  · exact absurd (by rw [← hmod, h1, zpow_one] at hkK; exact hkK) hxK

theorem B_decomp (h : Ctx29w G x K A B Q y b D J) {E : Subgroup G}
    (hE : E ≤ K ∧ A = E ⊔ zpowers x ∧ CFSG.IsElementaryAbelian 2 ↥E ∧ Nat.card ↥E = 4) :
    x ∈ B ⊓ cSec K ∧ B = E ⊔ (B ⊓ cSec K) ∧ E ⊓ (B ⊓ cSec K) = ⊥ ∧
      Nat.card ↥B = 16 ∧ Nat.card ↥(B ⊓ cSec K) = 4 := by
  obtain ⟨hEK, hAE, hEel, hE4⟩ := hE
  have hK : IsPCompIn 2 (centralizer ({x} : Set G)) K := h.circ.1.1.1.2.2
  have hZ := B1.PilotS3.center_trivial_of_shape3 hK h.shape.qShape3
  obtain ⟨hAB, hxB, hBC, hBel, -, -, hBeq⟩ := h.ext
  have hxB0 : x ∈ B ⊓ cSec K :=
    Subgroup.mem_inf.2 ⟨hxB, S3Ctx29.mem_cSec_of_le_centralizer hK.1⟩
  have hEA : E ≤ A := hAE ▸ le_sup_left
  have hEB : E ≤ B := hEA.trans hAB
  have hBsup : B = E ⊔ (B ⊓ cSec K) := by
    calc B = A ⊔ (B ⊓ cSec K) := hBeq
      _ = E ⊔ zpowers x ⊔ (B ⊓ cSec K) := by rw [← hAE]
      _ = E ⊔ (B ⊓ cSec K) := by
        rw [sup_assoc, sup_eq_right.2 (Subgroup.zpowers_le.2 hxB0)]
  have hEB0 : E ⊓ (B ⊓ cSec K) = ⊥ := by
    rw [eq_bot_iff]
    intro e he
    obtain ⟨heE, heB0⟩ := Subgroup.mem_inf.1 he
    exact Subgroup.mem_bot.2 (S3Ctx29.eq_one_of_mem_cSec hZ hEK
      (CFSG.IsElementaryAbelian.isPGroup 2 ↥E) heE (Subgroup.mem_inf.1 heB0).2)
  have hBc : ∀ a ∈ B, ∀ c ∈ B, a * c = c * a := fun a ha c hc =>
    congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : ↥B) ⟨c, hc⟩)
  have hcomm : ∀ e ∈ E, ∀ c ∈ B ⊓ cSec K, e * c = c * e := fun e he c hc =>
    hBc e (hEB he) c (Subgroup.mem_inf.1 hc).1
  have hBcard : Nat.card ↥B = 16 := by
    have h2 : Nat.card ↥B = 2 ^ pRank 2 ↥B := C3.Layer1.Back.card_eq_two_pow_pRank hBel
    rw [h2, h.rankB]
    norm_num
  have hcard : Nat.card ↥(B ⊓ cSec K) = 4 := by
    have h1 := S3Theta52.card_sup_of_commute hcomm hEB0
    rw [← hBsup, hBcard, hE4] at h1
    omega
  exact ⟨hxB0, hBsup, hEB0, hBcard, hcard⟩

theorem J_comp (h : Ctx29w G x K A B Q y y D J) : IsPCompIn 2 (centralizer ({y} : Set G)) J := by
  rcases h.obs with h1 | ⟨-, h2, -⟩
  · exact h1.comp
  · exact h2.comp

theorem B_comm (h : Ctx29w G x K A B Q y b D J) : ∀ a ∈ B, ∀ c ∈ B, a * c = c * a := by
  obtain ⟨-, -, -, hBel, -⟩ := h.ext
  exact fun a ha c hc => congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : ↥B) ⟨c, hc⟩)

theorem y_mem_B (h : Ctx29w G x K A B Q y b D J) : y ∈ B :=
  h.ext.1 (Subgroup.mem_inf.1 h.y_mem).1

theorem B_le_centralizer_y (h : Ctx29w G x K A B Q y b D J) : B ≤ centralizer ({y} : Set G) :=
  fun c hc => Subgroup.mem_centralizer_singleton_iff.2 (B_comm h c hc y (y_mem_B h))

theorem B_sq (h : Ctx29w G x K A B Q y b D J) : ∀ c ∈ B, c * c = 1 := by
  obtain ⟨-, -, -, hBel, -⟩ := h.ext
  obtain ⟨-, hsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hBel
  exact hsq

theorem y_mem_cSec_J (h : Ctx29w G x K A B Q y y D J) : y ∈ cSec J :=
  S3Ctx29.mem_cSec_of_le_centralizer (J_comp h).1

theorem obs52_of_sl2 (h : Ctx29w G x K A B Q y y D J) (hsl : HasSL2Model (↥J ⧸ pPrimeCore 2 ↥J) Odd) :
    Obs52 B y D J := by
  rcases h.obs with h1 | ⟨-, -, -, hA7, -⟩
  · exact h1
  · exact absurd (S3Sec29A1.center_kBar_eq_bot (J_comp h) (Or.inl hA7))
      (S3Sec29D.center_ne_bot_of_sl2 hsl)

theorem card_cSec_le_two (h : Ctx29w G x K A B Q y y D J) (hO : Obs52 B y D J) :
    Nat.card ↥(B ⊓ cSec J) ≤ 2 := by
  obtain ⟨E, hEK, hAE, -, hEel, hE4, -⟩ := exists_E h
  obtain ⟨-, -, -, hB16, -⟩ := B_decomp h ⟨hEK, hAE, hEel, hE4⟩
  have := S3Sec29A.obs52_quot h.ext.2.2.2.1 hB16 hO
  rw [hB16] at this
  omega

theorem eight_le_card_normalizer (h : Ctx29w G x K A B Q y y D J) (hO : Obs52 B y D J) :
    8 ≤ Nat.card ↥(B ⊓ normalizer (J : Set G)) := by
  obtain ⟨hDB, hDel, hDr⟩ := hO.D_le
  have hD4 : 4 ≤ Nat.card ↥D := by
    rw [C3.Layer1.Back.card_eq_two_pow_pRank hDel]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ pRank 2 ↥D := Nat.pow_le_pow_right (by norm_num) hDr
  have hyB := y_mem_B h
  have hyJ := y_mem_cSec_J h
  have hy2 : Nat.card ↥(zpowers y) = 2 := by rw [Nat.card_zpowers, h.y_ord]
  have hc : ∀ d ∈ D, ∀ k ∈ zpowers y, d * k = k * d := fun d hd k hk =>
    B_comm h d (hDB hd) k ((Subgroup.zpowers_le.2 hyB) hk)
  have hi : D ⊓ zpowers y = ⊥ := by
    rw [eq_bot_iff]
    intro d hd
    obtain ⟨hdD, hdy⟩ := Subgroup.mem_inf.1 hd
    by_contra hne
    exact hO.D_faith d hdD hne ((Subgroup.zpowers_le.2 hyJ) hdy)
  have hcard := S3Theta52.card_sup_of_commute hc hi
  have hle : D ⊔ zpowers y ≤ B ⊓ normalizer (J : Set G) := by
    refine sup_le (le_inf hDB hO.D_norm) ?_
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_inf.2 ⟨hyB, (y_mem_cSec_J h).1⟩
  have := Subgroup.card_le_of_le hle
  rw [hcard, hy2] at this
  omega

theorem exists_B0_mem_normalizer (h : Ctx29w G x K A B Q y y D J) (hO : Obs52 B y D J) :
    ∃ hh ∈ B ⊓ cSec K, hh ≠ 1 ∧ hh ∈ normalizer (J : Set G) := by
  obtain ⟨E, hEK, hAE, -, hEel, hE4, -⟩ := exists_E h
  obtain ⟨-, -, -, hB16, hB04⟩ := B_decomp h ⟨hEK, hAE, hEel, hE4⟩
  have h8 := eight_le_card_normalizer h hO
  have hm := S3Sec29A.card_mul_le_card_inf_mul (inf_le_left : B ⊓ cSec K ≤ B)
    (inf_le_left : B ⊓ normalizer (J : Set G) ≤ B)
  rw [hB04, hB16] at hm
  have h2 : 2 ≤ Nat.card ↥((B ⊓ normalizer (J : Set G)) ⊓ (B ⊓ cSec K)) := by
    have : 4 * 8 ≤ Nat.card ↥((B ⊓ normalizer (J : Set G)) ⊓ (B ⊓ cSec K)) * 16 :=
      le_trans (Nat.mul_le_mul_left 4 h8) hm
    omega
  by_contra hne
  push Not at hne
  have hbot : (B ⊓ normalizer (J : Set G)) ⊓ (B ⊓ cSec K) = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    obtain ⟨hgN, hgB0⟩ := Subgroup.mem_inf.1 hg
    by_contra hg1
    exact hne g hgB0 hg1 (Subgroup.mem_inf.1 hgN).2
  rw [hbot, Subgroup.card_bot] at h2
  omega

theorem exists_not_mem_normalizer (hK31e : Kg31e G) (h : Ctx29w G x K A B Q y y D J)
    (hsl : HasSL2Model (↥J ⧸ pPrimeCore 2 ↥J) Odd) : ∃ g ∈ B, g ∉ normalizer (J : Set G) := by
  have hnot := hK31e x K A B y D J h.hyp h.noAlt h.circ h.shape h.src h.ext h.rankB
    (obs52_of_sl2 h hsl) hsl
  by_contra hall
  push Not at hall
  exact hnot hall

end S3Sec29D2

end CFSG.GH74.Generic.BProg.B3
