module

public import CFSG.GH74.Generic.BProg.B3.S3Ctx29wDefs
public import CFSG.GH74.Generic.BProg.B3.S3Ctx29Layer
public import CFSG.GH74.Generic.BProg.B3.S3Sec29A
public import CFSG.GH74.Generic.BProg.B3.S3Ctx29

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.LocalCores CFSG.ClassicalInvolution.Balance Subgroup
  CFSG.ABGLocalTools
open scoped commutatorElement

theorem Ctx29w.exists_E {G : Type} [Group G] [Finite G] {x y b : G} {K A B Q D J : Subgroup G}
    (h : Ctx29w G x K A B Q y b D J) :
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

theorem Ctx29w.B_decomp {G : Type} [Group G] [Finite G] {x y b : G}
    {K A B Q D J E : Subgroup G} (h : Ctx29w G x K A B Q y b D J)
    (hE : E ≤ K ∧ A = E ⊔ zpowers x ∧ CFSG.IsElementaryAbelian 2 ↥E ∧ Nat.card ↥E = 4) :
    x ∈ B ⊓ cSec K ∧ B = E ⊔ (B ⊓ cSec K) ∧ E ⊓ (B ⊓ cSec K) = ⊥ ∧
      pRank 2 ↥(B ⊓ cSec K) = 2 := by
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
  have hB0el : CFSG.IsElementaryAbelian 2 ↥(B ⊓ cSec K) :=
    Th2Sig6.isElementaryAbelian_of_le hBel inf_le_left
  have hcard : Nat.card ↥(B ⊓ cSec K) = 2 ^ 2 := by
    have h1 := S3Theta52.card_sup_of_commute hcomm hEB0
    rw [← hBsup, hBcard, hE4] at h1
    omega
  refine ⟨hxB0, hBsup, hEB0, ?_⟩
  have := hB0el
  exact CFSG.pRank_eq_of_card_eq_pow one_lt_two hcard

theorem Ctx29w.rank_Q {G : Type} [Group G] [Finite G] {x y b : G} {K A B Q D J : Subgroup G}
    (h : Ctx29w G x K A B Q y b D J) : pRank 2 ↥Q = 2 := by
  obtain ⟨E, hEK, hAE, -, hEel, hE4, -⟩ := h.exists_E
  obtain ⟨-, -, -, hB0r⟩ := h.B_decomp ⟨hEK, hAE, hEel, hE4⟩
  apply le_antisymm
  · exact (C3.Layer1.Back.pRank_mono' h.Q_syl.le).trans h.C_rank.le
  · have := C3.Layer1.Back.pRank_mono' h.B0_le_Q
    omega

theorem Ctx29w.layer {G : Type} [Group G] [Finite G] (hK : K26 G) {x y b : G}
    {K A B Q D J : Subgroup G} (h : Ctx29w G x K A B Q y b D J) :
    IsPCompIn 2 (K ⊓ centralizer ({y} : Set G)) (Ly29 K y) ∧ y ∈ Ly29 K y ∧
      HasSL2Model (↥(Ly29 K y) ⧸ pPrimeCore 2 ↥(Ly29 K y)) (fun q => Odd q ∧ 5 ≤ q) ∧
      B ⊓ cSec (Ly29 K y) = zpowers y ⊔ (B ⊓ cSec K) ∧
      2 * Nat.card ↥(B ⊓ cSec (Ly29 K y)) = Nat.card ↥B := by
  obtain ⟨E, hEK, hAE, -, hEel, hE4, hyE⟩ := h.exists_E
  have hy1 : y ≠ 1 := by
    intro h1
    have := h.y_ord
    rw [h1, orderOf_one] at this
    omega
  obtain ⟨hc1, hc2, hc3, hc4⟩ := hK x K A E y h.circ.1.2.2 h.shape.qShape3 h.src hEK hAE hyE hy1
  obtain ⟨-, hBsup, hEB0, -⟩ := h.B_decomp ⟨hEK, hAE, hEel, hE4⟩
  obtain ⟨hAB, -, -, hBel, -, -, -⟩ := h.ext
  have hEA : E ≤ A := hAE ▸ le_sup_left
  have hEB : E ≤ B := hEA.trans hAB
  have hyB : y ∈ B := hAB (Subgroup.mem_inf.1 h.y_mem).1
  have hBc : ∀ a ∈ B, ∀ c ∈ B, a * c = c * a := fun a ha c hc =>
    congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : ↥B) ⟨c, hc⟩)
  have hcomm : ∀ e ∈ E, ∀ c ∈ B ⊓ cSec K, e * c = c * e := fun e he c hc =>
    hBc e (hEB he) c (Subgroup.mem_inf.1 hc).1
  have hB0L : B ⊓ cSec K ≤ cSec (Ly29 K y) := by
    intro g hg
    obtain ⟨hgB, hgc⟩ := Subgroup.mem_inf.1 hg
    exact S3Ctx29Layer.mem_cSec_pLayerOf hgc (hBc g hgB y hyB)
  have heq : B ⊓ cSec (Ly29 K y) = zpowers y ⊔ (B ⊓ cSec K) := by
    apply le_antisymm
    · intro b hb
      obtain ⟨hbB, hbL⟩ := Subgroup.mem_inf.1 hb
      rw [hBsup] at hbB
      obtain ⟨e, he, k, hk, rfl⟩ := S3Theta52.exists_mul_of_mem_sup hcomm hbB
      have hkL : k ∈ cSec (Ly29 K y) := hB0L hk
      have heL : e ∈ cSec (Ly29 K y) := by
        have := (cSec (Ly29 K y)).mul_mem hbL ((cSec (Ly29 K y)).inv_mem hkL)
        simpa using this
      have hmem : e ∈ E ⊓ cSec (Ly29 K y) := Subgroup.mem_inf.2 ⟨he, heL⟩
      rw [hc4] at hmem
      exact mul_mem (Subgroup.mem_sup_left hmem) (Subgroup.mem_sup_right hk)
    · refine sup_le ?_ (le_inf inf_le_left hB0L)
      rw [Subgroup.zpowers_le]
      have hmem : y ∈ E ⊓ cSec (Ly29 K y) := by
        rw [hc4]
        exact Subgroup.mem_zpowers y
      exact Subgroup.mem_inf.2 ⟨hyB, (Subgroup.mem_inf.1 hmem).2⟩
  refine ⟨hc1, hc2, hc3, heq, ?_⟩
  rw [heq]
  have hy_le : zpowers y ≤ E := Subgroup.zpowers_le.2 hyE
  have hi : zpowers y ⊓ (B ⊓ cSec K) = ⊥ := by
    rw [eq_bot_iff]
    exact (inf_le_inf_right _ hy_le).trans hEB0.le
  have hc' : ∀ a ∈ zpowers y, ∀ c ∈ B ⊓ cSec K, a * c = c * a := fun a ha c hc =>
    hcomm a (hy_le ha) c hc
  have h1 := S3Theta52.card_sup_of_commute hcomm hEB0
  rw [← hBsup, hE4] at h1
  rw [S3Theta52.card_sup_of_commute hc' hi, Nat.card_zpowers, h.y_ord, h1]
  ring

theorem Ctx29w.rank_quot {G : Type} [Group G] [Finite G] {x y b : G}
    {K A B Q D J : Subgroup G} (h : Ctx29w G x K A B Q y b D J) :
    (Obs52 B b D J → 2 ^ 3 * Nat.card ↥(B ⊓ cSec J) ≤ Nat.card ↥B) ∧
    (b = y → Obs32 A y D J → 2 ^ 2 * Nat.card ↥(B ⊓ cSec J) ≤ Nat.card ↥B) := by
  obtain ⟨hAB, -, -, hBel, -, -, -⟩ := h.ext
  have hB16 : Nat.card ↥B = 16 := by
    have h2 : Nat.card ↥B = 2 ^ pRank 2 ↥B := C3.Layer1.Back.card_eq_two_pow_pRank hBel
    rw [h2, h.rankB]
    norm_num
  have hA8 : Nat.card ↥A = 8 := h.src.2.2.1
  have hA : IsE 3 ⊤ A := isE3_of_isSource2 h.src
  have hA3 : pRank 2 ↥A ≤ 3 := by
    have := h.src.2.1
    exact (CFSG.pRank_eq_of_card_eq_pow one_lt_two (by simpa using hA8) : pRank 2 ↥A = 3).le
  refine ⟨fun hobs => S3Sec29A.obs52_quot hBel hB16 hobs, fun _ hobs => ?_⟩
  have hyA : y ∈ A := (Subgroup.mem_inf.1 h.y_mem).1
  exact S3Sec29A.obs32_quot hAB hA hA8 hA3 hyA hobs

end CFSG.GH74.Generic.BProg.B3
