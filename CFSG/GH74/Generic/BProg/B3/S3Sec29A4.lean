module

public import CFSG.GH74.Generic.BProg.B3.S3Sec29A3
public import CFSG.GH74.Generic.BProg.B3.S3Sec29A2
public import CFSG.GH74.Generic.BProg.B3.S3Ctx29wFacts
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.GH74.Generic.BProg.B3.S3Sec29Defs

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.LocalCores CFSG.ClassicalInvolution.Balance Subgroup
  CFSG.ABGLocalTools CFSG.GH74.GLS.TwoThin CFSG.GH74.GLS.C3.Layer1
  CFSG.GH74.GLS.C3.Layer1.PumpCalc CFSG.ComponentClassification CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

theorem lemma295w_core {G : Type} [Group G] [Finite G] (hNo : NoL3PumpupOfA7Step G)
    {x y b : G} {K A B Q D J : Subgroup G} (h : Ctx29w G x K A B Q y b D J) :
    B ⊓ cSec K ⊓ cSec J = ⊥ := by
  classical
  by_contra hne
  obtain ⟨u, hu, hu1⟩ : ∃ u ∈ B ⊓ cSec K ⊓ cSec J, u ≠ 1 := by
    by_contra hall
    push Not at hall
    exact hne (eq_bot_iff.2 fun u hu => Subgroup.mem_bot.2 (hall u hu))
  obtain ⟨huBK, huJ⟩ := Subgroup.mem_inf.1 hu
  obtain ⟨huB, huK⟩ := Subgroup.mem_inf.1 huBK
  obtain ⟨E, hEK, hAE, hxE, hEel, hE4, hyE⟩ := h.exists_E
  obtain ⟨hxB0, hBsup, hEB0, hB0r⟩ := h.B_decomp ⟨hEK, hAE, hEel, hE4⟩
  obtain ⟨hAB, hxB, hBC, hBel, -, -, hBeq⟩ := h.ext
  obtain ⟨hBc, hBsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hBel
  obtain ⟨-, hEsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hEel
  have hu2 : orderOf u = 2 := orderOf_eq_prime (by rw [sq]; exact hBsq u huB) hu1
  have hEA : E ≤ A := hAE ▸ le_sup_left
  have hEB : E ≤ B := hEA.trans hAB
  have hB16 : Nat.card ↥B = 16 := by
    have h2 : Nat.card ↥B = 2 ^ pRank 2 ↥B := C3.Layer1.Back.card_eq_two_pow_pRank hBel
    rw [h2, h.rankB]
    norm_num
  have hB0card : Nat.card ↥(B ⊓ cSec K) = 4 := by
    have hcommE : ∀ e ∈ E, ∀ k ∈ B ⊓ cSec K, e * k = k * e := fun e he k hk =>
      hBc e (hEB he) k (Subgroup.mem_inf.1 hk).1
    have h1 := S3Theta52.card_sup_of_commute hcommE hEB0
    rw [← hBsup, hB16, hE4] at h1
    omega
  have hr4 : pRank 2 G = 4 := by
    have h1 := Gen4.pRank_two_le h.hyp.gen4
    have h2 := pRank_le_top' B
    have h3 := h.rankB
    omega
  have hKc : IsPCompIn 2 (centralizer ({x} : Set G)) K := h.circ.1.1.1.2.2
  have hterm : IsTwoTerminal x K := h.circ.1.2.2
  have hKcen : CenterlessBar K := fun a ha =>
    (B1.PilotS3.center_trivial_of_shape3 hKc h.shape.qShape3) a (fun g => (ha g).symm)
  have hux : u ∈ centralizer ({x} : Set G) :=
    mem_centralizer_singleton_iff.mpr (hBc u huB x hxB)
  have hBu : B ≤ centralizer ({u} : Set G) := fun g hg =>
    mem_centralizer_singleton_iff.mpr (hBc g hg u huB)
  have hR : 3 ≤ pRank 2 ↥(centralizer ({u} : Set G)) := by
    have := C3.Layer1.Back.pRank_mono' hBu
    have h3 := h.rankB
    omega
  obtain ⟨M, hlt, hxM, ⟨e⟩, hcenM, hKuN, ΛK, hΛK, hΛKM⟩ :=
    S3Sec29A1.exists_Ku hr4 hterm hKc hu2 hux huK hR hKcen
  have hMc : IsPCompIn 2 (centralizer ({u} : Set G)) M := hlt.2.1.2.2
  have hEM : E ≤ M := fun d hd =>
    hΛKM (hΛK.twoElt d ⟨hEK hd, mem_centralizer_singleton_iff.mpr (hBc d (hEB hd) u huB)⟩
      ⟨1, by simpa [pow_two] using hEsq d hd⟩)
  have hb2 : orderOf b = 2 := by
    rcases h.obs with ho | ⟨hby, ho, -⟩
    · exact ho.b_ord
    · rw [hby]; exact ho.y_ord
  have hJc : IsPCompIn 2 (centralizer ({b} : Set G)) J := by
    rcases h.obs with ho | ⟨hby, ho, -⟩
    · exact ho.comp
    · rw [hby]; exact ho.comp
  have hbB : b ∈ B := h.b_mem
  have hbu : u ∈ centralizer ({b} : Set G) :=
    mem_centralizer_singleton_iff.mpr (hBc u huB b hbB)
  have hub : b ∈ centralizer ({u} : Set G) := hBu hbB
  have hBb : B ≤ centralizer ({b} : Set G) := fun g hg =>
    mem_centralizer_singleton_iff.mpr (hBc g hg b hbB)
  have hRb : 3 ≤ pRank 2 ↥(centralizer ({b} : Set G)) := by
    have := C3.Layer1.Back.pRank_mono' hBb
    have h3 := h.rankB
    omega
  obtain ⟨Λ, hΛ⟩ := exists_isLam hu2 hJc huJ
  have hbM : b ∈ normalizer (M : Set G) := hKuN b hub
  have hCle : Nat.card ↥(B ⊓ cSec J) ≤ 4 := by
    rcases h.obs with ho | ⟨hby, ho, -⟩
    · have := h.rank_quot.1 ho
      rw [show (2 : ℕ) ^ 3 = 8 by norm_num, hB16] at this
      omega
    · have := h.rank_quot.2 hby ho
      rw [show (2 : ℕ) ^ 2 = 4 by norm_num, hB16] at this
      omega
  rcases S3Sec29A1.pumpup_dichotomy hb2 hub hΛ hMc with hMJ | hcomm
  ·
    have hltJ : PumpUpLT 2 b J u M :=
      ⟨⟨hb2, by simpa [oBound] using hRb, hJc⟩, hlt.2.1, hbu, huJ, hMJ⟩
    have hΛL : PumpCalc.bar u Λ ≤ PumpCalc.bar u M := bar_le_of_stable hltJ hΛ hbM
    have hB0J : B ⊓ cSec K ≤ B ⊓ cSec J := by
      intro r hr
      obtain ⟨hrB, hrK⟩ := Subgroup.mem_inf.1 hr
      refine Subgroup.mem_inf.2 ⟨hrB, ?_⟩
      have hrb : r ∈ centralizer ({b} : Set G) := hBb hrB
      have hru : r ∈ centralizer ({u} : Set G) := hBu hrB
      have hrx : r ∈ centralizer ({x} : Set G) :=
        mem_centralizer_singleton_iff.mpr (hBc r hrB x hxB)
      have hrM : r ∈ centralizerSection M (pPrimeCoreOf 2 M) :=
        S3Sec29A1.mem_cSec_Ku hKc hlt e hxM hru hrx hrK
      exact S3Sec29A3.mem_cSec_of_act_trivial hJc hΛ hrb hru
        (S3Sec29A3.act_trivial_of_cSec hMc hΛL hru hrM)
    rcases h.obs with ho | ⟨hby, ho, hDA, hA7, -⟩
    · have h1 := h.rank_quot.1 ho
      have h2 := Subgroup.card_le_of_le hB0J
      rw [show (2 : ℕ) ^ 3 = 8 by norm_num, hB16] at h1
      omega
    · exact hNo b u J M hltJ hA7 (hby ▸ hEM hyE)
        (isL3OddGt3_of_mulEquiv e.symm h.shape.qShape3)
  ·
    have hEJ : E ≤ cSec J := by
      intro d hd
      have hdB := hEB hd
      have hdb : d ∈ centralizer ({b} : Set G) := hBb hdB
      have hdu : d ∈ centralizer ({u} : Set G) := hBu hdB
      exact S3Sec29A3.mem_cSec_of_act_trivial hJc hΛ hdb hdu
        (S3Sec29A3.act_trivial_of_comm hcomm hdu (hEM hd))
    have hFJ : zpowers u ⊔ E ≤ B ⊓ cSec J :=
      sup_le (zpowers_le.2 (Subgroup.mem_inf.2 ⟨huB, huJ⟩))
        (fun d hd => Subgroup.mem_inf.2 ⟨hEB hd, hEJ hd⟩)
    have hFcard : Nat.card ↥(zpowers u ⊔ E) = 8 := by
      have hcommF : ∀ a ∈ zpowers u, ∀ c ∈ E, a * c = c * a := fun a ha c hc =>
        hBc a (zpowers_le.2 huB ha) c (hEB hc)
      have hi : zpowers u ⊓ E = ⊥ := by
        rw [eq_bot_iff]
        intro z hz
        obtain ⟨hz1, hz2⟩ := Subgroup.mem_inf.1 hz
        have hz3 : z ∈ B ⊓ cSec K := zpowers_le.2 (Subgroup.mem_inf.2 ⟨huB, huK⟩) hz1
        have : z ∈ E ⊓ (B ⊓ cSec K) := Subgroup.mem_inf.2 ⟨hz2, hz3⟩
        rw [hEB0] at this
        exact this
      rw [S3Theta52.card_sup_of_commute hcommF hi, Nat.card_zpowers, hu2, hE4]
    have := Subgroup.card_le_of_le hFJ
    omega

end CFSG.GH74.Generic.BProg.B3
