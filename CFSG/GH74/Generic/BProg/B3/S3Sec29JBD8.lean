module

public import CFSG.GH74.Generic.BProg.B3.S3Sec29JBD7
public import CFSG.GH74.Generic.BProg.B3.S3Sec29D8

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.LocalCores CFSG.ClassicalInvolution.Balance Subgroup
  CFSG.ABGLocalTools CFSG.GH74.Generic.S45
open scoped commutatorElement

namespace S3Sec29JB

variable {G : Type} [Group G] [Finite G] {x y : G} {K A B Q D J R : Subgroup G}

theorem centralizes_diag_L (hKS : S3Sec29C.S16cKG) (h : Ctx29w G x K A B Q y y D J)
    (hO : Obs52 B y D J) {L : Subgroup G} (hBL : B ≤ normalizer (L : Set G)) (hJL : J ≤ cSec L)
    (hMu : MuPkgL K A Q y L) {z : ↥(S3.imgBar y J)}
    (hz : SL2Data ↥(S3.imgBar y J) z) {g : G} (hgB0 : g ∈ B ⊓ cSec K)
    (hgN : g ∉ normalizer (J : Set G)) {gb : CentralizerBar y} (hgb : gb = piC y g)
    (hc : S3Sec29D3.CommConj (S3.imgBar y J) gb) {e : G} (he : e ∈ A ⊓ K) :
    ∀ d ∈ (S3Sec29D3.diagHom (S3.imgBar y J) gb hc).range, piC y e * d = d * piC y e := by
  subst hgb
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJ := S3Sec29D2.J_comp h
  set JS := Jss y L with hJS
  set φ := S3Sec29D3.diagHom (S3.imgBar y J) (piC y g) hc with hφ
  have hBy := S3Sec29D2.B_le_centralizer_y h
  have hgB : g ∈ B := (Subgroup.mem_inf.1 hgB0).1
  have hgC : g ∈ centralizer ({y} : Set G) := hBy hgB
  have hgQ : g ∈ Q := h.B0_le_Q hgB0
  have hgg : g * g = 1 := S3Sec29D2.B_sq h g hgB
  have hg1 : g ≠ 1 := fun h1 => hgN (by rw [h1]; exact one_mem _)
  have hg2 : orderOf g = 2 := orderOf_eq_prime (by rw [pow_two]; exact hgg) hg1
  have hgL := hBL hgB
  obtain ⟨M, hM, h3, hyM, hAKM, hN, hFix⟩ := hMu g hgQ hg2
  have heB : e ∈ B := h.ext.1 (Subgroup.mem_inf.1 he).1
  have heC : e ∈ centralizer ({y} : Set G) := hBy heB
  have heM : e ∈ M := hAKM he
  have heg : e * g = g * e := S3Sec29D2.B_comm h e heB g hgB
  have hπg2 : piC y g * piC y g = 1 := by rw [← piC_mul y hgC hgC, hgg, piC_one]
  have hπeg : piC y e * piC y g = piC y g * piC y e := by
    rw [← piC_mul y heC hgC, ← piC_mul y hgC heC, heg]
  have hcase : piC y e ∈ normalizer ((S3.imgBar y J : Subgroup (CentralizerBar y)) :
      Set (CentralizerBar y)) ∨ piC y e * piC y g ∈ normalizer ((S3.imgBar y J :
      Subgroup (CentralizerBar y)) : Set (CentralizerBar y)) := by
    by_cases heN : e ∈ normalizer (J : Set G)
    · exact Or.inl (S3Sec29C.piC_mem_normalizer heC heN)
    · right
      rw [← piC_mul y heC hgC]
      exact S3Sec29C.piC_mem_normalizer (mul_mem heC hgC)
        (S3Sec29D8.mul_mem_normalizer_of_not h hO hgB hgN heB heN)
  have hgJS : g ∈ normalizer ((JS : Subgroup G) : Set G) :=
    S3Sec29D5.le_normalizer_Jss (T := zpowers g) (Subgroup.zpowers_le.2 hgC)
      (Subgroup.zpowers_le.2 hgL) (Subgroup.mem_zpowers g)
  have hJJS : J ≤ JS := S3Sec29D5.le_Jss hJ hJL
  have hΔX : φ.range ≤ S3.imgBar y (JS ⊓ centralizer ({g} : Set G)) := by
    rw [S3Sec29D4.imgBar_inf_centralizer hgC hgg hgJS]
    rintro _ ⟨c, rfl⟩
    refine Subgroup.mem_inf.2 ⟨?_, Subgroup.mem_centralizer_singleton_iff.2
      (S3Sec29D3.diagHom_comm hc hπg2 c)⟩
    obtain ⟨c', hc'J, hc'e⟩ := S3.mem_imgBar.1 c.2
    have hc'C : (c' : G) ∈ centralizer ({y} : Set G) := c'.2
    have hxc : g * c' * g⁻¹ ∈ JS := S3Sec29D5.conj_le_Jss hJ hJL hgC hgL ⟨c', hc'J, rfl⟩
    have hxcC : g * c' * g⁻¹ ∈ centralizer ({y} : Set G) :=
      mul_mem (mul_mem hgC hc'C) (inv_mem hgC)
    refine S3.mem_imgBar.2 ⟨⟨c' * (g * c' * g⁻¹), mul_mem hc'C hxcC⟩, mul_mem (hJJS hc'J) hxc, ?_⟩
    rw [← piC_of_mem y (mul_mem hc'C hxcC), piC_mul y hc'C hxcC, S3Sec29D4.piC_conj hgC hc'C,
      piC_of_mem y hc'C, hc'e, S3Sec29D3.diagHom_apply]
  have hq := S3Sec29D5.isQuasisimple_imgBar hJ
  obtain ⟨P, hPX, hPp, hΔP⟩ := S3Sec29D4.exists_perfect_le hΔX (S3Sec29D3.diag_perfect hc hq.1)
  have hXg : JS ⊓ centralizer ({g} : Set G) ≤ centralizer ({g} : Set G) := inf_le_right
  have hXy : JS ⊓ centralizer ({g} : Set G) ≤ centralizer ({y} : Set G) :=
    inf_le_left.trans (S3Sec29D5.Jss_le_centralizer _)
  have hXM : JS ⊓ centralizer ({g} : Set G) ≤ normalizer (M : Set G) := fun k hk =>
    hN k (Subgroup.mem_inf.2 ⟨hXg hk, hXy hk⟩)
  have hXL : S3Sec29C.FixesLayer g M y (JS ⊓ centralizer ({g} : Set G)) :=
    S3Sec29D5.FixesLayer.mono hFix (fun k hk =>
      Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨hXg hk, hXy hk⟩,
        S3Sec29D5.Jss_le_cSec _ (Subgroup.mem_inf.1 hk).1⟩)
  have hPM : P ≤ cSec M := (S3Sec29D4.le_perfectCoreOf hPX hPp).trans
    (S3Sec29C.perfectCore_le_cSec hKS hM h3 hyM h.y_ord hXg hXM hXL)
  have hPy : P ≤ centralizer ({y} : Set G) := hPX.trans hXy
  set N₀ := pPrimeCoreOf 2 M ⊓ centralizer ({y} : Set G) with hN₀
  set Nb := S3.imgBar y N₀ with hNb
  have hNodd : Odd (Nat.card ↥Nb) := by
    have h1 : Nat.card ↥Nb ∣ Nat.card ↥(N₀.subgroupOf (centralizer ({y} : Set G))) :=
      Subgroup.card_map_dvd (H := N₀.subgroupOf (centralizer ({y} : Set G))) (proj y)
    have h2 : Nat.card ↥(N₀.subgroupOf (centralizer ({y} : Set G))) = Nat.card ↥N₀ :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
    have h3' : Nat.card ↥N₀ ∣ Nat.card ↥(pPrimeCoreOf 2 M) := Subgroup.card_dvd_of_le inf_le_left
    have h4 : Odd (Nat.card ↥(pPrimeCoreOf 2 M)) := by
      have hcop : Nat.Coprime 2 (Nat.card ↥(pPrimeCoreOf 2 M)) := by
        rw [pPrimeCoreOf, Subgroup.card_map_of_injective M.subtype_injective]
        exact pPrimeCore_coprime_card
      exact Nat.coprime_two_left.mp hcop
    rw [h2] at h1
    exact Odd.of_dvd_nat h4 (h1.trans h3')
  have hΔN : ∀ d ∈ φ.range, ∀ n ∈ Nb, d * n * d⁻¹ ∈ Nb := by
    intro d hd n hn
    obtain ⟨p, hpP, hpe⟩ := S3.mem_imgBar.1 (hΔP hd)
    obtain ⟨n', hn'N, hn'e⟩ := S3.mem_imgBar.1 hn
    have hpM : (p : G) ∈ cSec M := hPM hpP
    have hpO : (p : G) ∈ normalizer (pPrimeCoreOf 2 M : Set G) := hpM.2.1
    have hn'C : (n' : G) ∈ centralizer ({y} : Set G) := n'.2
    have hpC : (p : G) ∈ centralizer ({y} : Set G) := p.2
    have hmem : (p : G) * n' * (p : G)⁻¹ ∈ N₀ := Subgroup.mem_inf.2
      ⟨(Subgroup.mem_normalizer_iff.1 hpO _).1 (Subgroup.mem_inf.1 hn'N).1,
        mul_mem (mul_mem hpC hn'C) (inv_mem hpC)⟩
    refine S3.mem_imgBar.2 ⟨p * n' * p⁻¹, hmem, ?_⟩
    rw [map_mul, map_mul, map_inv, hpe, hn'e]
  intro d hd
  have hed : piC y e * d * (piC y e)⁻¹ ∈ φ.range :=
    S3Sec29D8.normalizes_diag hc hπg2 hπeg hcase hd
  have hcomm_Δ : piC y e * d * (piC y e)⁻¹ * d⁻¹ ∈ φ.range := mul_mem hed (inv_mem hd)
  have hcomm_N : piC y e * d * (piC y e)⁻¹ * d⁻¹ ∈ Nb := by
    obtain ⟨p, hpP, hpe⟩ := S3.mem_imgBar.1 (hΔP hd)
    have hpM : (p : G) ∈ cSec M := hPM hpP
    have hpC : (p : G) ∈ centralizer ({y} : Set G) := p.2
    have hk : ⁅e, (p : G)⁆ ∈ pPrimeCoreOf 2 M := hpM.2.2 e heM
    have hkC : ⁅e, (p : G)⁆ ∈ centralizer ({y} : Set G) := by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem heC hpC) (inv_mem heC)) (inv_mem hpC)
    refine S3.mem_imgBar.2 ⟨⟨⁅e, (p : G)⁆, hkC⟩, Subgroup.mem_inf.2 ⟨hk, hkC⟩, ?_⟩
    rw [← piC_of_mem y hkC, commutatorElement_def,
      piC_mul y (mul_mem (mul_mem heC hpC) (inv_mem heC)) (inv_mem hpC),
      piC_mul y (mul_mem heC hpC) (inv_mem heC), piC_mul y heC hpC, piC_inv y heC,
      piC_inv y hpC, piC_of_mem y hpC, hpe]
  have hbot : φ.range ⊓ Nb = ⊥ := by
    refine S3Sec29D3.diag_odd_normal hc hq hz inf_le_left (fun d' hd' n hn => ?_) ?_
    · exact Subgroup.mem_inf.2 ⟨mul_mem (mul_mem hd' (Subgroup.mem_inf.1 hn).1) (inv_mem hd'),
        hΔN d' hd' n (Subgroup.mem_inf.1 hn).2⟩
    · exact Odd.of_dvd_nat hNodd (Subgroup.card_dvd_of_le inf_le_right)
  have h1 : piC y e * d * (piC y e)⁻¹ * d⁻¹ = 1 := by
    have : piC y e * d * (piC y e)⁻¹ * d⁻¹ ∈ φ.range ⊓ Nb := Subgroup.mem_inf.2 ⟨hcomm_Δ, hcomm_N⟩
    rwa [hbot, Subgroup.mem_bot] at this
  calc piC y e * d = (piC y e * d * (piC y e)⁻¹ * d⁻¹) * d * piC y e := by group
    _ = d * piC y e := by rw [h1, one_mul]

theorem lemma298wL (hK31e : Kg31e G) (hK21d : Kg21d) (hKS : S3Sec29C.S16cKG) {x y : G}
    {K A B Q D J R : Subgroup G} (h : Ctx29w G x K A B Q y y D J)
    (h295 : B ⊓ cSec K ⊓ cSec J = ⊥) {L : Subgroup G} (hBL : B ≤ normalizer (L : Set G))
    (hQL : Q ≤ normalizer (L : Set G)) (hyL : y ∈ cSec L) (hJL : J ≤ cSec L)
    (hR : IsSylowOf 2 R (Jss y L ⊔ Q ⊔ zpowers y))
    (hRB : ∀ g ∈ B ⊓ cSec K, ∀ r ∈ R, g * r * g⁻¹ ∈ R)
    (h297a : ∀ r ∈ R ⊓ centralizer ({x} : Set G), r * r ∈ Q → r ∈ Q ∨ r * y⁻¹ ∈ Q)
    (h297c : Q ⊓ ((R ⊓ Zstar (Jstar B J)) ⊔ zpowers y) = ⊥) (hMu : MuPkgL K A Q y L) :
    ¬ HasSL2Model (↥J ⧸ pPrimeCore 2 ↥J) Odd := by
  intro hsl
  have hJ := S3Sec29D2.J_comp h
  have hO := S3Sec29D2.obs52_of_sl2 h hsl
  have hBy := S3Sec29D2.B_le_centralizer_y h
  obtain ⟨hh, hhB0, hh1, hhN⟩ := S3Sec29D2.exists_B0_mem_normalizer h hO
  obtain ⟨g₀, hg₀B0, hg₀N⟩ :=
    exists_B0_not_mem_normalizer_L hK31e hK21d hKS h hsl h295 hBL hQL hyL hJL hR hRB h297a h297c
      hMu
  obtain ⟨z, hz⟩ := S3Sec29D5.exists_sl2Data hJ hsl
  have hhB : hh ∈ B := (Subgroup.mem_inf.1 hhB0).1
  have hg₀B : g₀ ∈ B := (Subgroup.mem_inf.1 hg₀B0).1
  have hhC : hh ∈ centralizer ({y} : Set G) := hBy hhB
  have hg₀C : g₀ ∈ centralizer ({y} : Set G) := hBy hg₀B
  have hg₁B0 : g₀ * hh ∈ B ⊓ cSec K := mul_mem hg₀B0 hhB0
  have hg₁N : g₀ * hh ∉ normalizer (J : Set G) := fun h1 => hg₀N (by
    have := mul_mem h1 (inv_mem hhN)
    rwa [mul_inv_cancel_right] at this)
  have hg₁C : g₀ * hh ∈ centralizer ({y} : Set G) := mul_mem hg₀C hhC
  have hcc₀ := S3Sec29D5.commConj_of_not_mem_normalizer hJ hg₀C hg₀N
  have hcc₁ := S3Sec29D5.commConj_of_not_mem_normalizer hJ hg₁C hg₁N
  have hπ₁ : piC y (g₀ * hh) = piC y g₀ * piC y hh := piC_mul y hg₀C hhC
  have hcc₁' : S3Sec29D3.CommConj (S3.imgBar y J) (piC y g₀ * piC y hh) := hπ₁ ▸ hcc₁
  have hhN' : piC y hh ∈ normalizer ((S3.imgBar y J : Subgroup (CentralizerBar y)) :
      Set (CentralizerBar y)) := S3Sec29C.piC_mem_normalizer hhC hhN
  have hhne : ∃ c ∈ S3.imgBar y J, piC y hh * c * (piC y hh)⁻¹ ≠ c := by
    by_contra hall
    push Not at hall
    have hc : hh ∈ cSec J := S3Sec29C.mem_cSec_of_piC hJ hhC fun g hg => hall _
      (S3.mem_imgBar.2 ⟨⟨g, hJ.1 hg⟩, hg, (piC_of_mem y (hJ.1 hg)).symm⟩)
    have : hh ∈ B ⊓ cSec K ⊓ cSec J := Subgroup.mem_inf.2 ⟨hhB0, hc⟩
    rw [h295, Subgroup.mem_bot] at this
    exact hh1 this
  have hgen := S3Sec29D3.le_diag_sup hcc₀ hcc₁' (S3Sec29D5.isQuasisimple_imgBar hJ) hhN' hhne
  obtain ⟨E, hEK, hAE, -, hEel, hE4, -⟩ := S3Sec29D2.exists_E h
  have hEA : E ≤ A := hAE ▸ le_sup_left
  have hEcJ : E ≤ B ⊓ cSec J := by
    intro e he
    have heAK : e ∈ A ⊓ K := Subgroup.mem_inf.2 ⟨hEA he, hEK he⟩
    have heB : e ∈ B := h.ext.1 (hEA he)
    have heC : e ∈ centralizer ({y} : Set G) := hBy heB
    have hD₀ : (S3Sec29D3.diagHom (S3.imgBar y J) (piC y g₀) hcc₀).range ≤
        centralizer ({piC y e} : Set (CentralizerBar y)) := fun d hd =>
      Subgroup.mem_centralizer_singleton_iff.2
        (centralizes_diag_L hKS h hO hBL hJL hMu hz hg₀B0 hg₀N rfl hcc₀ heAK d hd).symm
    have hD₁ : (S3Sec29D3.diagHom (S3.imgBar y J) (piC y g₀ * piC y hh) hcc₁').range ≤
        centralizer ({piC y e} : Set (CentralizerBar y)) := fun d hd =>
      Subgroup.mem_centralizer_singleton_iff.2
        (centralizes_diag_L hKS h hO hBL hJL hMu hz hg₁B0 hg₁N hπ₁.symm hcc₁' heAK d hd).symm
    have hJe := hgen.trans (sup_le hD₀ hD₁)
    refine Subgroup.mem_inf.2 ⟨heB, S3Sec29C.mem_cSec_of_piC hJ heC fun g hg => ?_⟩
    have hgC := hJ.1 hg
    have h1 := Subgroup.mem_centralizer_singleton_iff.1
      (hJe (S3.mem_imgBar.2 ⟨⟨g, hgC⟩, hg, (piC_of_mem y hgC).symm⟩))
    rw [← h1]; group
  have h4 : 4 ≤ Nat.card ↥(B ⊓ cSec J) := hE4 ▸ Subgroup.card_le_of_le hEcJ
  have h2 := S3Sec29D2.card_cSec_le_two h hO
  omega

end S3Sec29JB

end CFSG.GH74.Generic.BProg.B3
