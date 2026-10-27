module

public import CFSG.LocalAnalysis.ABGTheoremB.IVAssembly
public import CFSG.LocalAnalysis.ABGTheoremB.IV7Assembly
public import CFSG.LocalAnalysis.ABGTheoremB.IV8
public import CFSG.LocalAnalysis.ABGTheoremB.V2
public import CFSG.LocalAnalysis.ABGTheoremB.V6
public import CFSG.LocalAnalysis.ABGTheoremB.CorollaryV21Proof
public import CFSG.LocalAnalysis.ABGTheoremB.TheoremBStar
public import CFSG.LocalAnalysis.ABGTheoremB.V56Bridges
public import CFSG.LocalAnalysis.ABGTheoremB.PropR1Input
public import CFSG.LocalAnalysis.ABGTheoremB.ClaimR23
public import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.OmnibusQD
public import CFSG.GroupTheory.ABGLocalTools.PStabilityDGroup
public import CFSG.LocalAnalysis.ABGTheoremB.IV9Assembly
public import CFSG.LocalAnalysis.ABGTheoremB.IV9DGroupTrichotomy
public import CFSG.LocalAnalysis.ABGTheoremB.IV9DGroupCore
public import CFSG.LocalAnalysis.ABGTheoremB.PSL2Schur
public import CFSG.LocalAnalysis.ABGTheoremB.PSL2FourGroups
public import CFSG.LocalAnalysis.ABGTheoremB.IV9DGroupCentralizers
public import CFSG.LocalAnalysis.ABGTheoremB.V4Prop1
public import CFSG.LocalAnalysis.ABGTheoremB.V4Lemma5
public import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.InputsFourFusion
public import CFSG.GroupTheory.ABGDGroups.LinearOddCyclic
public import CFSG.LocalAnalysis.ABGTheoremB.LinearImageForm
public import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.DGroupCentralizerQD
public import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.FinalInputsSection
public import Certificates.Certificate1
public import Certificates.Certificate2
public import Certificates.Certificate7
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate8
public import Certificates.Certificate9
public import Certificates.Certificate10
public import Certificates.Certificate11
public import Certificates.Certificate12
public import Certificates.Certificate42
public import Certificates.Certificate43
public import Certificates.Certificate44
public import CFSG.GroupTheory.ABGLocalTools.PStabilityDefs
public import CFSG.GroupTheory.ABGLocalTools.Sections
public import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.Elimination

public section

namespace CFSG.ABGTheoremB

open CFSG.QuasiDihedralFusion CFSG.ABGLocalTools CFSG.ABGTheoremB.TotallyInverted

namespace Setting

variable {G : Type} [Group G] [Finite G] (σ : Setting G)

theorem isPStable_of_isDGroupWrt : ∀ H : Subgroup G, σ.D ≤ H →
    IsDGroupWrt (σ.T.subgroupOf H) → ∀ r : ℕ, r.Prime → r ≠ 2 → CFSG.pCore r H ≠ ⊥ →
      CFSG.pPrimeCore r H ≤ CFSG.oddCore H → IsPStable r H := by
  intro H _ hW r hr hr2 hOp _
  have : Fact r.Prime := ⟨hr⟩
  exact isPStable_of_isDGroup hr2 hW.1 hOp

theorem propIV91_of_inputs (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) (hN : σ.IVNFacts)
    (h_y : σ.height = 1 → ∃ y ∈ σ.D, y ∉ centerOf σ.D ∧ y ∈ σ.L₀ ∧
      ∀ S₁ : Sylow 2 G, σ.D ≤ (S₁ : Subgroup G) →
        ∃ s ∈ (S₁ : Subgroup G), y = σ.x₂ * (s * σ.x₂ * s⁻¹))
    (h_II417 : ∀ r : ℕ, σ.HypIV7 r → ∀ d : σ.IV7Data r, ∀ W : Subgroup G, W ≤ d.R →
      Subgroup.normalizer (d.R : Set G) ≤ Subgroup.normalizer (W : Set G) →
      (∀ w ∈ W, w ^ r = 1) →
      Subgroup.normalizer (d.R : Set G) ⊓ Subgroup.centralizer (W : Set G) ≤
        solvRadIn (Subgroup.normalizer (d.R : Set G)) →
      ¬ ∃ a ∈ W, ∃ b ∈ W, W ≤ Subgroup.closure {a, b} ⊔ ⁅W, W⁆)
    (h_II510 : ∀ r : ℕ, σ.HypIV7 r → ∀ d : σ.IV7Data r, ∀ W : Subgroup G, W ≤ d.R →
      Subgroup.normalizer (d.R : Set G) ≤ Subgroup.normalizer (W : Set G) →
      (∀ a ∈ W, ∀ b ∈ W, a * b = b * a) → (∀ w ∈ W, w ^ r = 1) →
      Subgroup.normalizer (d.R : Set G) ⊓ Subgroup.centralizer (W : Set G) ≤
        solvRadIn (Subgroup.normalizer (d.R : Set G)) →
      (W ⊓ Subgroup.centralizer {σ.x₂}).relIndex W = r →
      ∃ u ∈ Subgroup.normalizer (d.R : Set G), ∃ s k : ℕ, s.Prime ∧ s ≠ 2 ∧ s ≠ r ∧
        u ^ (s ^ k) ∈ Subgroup.centralizer (W : Set G) ∧
        u ∉ Subgroup.centralizer (W : Set G) ∧
        σ.x₂ * u * σ.x₂⁻¹ * u ∈ Subgroup.centralizer (W : Set G) ∧
        ∃ a ∈ W ⊓ Subgroup.centralizer {σ.x₂}, a ≠ 1 ∧ u * a = a * u) :
    σ.PropIV91 :=
  σ.propIV91_of hσ hII hN
    (fun _ hDH hW _ hFH hF hTF hFT =>
      CFSG.ABGDGroups.exists_zpow_mem_oddCore_map_of_commutator_eq hW.1
        ((σ.T_le_D hσ).trans hDH) hW.2.1 hFH hF hTF hFT)
    (σ.dGroup_trichotomy hσ hII) (σ.inf_centralizer_T_le_of_linearType_nine hσ)
    psl2_odd_central_section
    (fun _ hr hr2 => σ.exists_automizer_element_of_psl2_section hσ hr hr2) h_y
    (fun _ => σ.T_le_pPrimeCoreIn_of_even hσ hII) h_II417
    (fun _ hr hr2 => σ.dGroup_exponent_commutator_le hσ hII hr hr2) h_II510
    (σ.dGroup_le_oddCore_of_inverted hσ hII)

theorem propIV91_of_height_ne_one' (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) (hN : σ.IVNFacts)
    (hh : σ.height ≠ 1) : σ.PropIV91 :=
  σ.propIV91_of_height_ne_one hσ hII hN hh
    (fun _ hDH hW _ hFH hF hTF hFT =>
      CFSG.ABGDGroups.exists_zpow_mem_oddCore_map_of_commutator_eq hW.1
        ((σ.T_le_D hσ).trans hDH) hW.2.1 hFH hF hTF hFT)
    (σ.dGroup_trichotomy hσ hII)

theorem stage_one (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) (hN : σ.IVNFacts)
    (h91 : σ.PropIV91)
    (h_II61Q : ∀ r : ℕ, r.Prime → r ∣ Nat.card σ.ON → r ≠ σ.p → ∀ H ∈ σ.familyL r,
      CFSG.pPrimeCore r H ≤ CFSG.solvableRadical H → IsPStable r H) :
    ∀ r : ℕ, σ.HypIV7 r → r = σ.p := fun _ hr =>
  σ.propV21_of_familyL hσ hII (σ.lemmaIV32_of hσ hII) (σ.propIV61_of hσ hII) (σ.corIV61_of hσ hII)
    (σ.propIV71_of_IVNFacts hσ hII hN) (σ.lemmaIV81 hσ hII) (σ.lemmaIV83 hσ hII)
    (σ.corIV81 hσ hII) h91 (fun _ _ => σ.isPStable_of_isDGroupWrt) h_II61Q
    hN.C_le_oddCore_sup_D hr

theorem stage_two_of_height_eq_one (hσ : σ.IsValid) (hh : σ.height = 1)
    (hII : σ.ChapterIIFacts) (hN : σ.IVNFacts) (hT : σ.TIFacts)
    (hR1N : ∀ J : Subgroup G, σ.IsV21Layer J → σ.R1NFacts J) (h91 : σ.PropIV91)
    (h₁ : ∀ r : ℕ, σ.HypIV7 r → r = σ.p)
    (h41 : ∀ J : Subgroup G, σ.IsV21Layer J → σ.PropV41 J)
    (h45 : ∀ J : Subgroup G, σ.IsV21Layer J → σ.LemmaV45 J)
    (h_c12 : ∀ J : Subgroup G, σ.IsV21Layer J → σ.HypIV7 σ.p → ∀ W ∈ σ.familyW J,
      ∀ P : Subgroup G, IsSylowOf σ.p P σ.C → σ.D ≤ Subgroup.normalizer (P : Set G) →
      ∀ K ∈ σ.familyMstar σ.p, W ≤ K →
      ∀ U ∈ maximals (signalizersPerm K σ.D W σ.p), U ∈ maximals (signalizers K σ.D σ.p) →
      P ≤ U → pPrimeCoreIn σ.p (U ⊔ W) = ⊥ → σ.LinearImageForm σ.p K U) :
    ¬ σ.HypIV7 σ.p :=
  V56.propV61 hσ hII (σ.corollaryV21 hσ hII h₁ hN.sylow_quaternion_element) h41 h45
    (σ.cStructure_of hσ hN hT) (σ.lemmaV31_of hσ hII hN) (σ.lemmaV33_of hσ hII hN)
    (σ.propR1Input_of hσ hII hN hR1N)
    (σ.propR2Input_of_height_one hσ hII hh h91 σ.isPStable_of_isDGroupWrt h_c12)
    (σ.lemmaIV32_of hσ hII) (σ.propIV61_of hσ hII) (σ.propIV62 hσ hII)
    (σ.propIV71_of_IVNFacts hσ hII hN) (σ.lemmaIV81 hσ hII) (σ.lemmaIV83 hσ hII) h91

theorem theoremBStar_of_height_eq_one (hσ : σ.IsValid) (hh : σ.height = 1)
    (hII : σ.ChapterIIFacts) (hN : σ.IVNFacts) (hT : σ.TIFacts) (hT9 : TIFactsQ9 σ)
    (hQC : σ.QCoverFact) (hd : ∃ d ∈ σ.D, d * σ.x₂ * d⁻¹ = σ.x₃) (hF₀ : IsSylowOf 2 σ.F₀ σ.C)
    (hR1N : ∀ J : Subgroup G, σ.IsV21Layer J → σ.R1NFacts J) (h91 : σ.PropIV91)
    (h_II61Q : ∀ r : ℕ, r.Prime → r ∣ Nat.card σ.ON → r ≠ σ.p → ∀ H ∈ σ.familyL r,
      CFSG.pPrimeCore r H ≤ CFSG.solvableRadical H → IsPStable r H)
    (h41 : ∀ J : Subgroup G, σ.IsV21Layer J → σ.PropV41 J)
    (h45 : ∀ J : Subgroup G, σ.IsV21Layer J → σ.LemmaV45 J)
    (h_c12 : ∀ J : Subgroup G, σ.IsV21Layer J → σ.HypIV7 σ.p → ∀ W ∈ σ.familyW J,
      ∀ P : Subgroup G, IsSylowOf σ.p P σ.C → σ.D ≤ Subgroup.normalizer (P : Set G) →
      ∀ K ∈ σ.familyMstar σ.p, W ≤ K →
      ∀ U ∈ maximals (signalizersPerm K σ.D W σ.p), U ∈ maximals (signalizers K σ.D σ.p) →
      P ≤ U → pPrimeCoreIn σ.p (U ⊔ W) = ⊥ → σ.LinearImageForm σ.p K U)
    (h57 : ABG_II_5_7_Input σ) (h87 : ∀ r : ℕ, r.Prime → r ≠ 2 → ABG_V_8_7_D_Input σ r)
    (hDFF : Sec10.DGroupFourFusion G) (hI : ∀ (r : ℕ) (Δ : Data σ r), Sec11.Inputs Δ) :
    σ.TheoremBStar := by
  have h₁ := σ.stage_one hσ hII hN h91 h_II61Q
  have h₂ := σ.stage_two_of_height_eq_one hσ hh hII hN hT hR1N h91 h₁ h41 h45 h_c12
  have hV := σ.corollaryV61 hσ hII (σ.notTotallyInvertedOrdinary_of_stages h₁ h₂) hN.propIV51
    hN.sylow_quaternion_element
  exact σ.theoremBStar_of_stages h₁ h₂ (not_totallyInverted_of_height_eq_one hσ hh hII hV hT hT9
    hd hF₀ hQC h57 h87 hDFF hI)

theorem lemmaV31Input_of (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) (hN : σ.IVNFacts)
    {J : Subgroup G} (hJ : σ.IsV21Layer J) : V4.LemmaV31Input σ J where
  coprime := (σ.lemmaV31_of hσ hII hN J hJ).coprime
  comm := fun a ha b hb => by
    have hab : a * b * a⁻¹ * b⁻¹ ∈ ⁅σ.C ⊓ σ.L₀, σ.C ⊓ σ.L₀⁆ := by
      have := Subgroup.commutator_mem_commutator (H₁ := σ.C ⊓ σ.L₀) (H₂ := σ.C ⊓ σ.L₀)
        ⟨ha.1, hJ.le ha.2⟩ ⟨hb.1, hJ.le hb.2⟩
      simpa [commutatorElement_def] using this
    have hJab : a * b * a⁻¹ * b⁻¹ ∈ J :=
      J.mul_mem (J.mul_mem (J.mul_mem ha.2 hb.2) (J.inv_mem ha.2)) (J.inv_mem hb.2)
    rw [← hJ.inf_eq]
    exact ⟨hJab, hN.C_inf_L₀_commutator hab⟩
  covers := (σ.lemmaV31_of hσ hII hN J hJ).covers

structure QDBStarInputs : Prop where
  r1N : ∀ J : Subgroup G, σ.IsV21Layer J → σ.R1NFacts J
  II417 : ∀ r : ℕ, σ.HypIV7 r → ∀ d : σ.IV7Data r, ∀ W : Subgroup G, W ≤ d.R →
    Subgroup.normalizer (d.R : Set G) ≤ Subgroup.normalizer (W : Set G) →
    (∀ w ∈ W, w ^ r = 1) →
    Subgroup.normalizer (d.R : Set G) ⊓ Subgroup.centralizer (W : Set G) ≤
      solvRadIn (Subgroup.normalizer (d.R : Set G)) →
    ¬ ∃ a ∈ W, ∃ b ∈ W, W ≤ Subgroup.closure {a, b} ⊔ ⁅W, W⁆
  II510 : ∀ r : ℕ, σ.HypIV7 r → ∀ d : σ.IV7Data r, ∀ W : Subgroup G, W ≤ d.R →
    Subgroup.normalizer (d.R : Set G) ≤ Subgroup.normalizer (W : Set G) →
    (∀ a ∈ W, ∀ b ∈ W, a * b = b * a) → (∀ w ∈ W, w ^ r = 1) →
    Subgroup.normalizer (d.R : Set G) ⊓ Subgroup.centralizer (W : Set G) ≤
      solvRadIn (Subgroup.normalizer (d.R : Set G)) →
    (W ⊓ Subgroup.centralizer {σ.x₂}).relIndex W = r →
    ∃ u ∈ Subgroup.normalizer (d.R : Set G), ∃ s k : ℕ, s.Prime ∧ s ≠ 2 ∧ s ≠ r ∧
      u ^ (s ^ k) ∈ Subgroup.centralizer (W : Set G) ∧
      u ∉ Subgroup.centralizer (W : Set G) ∧
      σ.x₂ * u * σ.x₂⁻¹ * u ∈ Subgroup.centralizer (W : Set G) ∧
      ∃ a ∈ W ⊓ Subgroup.centralizer {σ.x₂}, a ≠ 1 ∧ u * a = a * u
  II61Q : ∀ r : ℕ, r.Prime → r ∣ Nat.card σ.ON → r ≠ σ.p → ∀ H ∈ σ.familyL r,
    CFSG.pPrimeCore r H ≤ CFSG.solvableRadical H → IsPStable r H
  v42 : ∀ J : Subgroup G, σ.IsV21Layer J → V4.LemmaII42Input σ J
  v46 : ∀ J : Subgroup G, σ.IsV21Layer J → V4.LemmaII46Input σ J
  v49 : ∀ J : Subgroup G, σ.IsV21Layer J → V4.LemmaII49Input σ J
  qSig : V4.QGroupSignalizerInput σ
  dSig : V4.DGroupSignalizerInput σ
  v87D : ∀ r : ℕ, r.Prime → r ≠ 2 → ABG_V_8_7_D_Input σ r
  dFourFusion : Sec10.DGroupFourFusion G

theorem theoremBStar_of_qdInputs (hσ : σ.IsValid) (hh : σ.height = 1)
    (hII : σ.ChapterIIFacts) (hN : σ.IVNFacts) (hT : σ.TIFacts) (hT9 : TIFactsQ9 σ)
    (hQC : σ.QCoverFact) (hd : ∃ d ∈ σ.D, d * σ.x₂ * d⁻¹ = σ.x₃) (hF₀ : IsSylowOf 2 σ.F₀ σ.C)
    (h_y : σ.height = 1 → ∃ y ∈ σ.D, y ∉ centerOf σ.D ∧ y ∈ σ.L₀ ∧
      ∀ S₁ : Sylow 2 G, σ.D ≤ (S₁ : Subgroup G) →
        ∃ s ∈ (S₁ : Subgroup G), y = σ.x₂ * (s * σ.x₂ * s⁻¹))
    (hI : ∀ (r : ℕ) (Δ : Data σ r), Sec11.ABG_II_4_4 Δ ∧ Sec11.ABG_II_4_10_iii Δ)
    (hQD : σ.QDBStarInputs) : σ.TheoremBStar := by
  have h91 := σ.propIV91_of_inputs hσ hII hN h_y hQD.II417 hQD.II510
  have h₁ := σ.stage_one hσ hII hN h91 hQD.II61Q
  have h41 : ∀ J : Subgroup G, σ.IsV21Layer J → σ.PropV41 J := fun J hJ =>
    V4.propV41 hσ hII hJ (σ.lemmaV31Input_of hσ hII hN hJ) hT.commutator_le (hQD.v42 J hJ)
      (hQD.v46 J hJ) (hQD.v49 J hJ) h₁ (Inputs.qGroupFourFusion G) hQD.qSig hQD.dSig
  have h45 : ∀ J : Subgroup G, σ.IsV21Layer J → σ.LemmaV45 J := fun J hJ =>
    V4.lemmaV45 hσ hII hJ (σ.lemmaV31Input_of hσ hII hN hJ) hT.commutator_le (hQD.v42 J hJ)
      (hQD.v46 J hJ) (hQD.v49 J hJ) h₁ (Inputs.qGroupFourFusion G)
  exact σ.theoremBStar_of_height_eq_one hσ hh hII hN hT hT9 hQC hd hF₀ hQD.r1N h91 hQD.II61Q
    h41 h45
    (fun J hJ hHyp W hW P hP hDP K hK hWK U hU hU' hPU hUW =>
      σ.linearImageForm_of hσ hII J hJ hHyp W hW P hP hDP K hK hWK U hU hU' hPU hUW)
    (abg_II_5_7_input_of hσ) hQD.v87D hQD.dFourFusion
    (fun r Δ => ⟨(hI r Δ).1, (hI r Δ).2, Sec11.abg_II_4_18_of hσ Δ⟩)

end Setting

end CFSG.ABGTheoremB
