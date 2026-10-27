module

public import CFSG.ClassicalInvolution.Asc77.AscT7HC4
import CFSG.ClassicalInvolution.Asc77.AscIHSectF
import CFSG.ClassicalInvolution.ModelFacts.Orth15SExact

public section

namespace CFSG.ClassicalInvolution.Asc77

namespace S22

set_option linter.unusedSectionVars false

open CFSG CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Disconnected

section Lift

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}

theorem exactImg_star_lift (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hc2 : IsPGroup 2 (Subgroup.zpowers c)) {K J : Subgroup G}
    (hK : K ∈ tqMembers Ω c) (hJ : J ∈ tqMembers Ω c)
    (h : T7H.exactImg Ω c J ∈
      omegaStarNbr (oddQuotientFamily (exactPair Ω c)) (T7H.exactImg Ω c K)) :
    ∃ n : ↥(exactLayer Ω c), n ∈ classicalInvolutionOddCore ↥(exactLayer Ω c) ∧
      J ∈ omegaStarNbr Ω (conjSub (n : G) K) := by
  set Y := exactLayer Ω c with hY
  set N₀ := classicalInvolutionOddCore ↥Y with hN₀
  have hN₀odd : Odd (Nat.card N₀) := CFSG.ComponentClassification.OddCore.odd_card ↥Y
  have hΛ : HypOmegaMod p f (exactPair Ω c) := hypOmegaMod_exactPair hp hq hΩ hc2
  have hΛ' : HypOmegaMod p f (quotFamily (exactPair Ω c) N₀) :=
    oddQuotHyp p f hp hq ↥Y (exactPair Ω c) hΛ N₀ hN₀odd
  have hKY : (exactCore c K).subgroupOf Y ∈ exactPair Ω c :=
    ⟨exactCore c K, exactCore_mem_exactFamily hK, exactCore_le_exactLayer hK, rfl⟩
  have hJY : (exactCore c J).subgroupOf Y ∈ exactPair Ω c :=
    ⟨exactCore c J, exactCore_mem_exactFamily hJ, exactCore_le_exactLayer hJ, rfl⟩
  obtain ⟨n, hn, hnb⟩ := exists_conj_omegaStarNbr hp hq hΛ hΛ' hN₀odd hKY hJY h
  refine ⟨n, hn, ?_⟩
  have hnc : (n : G) * c * (n : G)⁻¹ = c := T7H.mem_centralizer_of_mem_exactLayer
  have hncent : (n : G) ∈ Subgroup.centralizer ({c} : Set G) :=
    exactLayer_le_centralizer Ω c n.2
  rw [conjSub_subgroupOf] at hnb
  have hK'Y : conjSub (n : G) (exactCore c K) ≤ Y := by
    intro x hx
    rw [mem_conjSub_iff] at hx
    have h1 : (n : G)⁻¹ * x * (n : G) ∈ Y := exactCore_le_exactLayer hK hx
    have h2 := Y.mul_mem (Y.mul_mem n.2 h1) (Y.inv_mem n.2)
    simpa [mul_assoc] using h2
  have hJ'Y : exactCore c J ≤ Y := exactCore_le_exactLayer hJ
  have h3 : exactCore c J ∈ omegaStarNbr (exactFamily Ω c) (conjSub (n : G) (exactCore c K)) :=
    omegaStarNbr_of_restrict hK'Y hJ'Y hnb
  have hK'' : conjSub (n : G) K ∈ tqMembers Ω c :=
    conjSub_mem_tqMembers hΩ.conjInvariant hncent hK
  have h4 : exactCore c (conjSub (n : G) K) = conjSub (n : G) (exactCore c K) := by
    have := exactCore_conjSub (n : G) c K
    rwa [hnc] at this
  refine AscE184Sect.mem_omegaStarNbr_of_sectionFamily hp hq hΩ hc2 (A := Subgroup.zpowers c)
    (by rw [sectionMembers_zpowers]; exact hK'') (by rw [sectionMembers_zpowers]; exact hJ) ?_
  rw [secMember_zpowers_eq_exactCore hΩ hc2 hJ.1 hJ.2,
    secMember_zpowers_eq_exactCore hΩ hc2 hK''.1 hK''.2, sectionFamily_zpowers hΩ hc2, h4]
  exact h3

theorem hstar_layer (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    (hA : ∀ M ∈ Ω, ∀ J ∈ omegaStarNbr Ω M, ∃ w, IsUniqueInvolution M w ∧ IsUniqueInvolution J w) :
    ∀ B ∈ oddQuotientFamily (exactPair Ω c), ∀ J ∈ oddQuotientFamily (exactPair Ω c),
      J ∈ omegaStarNbr (oddQuotientFamily (exactPair Ω c)) B →
        ∃ w, IsUniqueInvolution B w ∧ IsUniqueInvolution J w := by
  intro B hB J hJ hnb
  obtain ⟨B₀, hB₀, rfl⟩ := T7H.exists_exactImg_of_mem hB
  obtain ⟨J₀, hJ₀, rfl⟩ := T7H.exists_exactImg_of_mem hJ
  obtain ⟨n, hn, hnb'⟩ := exactImg_star_lift hp hq hΩ hc2 hB₀ hJ₀ hnb
  have hncent : (n : G) ∈ Subgroup.centralizer ({c} : Set G) :=
    exactLayer_le_centralizer Ω c n.2
  have hnc : (n : G) * c * (n : G)⁻¹ = c := T7H.mem_centralizer_of_mem_exactLayer
  have hBn : conjSub (n : G) B₀ ∈ tqMembers Ω c :=
    conjSub_mem_tqMembers hΩ.conjInvariant hncent hB₀
  obtain ⟨w, hw1, hw2⟩ := hA _ (hΩ.conjInvariant (n : G) B₀ hB₀.1) J₀ hnb'
  have hwc : w ∈ exactCore c (conjSub (n : G) B₀) :=
    (T7H.isUniqueInvolution_exactCore hp hΩ hc2 hBn hw1).mem
  have hwY : w ∈ exactLayer Ω c := exactCore_le_exactLayer hBn hwc
  refine ⟨T7H.toBar Ω c w hwY, ?_, T7H.exactImg_isUnique hp hΩ hc2 hJ₀ hw2 hwY⟩
  rw [← T7H.exactImg_conjSub_odd hn hnc (K := B₀)]
  exact T7H.exactImg_isUnique hp hΩ hc2 hBn hw1 hwY

end Lift

section Section

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem layer_section (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hAΩ : ∀ M ∈ Ω, AEmpty Ω M) {u : G} (hu2 : u * u = 1)
    (hnc : ¬ ({u} : Set G) ⊆ Subgroup.center G) :
    GenSection p f (oddQuotientFamily (exactPair Ω u)) ∧
      Nat.card (↥(exactLayer Ω u) ⧸ classicalInvolutionOddCore ↥(exactLayer Ω u)) <
        Nat.card G := by
  classical
  have hcpg : IsPGroup 2 (Subgroup.zpowers u) := isPGroup_zpowers_of_sq_eq_one hu2
  set Y := exactLayer Ω u with hY
  set N₀ := classicalInvolutionOddCore ↥Y with hN₀
  have hN₀odd : Odd (Nat.card N₀) := CFSG.ComponentClassification.OddCore.odd_card ↥Y
  have hΛ : HypOmegaMod p f (exactPair Ω u) := hypOmegaMod_exactPair hp hq hΩ hcpg
  have hΦ : HypOmegaMod p f (oddQuotientFamily (exactPair Ω u)) :=
    oddQuotHyp p f hp hq ↥Y (exactPair Ω u) hΛ N₀ hN₀odd
  have hgen : omegaGen (oddQuotientFamily (exactPair Ω u)) = ⊤ :=
    omegaGen_quotFamily_eq_top (exactPair Ω u) N₀
      (omegaGen_restrictFamily_eq_top (exactFamily Ω u) Y (exactLayer_eq_iSup Ω u).symm)
  have hAΛ : ∀ L ∈ exactPair Ω u, AEmpty (exactPair Ω u) L := by
    have h0 := aEmpty_exactPair hp hq hΩ hAΩ hcpg
    have e0 : centralizingMembers (exactFamily Ω u) {u} = exactFamily Ω u :=
      centMembers_exactFamily Ω u
    rw [e0] at h0
    exact h0
  have hAΦ : ∀ L ∈ oddQuotientFamily (exactPair Ω u),
      AEmpty (oddQuotientFamily (exactPair Ω u)) L :=
    aEmpty_quotFamily hp hq hΛ hΦ hN₀odd hAΛ
  have hlt : Nat.card (↥Y ⧸ N₀) < Nat.card G := by
    have h1 : Nat.card (↥Y ⧸ N₀) ≤ Nat.card ↥Y :=
      Nat.le_of_dvd Nat.card_pos (Subgroup.index_dvd_card N₀)
    have h2 : Nat.card ↥Y < Nat.card G := card_exactLayer_lt hnc
    omega
  exact ⟨⟨hΦ, CFSG.ComponentClassification.OddCore.quotient_corefree ↥Y, hgen, hAΦ⟩, hlt⟩

end Section

end S22

end CFSG.ClassicalInvolution.Asc77
