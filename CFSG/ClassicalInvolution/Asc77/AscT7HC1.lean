module

public import CFSG.ClassicalInvolution.Asc77.AscIHSectL
public import CFSG.ClassicalInvolution.Asc77.AscE184SecD
public import CFSG.ClassicalInvolution.Asc77.WP3LayerSec

public section

namespace CFSG.ClassicalInvolution.Asc77.T7H

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.ExactLayer AscE184Sect

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)} {c : G}

@[expose] noncomputable def exactImg (Ω : Set (Subgroup G)) (c : G) (K : Subgroup G) :
    Subgroup (↥(exactLayer Ω c) ⧸ classicalInvolutionOddCore ↥(exactLayer Ω c)) :=
  ((exactCore c K).subgroupOf (exactLayer Ω c)).map
    (QuotientGroup.mk' (classicalInvolutionOddCore ↥(exactLayer Ω c)))

theorem exactImg_mem {K : Subgroup G} (hK : K ∈ tqMembers Ω c) :
    exactImg Ω c K ∈ oddQuotientFamily (exactPair Ω c) :=
  ⟨_, ⟨exactCore c K, exactCore_mem_exactFamily hK, exactCore_le_exactLayer hK, rfl⟩, rfl⟩

theorem exists_exactImg_of_mem {M : Subgroup (↥(exactLayer Ω c) ⧸
    classicalInvolutionOddCore ↥(exactLayer Ω c))} (hM : M ∈ oddQuotientFamily (exactPair Ω c)) :
    ∃ J ∈ tqMembers Ω c, M = exactImg Ω c J := by
  obtain ⟨_, ⟨L, ⟨J, hJ, rfl⟩, hLY, rfl⟩, rfl⟩ := hM
  exact ⟨J, hJ, rfl⟩


theorem exactImg_conjSub_odd {K : Subgroup G} {n : ↥(exactLayer Ω c)}
    (hn : n ∈ classicalInvolutionOddCore ↥(exactLayer Ω c)) (hnc : (n : G) * c * (n : G)⁻¹ = c) :
    exactImg Ω c (conjSub (n : G) K) = exactImg Ω c K := by
  have h1 : exactCore c (conjSub (n : G) K) = conjSub (n : G) (exactCore c K) := by
    have := exactCore_conjSub (n : G) c K
    rwa [hnc] at this
  unfold exactImg
  rw [h1, ← conjSub_subgroupOf, AscQuot.map_conjSub,
    show QuotientGroup.mk' (classicalInvolutionOddCore ↥(exactLayer Ω c)) n = 1 from
      (QuotientGroup.eq_one_iff n).mpr hn, conjSub_one]


omit [Fact p.Prime] in
theorem mem_centralizer_of_mem_exactLayer {n : ↥(exactLayer Ω c)} :
    (n : G) * c * (n : G)⁻¹ = c := by
  have h := Subgroup.mem_centralizer_singleton_iff.mp (exactLayer_le_centralizer Ω c n.2)
  calc (n : G) * c * (n : G)⁻¹ = c * (n : G) * (n : G)⁻¹ := by rw [h]
    _ = c := by group

theorem exactImg_nbr_lift (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hc2 : IsPGroup 2 (Subgroup.zpowers c)) {K J : Subgroup G}
    (hK : K ∈ tqMembers Ω c) (hJ : J ∈ tqMembers Ω c)
    (h : exactImg Ω c J ∈ omegaNbr (oddQuotientFamily (exactPair Ω c)) (exactImg Ω c K)) :
    ∃ n : ↥(exactLayer Ω c), n ∈ classicalInvolutionOddCore ↥(exactLayer Ω c) ∧
      J ∈ omegaNbr Ω (conjSub (n : G) K) := by
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
  obtain ⟨n, hn, hnb⟩ := exists_conj_omegaNbr hp hq hΛ hΛ' hN₀odd hKY hJY h
  refine ⟨n, hn, ?_⟩
  have hnc : (n : G) * c * (n : G)⁻¹ = c := mem_centralizer_of_mem_exactLayer
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
  have h3 : exactCore c J ∈ omegaNbr (exactFamily Ω c) (conjSub (n : G) (exactCore c K)) :=
    omegaNbr_of_restrict hK'Y hJ'Y hnb
  have hK'' : conjSub (n : G) K ∈ tqMembers Ω c :=
    conjSub_mem_tqMembers hΩ.conjInvariant hncent hK
  have h4 : exactCore c (conjSub (n : G) K) = conjSub (n : G) (exactCore c K) := by
    have := exactCore_conjSub (n : G) c K
    rwa [hnc] at this
  refine mem_omegaNbr_of_sectionFamily hp hq hΩ hc2 (A := Subgroup.zpowers c)
    (by rw [sectionMembers_zpowers]; exact hK'') (by rw [sectionMembers_zpowers]; exact hJ) ?_
  rw [secMember_zpowers_eq_exactCore hΩ hc2 hJ.1 hJ.2,
    secMember_zpowers_eq_exactCore hΩ hc2 hK''.1 hK''.2, sectionFamily_zpowers hΩ hc2, h4]
  exact h3


theorem exactImg_nbr_eq (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hc2 : IsPGroup 2 (Subgroup.zpowers c)) {K K' : Subgroup G} (hK : K ∈ tqMembers Ω c)
    (hperp : KPerp Ω K = {K, K'}) {J : Subgroup G} (hJ : J ∈ tqMembers Ω c)
    (h : exactImg Ω c J ∈ omegaNbr (oddQuotientFamily (exactPair Ω c)) (exactImg Ω c K)) :
    exactImg Ω c J = exactImg Ω c K' := by
  obtain ⟨n, hn, hnb⟩ := exactImg_nbr_lift hp hq hΩ hc2 hK hJ h
  have hnc : (n : G) * c * (n : G)⁻¹ = c := mem_centralizer_of_mem_exactLayer
  have h1 := omegaNbr_conj hΩ.conjInvariant hnb (n : G)⁻¹
  rw [conjSub_inv_conjSub] at h1
  have h2 : conjSub (n : G)⁻¹ J ∈ KPerp Ω K := Set.mem_insert_of_mem _ h1
  rw [hperp] at h2
  have h3 : conjSub (n : G)⁻¹ J = K' := by
    rcases h2 with h2 | h2
    · exact absurd h2 h1.2.1
    · exact h2
  have h4 : J = conjSub (n : G) K' := by
    rw [← h3, conjSub_conjSub_inv]
  rw [h4]
  exact exactImg_conjSub_odd hn hnc

end CFSG.ClassicalInvolution.Asc77.T7H
