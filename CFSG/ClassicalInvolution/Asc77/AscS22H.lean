module

public import CFSG.ClassicalInvolution.Asc77.AscT7HC4
public import CFSG.ClassicalInvolution.Asc77.AscT7JHyp51u

public section

namespace CFSG.ClassicalInvolution.Asc77

namespace S22

set_option linter.unusedSectionVars false

open CFSG CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement

section OddCore

variable {G : Type} [Group G] [Finite G]

theorem mem_oddCore_subgroupOf {Y Q : Subgroup G} (hQY : Q ≤ Y) {x : G} (hx : x ∈ Q)
    (hxo : (⟨x, hx⟩ : ↥Q) ∈ classicalInvolutionOddCore ↥Q) :
    (⟨⟨x, hQY hx⟩, Subgroup.mem_subgroupOf.mpr hx⟩ : ↥(Q.subgroupOf Y)) ∈
      classicalInvolutionOddCore ↥(Q.subgroupOf Y) := by
  let e : ↥(Q.subgroupOf Y) ≃* ↥Q := Subgroup.subgroupOfEquivOfLe hQY
  have hnorm : (classicalInvolutionOddCore ↥Q).Normal := inferInstance
  have hN : ((classicalInvolutionOddCore ↥Q).comap (e : ↥(Q.subgroupOf Y) →* ↥Q)).Normal :=
    hnorm.comap _
  have hcard : Nat.card ((classicalInvolutionOddCore ↥Q).comap (e : ↥(Q.subgroupOf Y) →* ↥Q)) =
      Nat.card (classicalInvolutionOddCore ↥Q) := by
    rw [Subgroup.comap_equiv_eq_map_symm]
    exact Subgroup.card_map_of_injective e.symm.injective
  have hodd : Odd (Nat.card
      ((classicalInvolutionOddCore ↥Q).comap (e : ↥(Q.subgroupOf Y) →* ↥Q))) := by
    rw [hcard]
    exact CFSG.ComponentClassification.OddCore.odd_card ↥Q
  have hle : (classicalInvolutionOddCore ↥Q).comap (e : ↥(Q.subgroupOf Y) →* ↥Q) ≤
      classicalInvolutionOddCore ↥(Q.subgroupOf Y) := le_sSup ⟨hN, hodd⟩
  exact hle hxo

end OddCore

section Action

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}

theorem exists_odd_mul (hΩ : HypOmegaMod p f Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    {J : Subgroup G} (hJ : J ∈ tqMembers Ω c) {v : G}
    (hvc : v ∈ Subgroup.centralizer ({c} : Set G)) (hvJ : v ∈ trivialOnQuot J) {k : G}
    (hk : k ∈ exactCore c J) (hkY : k ∈ exactLayer Ω c) (hvk : v * k * v⁻¹ ∈ exactLayer Ω c) :
    ∃ n ∈ oddCoreOf (T7H.exactImg Ω c J),
      T7H.toBar Ω c (v * k * v⁻¹) hvk = n * T7H.toBar Ω c k hkY := by
  obtain ⟨zJ, hzJ⟩ := hΩ.classical J hJ.1
  have hcore : v ∈ trivialOnQuot (exactCore c J) :=
    mem_trivialOnQuot_exactCore hzJ hc2 hJ.2 hvJ hvc
  have ho : ⁅v, k⁆ ∈ oddCoreIn (exactCore c J) := hcore.2 k hk
  have hoQ : ⁅v, k⁆ ∈ exactCore c J := oddCoreIn_le _ ho
  have hoY : ⁅v, k⁆ ∈ exactLayer Ω c := exactCore_le_exactLayer hJ hoQ
  set Y := exactLayer Ω c with hY
  set N₀ := classicalInvolutionOddCore ↥Y with hN₀
  have hN₀odd : Odd (Nat.card N₀) := CFSG.ComponentClassification.OddCore.odd_card ↥Y
  refine ⟨T7H.toBar Ω c ⁅v, k⁆ hoY, ?_, ?_⟩
  · have hP : oddCoreOf (T7H.exactImg Ω c J) =
        (oddCoreOf ((exactCore c J).subgroupOf Y)).map (QuotientGroup.mk' N₀) :=
      oddCoreOf_map_mk_of_odd (odd_natCard_inf hN₀odd _)
    rw [hP]
    have ho' : ⁅v, k⁆ ∈ oddCoreOf (exactCore c J) := ho
    obtain ⟨hx, hxo⟩ := mem_oddCoreOf_iff.mp ho'
    refine Subgroup.mem_map.mpr ⟨⟨⁅v, k⁆, hoY⟩, ?_, rfl⟩
    rw [mem_oddCoreOf_iff]
    exact ⟨Subgroup.mem_subgroupOf.mpr hoQ,
      mem_oddCore_subgroupOf (exactCore_le_exactLayer hJ) hoQ hxo⟩
  · unfold T7H.toBar
    rw [← map_mul]
    congr 1
    apply Subtype.ext
    show v * k * v⁻¹ = ⁅v, k⁆ * k
    simp only [commutatorElement_def]
    group

end Action

section Twins

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem exists_commuting_sylow_exactCore (hΩ : HypOmegaMod p f Ω) {c : G}
    {J J' : Subgroup G} {z : G} (hJ : J ∈ tqMembers Ω c) (hJ' : J' ∈ tqMembers Ω c)
    (hne : J ≠ J') (hz : IsUniqueInvolution J z) (hz' : IsUniqueInvolution J' z) :
    ∃ V V' : Subgroup G, IsSylow2In V (exactCore c J) ∧ IsSylow2In V' (exactCore c J') ∧
      Commutes V V' := by
  obtain ⟨V, hV, -⟩ := IsSylow2In.exists_ge (isPGroup_two_bot (G := G))
    (bot_le : ⊥ ≤ exactCore c J)
  have hVJ : V ≤ J := hV.1.trans (exactCore_le_left c J)
  have hVc : V ≤ Subgroup.centralizer ({c} : Set G) := hV.1.trans (exactCore_le_centralizer c J)
  have hJN : J ≤ Subgroup.normalizer (J' : Set G) :=
    hΩ.le_normalizer_of_twin hJ.1 hJ'.1 hne hz hz'
  have hVN : V ≤ Subgroup.normalizer (exactCore c J' : Set G) := by
    intro v hv
    rw [mem_normalizer_iff_conjSub_eq]
    have hvJ' : conjSub v J' = J' := mem_normalizer_iff_conjSub_eq.mp (hJN (hVJ hv))
    have hvc : v * c * v⁻¹ = c := by
      have := Subgroup.mem_centralizer_singleton_iff.mp (hVc hv)
      calc v * c * v⁻¹ = (c * v) * v⁻¹ := by rw [this]
        _ = c := by group
    have h2 := exactCore_conjSub v c J'
    rw [hvc, hvJ'] at h2
    exact h2.symm
  obtain ⟨V', hV', hfix⟩ := exists_sylow_normalized hV.2.1 hVN
  have hVV' : V ≤ Subgroup.normalizer (V' : Set G) := fun v hv =>
    mem_normalizer_iff_conjSub_eq.mpr (hfix v hv)
  have hP2 : IsPGroup 2 ↥(V ⊔ V') := hV.2.1.to_sup_of_normal_right' hV'.2.1 hVV'
  exact ⟨V, V', hV, hV', hΩ.commutes_of_twin_of_isPGroup hJ.1 hJ'.1 hne hz hz' hVJ
    (hV'.1.trans (exactCore_le_left c J')) hP2⟩

end Twins

section Data

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' K₃ : Subgroup G} {z u₁ u₂ u₃ : G}

theorem mem_tqMembers_of_twin (h : Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃) {J : Subgroup G}
    (hJ : J ∈ twinSet Ω K) (hJK : J ≠ K) (hJK' : J ≠ K') : J ∈ tqMembers Ω (u₁ * u₂) := by
  have hzJ : IsUniqueInvolution J z := isUniqueInvolution_of_mem_twinSet h.hz hJ
  have h1 : u₁ ∈ trivialOnQuot J :=
    T7J.twin_le_trivialOnQuot h.stand.hyp h.stand.mem hJ.1 hJK.symm h.hz hzJ h.hu₁.1
  have h2 : u₂ ∈ trivialOnQuot J :=
    T7J.twin_le_trivialOnQuot h.stand.hyp h.hK'.1 hJ.1 hJK'.symm h.hzK' hzJ h.hu₂.1
  exact ⟨hJ.1, (trivialOnQuot J).mul_mem h1 h2⟩

end Data

end S22

end CFSG.ClassicalInvolution.Asc77
