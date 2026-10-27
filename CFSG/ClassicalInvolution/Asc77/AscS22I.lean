module

public import CFSG.ClassicalInvolution.Asc77.AscS22H
import CFSG.ClassicalInvolution.Asc77.AscT7L2
import CFSG.ClassicalInvolution.Asc77.AscS22B
import CFSG.ClassicalInvolution.Asc77.AscT7ASectB
public import CFSG.ClassicalInvolution.Asc77.AscS22G
public import CFSG.ClassicalInvolution.Asc77.AscT7BThmE

public section

namespace CFSG.ClassicalInvolution.Asc77

namespace S22

set_option linter.unusedSectionVars false

open CFSG CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement

section Main

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {Ω : Set (Subgroup G)} {K K' K₃ : Subgroup G} {z u₁ u₂ u₃ : G}

theorem hAall_of_dstarComp (h : Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃)
    (hA : ∀ J ∈ dstarComp Ω K, J ∈ twinSet Ω K) :
    ∀ M ∈ Ω, ∀ J ∈ omegaStarNbr Ω M, ∃ w, IsUniqueInvolution M w ∧ IsUniqueInvolution J w := by
  have hΩ : HypOmegaMod p f Ω := h.stand.hyp
  intro M hM J hJ
  obtain ⟨g, hg⟩ := h.stand.trans M hM
  have e1 : conjSub g⁻¹ J ∈ omegaStarNbr Ω K := by
    have := omegaStarNbr_conj hΩ.conjInvariant hJ g⁻¹
    rwa [← hg, conjSub_inv_conjSub] at this
  have e2 : conjSub g⁻¹ J ∈ dstarComp Ω K :=
    Relation.ReflTransGen.single ⟨e1.1, Or.inl e1⟩
  have e3 : conjSub g⁻¹ J ∈ twinSet Ω K := hA _ e2
  have e4 := twinSet_conj hΩ.conjInvariant e3 g
  rw [conjSub_conjSub_inv, hg] at e4
  obtain ⟨-, w, hw1, hw2⟩ := e4
  exact ⟨w, hw1, hw2⟩

theorem layer_zStar (h : Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃) {K₄ : Subgroup G}
    (hK₄ : K₄ ∈ twinSet Ω K) (h1 : K₄ ≠ K) (h2 : K₄ ≠ K') (h3 : K₄ ≠ K₃)
    (hAall : ∀ M ∈ Ω, ∀ J ∈ omegaStarNbr Ω M,
      ∃ w, IsUniqueInvolution M w ∧ IsUniqueInvolution J w) :
    z ∈ zStarOf (Subgroup.centralizer ({u₁ * u₂} : Set G)) := by
  classical
  have hp : p ≠ 2 := h.stand.odd
  have hq : 5 ≤ p ^ f := h.stand.five
  have hΩ : HypOmegaMod p f Ω := h.stand.hyp
  have hBelow : CITBelowU p f (Nat.card G) := h.stand.below f hq
  have hK : K ∈ Ω := h.stand.mem
  have hu1 : u₁ * u₂ ≠ 1 :=
    (T7S22.mul_ne_one_of_twins h.stand.hyp h.stand.mem h.hK'.1 h.hne.symm h.hz h.hu₁.1
      h.hu₂.1 h.hu₂.2).1
  have hu₂C' : (u₁ * u₂) * u₂ = u₂ * (u₁ * u₂) := by
    calc (u₁ * u₂) * u₂ = (u₂ * u₁) * u₂ := by rw [h.comm₁₂]
      _ = u₂ * (u₁ * u₂) := by group
  have hu2 : (u₁ * u₂) * (u₁ * u₂) = 1 := h.sq_12
  set u : G := u₁ * u₂ with hudef
  have hcpg : IsPGroup 2 (Subgroup.zpowers u) := isPGroup_zpowers_of_sq_eq_one hu2
  have hnc : ¬ ({u} : Set G) ⊆ Subgroup.center G := by
    intro hsub
    obtain ⟨V, hV, -⟩ := IsSylow2In.exists_ge (isPGroup_two_bot (G := G)) (bot_le : ⊥ ≤ K)
    obtain ⟨x, -, y, -, hxy⟩ :=
      (hΩ.isQuatSub_of_mem_RSet hp (mem_RSet_of_isSylow2In hK hV)).exists_not_commute
    have hucen : u ∈ Subgroup.center G := hsub (Set.mem_singleton _)
    exact hu1 (T7B.eq_one_of_central ⟨x, y, hxy⟩ (fun g' => Subgroup.mem_center_iff.mp hucen g'))
  obtain ⟨hS, hlt⟩ := layer_section hp hq hΩ h.stand.aEmpty hu2 hnc
  have hK₃Ω : K₃ ∈ tqMembers Ω u := mem_tqMembers_of_twin h h.hK₃ h.hK₃K h.hK₃K'
  have hK₄Ω : K₄ ∈ tqMembers Ω u := mem_tqMembers_of_twin h hK₄ h1 h2
  have hzK₃ : IsUniqueInvolution K₃ z := h.hzK₃
  have hzK₄ : IsUniqueInvolution K₄ z := isUniqueInvolution_of_mem_twinSet h.hz hK₄
  have hzc₃ : z ∈ exactCore u K₃ := (T7H.isUniqueInvolution_exactCore hp hΩ hcpg hK₃Ω hzK₃).mem
  have hzY : z ∈ exactLayer Ω u := exactCore_le_exactLayer hK₃Ω hzc₃
  set Y : Subgroup G := exactLayer Ω u with hY
  set N₀ : Subgroup ↥Y := classicalInvolutionOddCore ↥Y with hN₀
  have hN₀odd : Odd (Nat.card N₀) := CFSG.ComponentClassification.OddCore.odd_card ↥Y
  have hA3 : T7H.exactImg Ω u K₃ ∈ oddQuotientFamily (exactPair Ω u) := T7H.exactImg_mem hK₃Ω
  have hA4 : T7H.exactImg Ω u K₄ ∈ oddQuotientFamily (exactPair Ω u) := T7H.exactImg_mem hK₄Ω
  have hzA3 : IsUniqueInvolution (T7H.exactImg Ω u K₃) (T7H.toBar Ω u z hzY) :=
    T7H.exactImg_isUnique hp hΩ hcpg hK₃Ω hzK₃ hzY
  have hzA4 : IsUniqueInvolution (T7H.exactImg Ω u K₄) (T7H.toBar Ω u z hzY) :=
    T7H.exactImg_isUnique hp hΩ hcpg hK₄Ω hzK₄ hzY
  have hne : T7H.exactImg Ω u K₃ ≠ T7H.exactImg Ω u K₄ := by
    obtain ⟨V, V', hV, hV', hcomm⟩ :=
      exists_commuting_sylow_exactCore hΩ hK₃Ω hK₄Ω (Ne.symm h3) hzK₃ hzK₄
    refine map_ne_of_commutes_sylow (N := N₀) hp hS.hyp hN₀odd
      (M₁ := (exactCore u K₃).subgroupOf Y) (M₂ := (exactCore u K₄).subgroupOf Y)
      (V₁ := V.subgroupOf Y) (V₂ := V'.subgroupOf Y)
      ⟨_, exactCore_mem_exactFamily hK₃Ω, exactCore_le_exactLayer hK₃Ω, rfl⟩
      (hV.subgroupOf (exactCore_le_exactLayer hK₃Ω))
      (hV'.subgroupOf (exactCore_le_exactLayer hK₄Ω)) ?_
    intro x hx y hy
    exact Subtype.ext (hcomm x (Subgroup.mem_subgroupOf.mp hx) y (Subgroup.mem_subgroupOf.mp hy))
  have hstar := hstar_layer hp hq hΩ hcpg hAall
  set C : Subgroup G := Subgroup.centralizer ({u} : Set G) with hC
  have hYC : Y ≤ C := exactLayer_le_centralizer Ω u
  have hYconj : ∀ g ∈ C, ∀ y ∈ Y, g * y * g⁻¹ ∈ Y := by
    intro g hg y hy
    have := conj_mem_conjSub (n := g) hy
    rwa [conjSub_exactLayer hΩ.conjInvariant hg] at this
  have hOnorm : ∀ g ∈ C, g ∈ Subgroup.normalizer (oddCoreOf Y : Set G) := fun g hg =>
    T7L.mem_normalizer_oddCoreOf
      (mem_normalizer_iff_conjSub_eq.mpr (conjSub_exactLayer hΩ.conjInvariant hg))
  have hu₂C : u₂ ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr hu₂C'.symm
  let N₁ : Subgroup ↥C := (oddCoreOf Y).subgroupOf C
  have hN₁ : N₁.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact (Subgroup.mem_normalizer_iff.mp (hOnorm g g.2) n).mp hn
  have hle : N₀ ≤ N₁.comap (Subgroup.inclusion hYC) := by
    intro n hn
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    exact ⟨n, hn, rfl⟩
  let ι : (↥Y ⧸ N₀) →* (↥C ⧸ N₁) := QuotientGroup.map N₀ N₁ (Subgroup.inclusion hYC) hle
  have hιmk : ∀ y : ↥Y, ι (QuotientGroup.mk' N₀ y) =
      QuotientGroup.mk' N₁ (Subgroup.inclusion hYC y) := fun y => rfl
  have hι : Function.Injective ι := by
    rw [injective_iff_map_eq_one]
    intro x hx
    induction x using QuotientGroup.induction_on with
    | H y =>
      have hy1 : QuotientGroup.mk' N₁ (Subgroup.inclusion hYC y) = 1 := hx
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hy1
      obtain ⟨hyY, hyo⟩ := mem_oddCoreOf_iff.mp hy1
      exact (QuotientGroup.eq_one_iff y).mpr hyo
  have hιmk' : ∀ y : ↥Y, ι (y : ↥Y ⧸ N₀) = ((Subgroup.inclusion hYC y : ↥C) : ↥C ⧸ N₁) :=
    fun y => rfl
  have hconjι : ∀ (g : ↥C) (y : ↥Y), (g : ↥C ⧸ N₁) * ι (y : ↥Y ⧸ N₀) * (g : ↥C ⧸ N₁)⁻¹ =
      ι ((⟨(g : G) * y * (g : G)⁻¹, hYconj g g.2 y y.2⟩ : ↥Y) : ↥Y ⧸ N₀) := by
    intro g y
    rw [hιmk', hιmk', ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
  let g₂ : ↥C := ⟨u₂, hu₂C⟩
  have ha : ∀ x : ↥Y ⧸ N₀, (g₂ : ↥C ⧸ N₁) * ι x * (g₂ : ↥C ⧸ N₁)⁻¹ ∈ ι.range ∧
      (g₂ : ↥C ⧸ N₁)⁻¹ * ι x * (g₂ : ↥C ⧸ N₁) ∈ ι.range := by
    intro x
    induction x using QuotientGroup.induction_on with
    | H y =>
      refine ⟨⟨_, (hconjι g₂ y).symm⟩, ?_⟩
      have h' := hconjι g₂⁻¹ y
      rw [QuotientGroup.mk_inv, inv_inv] at h'
      exact ⟨_, h'.symm⟩
  have hactJ : ∀ {J : Subgroup G}, J ∈ tqMembers Ω u → u₂ ∈ trivialOnQuot J →
      ∀ x ∈ T7H.exactImg Ω u J, ∃ n ∈ oddCoreOf (T7H.exactImg Ω u J),
        (g₂ : ↥C ⧸ N₁) * ι x * (g₂ : ↥C ⧸ N₁)⁻¹ = ι (n * x) := by
    intro J hJ hvJ x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    have hk : (y : G) ∈ exactCore u J := Subgroup.mem_subgroupOf.mp hy
    obtain ⟨n, hn, hnk⟩ := exists_odd_mul hΩ hcpg hJ hu₂C hvJ hk y.2 (hYconj u₂ hu₂C y y.2)
    refine ⟨n, hn, ?_⟩
    have e := hconjι g₂ y
    exact e.trans (congrArg ι hnk)
  have hu₂K₃ : u₂ ∈ trivialOnQuot K₃ :=
    T7J.twin_le_trivialOnQuot hΩ h.hK'.1 h.hK₃.1 h.hK₃K'.symm h.hzK' hzK₃ h.hu₂.1
  have hu₂K₄ : u₂ ∈ trivialOnQuot K₄ :=
    T7J.twin_le_trivialOnQuot hΩ h.hK'.1 hK₄.1 h2.symm h.hzK' hzK₄ h.hu₂.1
  have ha2 : (g₂ : ↥C ⧸ N₁) * (g₂ : ↥C ⧸ N₁) = ι (T7H.toBar Ω u z hzY) := by
    rw [← QuotientGroup.mk_mul]
    show ((g₂ * g₂ : ↥C) : ↥C ⧸ N₁) = ((Subgroup.inclusion hYC ⟨z, hzY⟩ : ↥C) : ↥C ⧸ N₁)
    congr 1
    exact Subtype.ext h.sq₂
  have hall := twin_section_dichotomy hp hq hBelow hlt hS hA3 hA4 hne hzA3 hzA4 hstar ι hι
    (g₂ : ↥C ⧸ N₁) ha (hactJ hK₃Ω hu₂K₃) (hactJ hK₄Ω hu₂K₄) ha2
  have hOY : oddCoreOf Y ≤ oddCoreOf C :=
    le_oddCoreIn_of_normalizes ((oddCoreOf_le_self Y).trans hYC) (fun g hg => hOnorm g hg)
      (oddCoreOf_odd_natCard _)
  have hzC : z ∈ C := hYC hzY
  have hcomm : ∀ g ∈ C, ⁅g, z⁆ ∈ oddCoreOf Y := by
    intro g hg
    have hgK₃ : conjSub g K₃ ∈ tqMembers Ω u := conjSub_mem_tqMembers hΩ.conjInvariant hg hK₃Ω
    have hzg : IsUniqueInvolution (conjSub g K₃) (g * z * g⁻¹) := hzK₃.conj g
    have hzgc : g * z * g⁻¹ ∈ exactCore u (conjSub g K₃) :=
      (T7H.isUniqueInvolution_exactCore hp hΩ hcpg hgK₃ hzg).mem
    have hzgY : g * z * g⁻¹ ∈ Y := exactCore_le_exactLayer hgK₃ hzgc
    have hB := hall _ (T7H.exactImg_mem hgK₃)
    have hB' := T7H.exactImg_isUnique hp hΩ hcpg hgK₃ hzg hzgY
    have heq : T7H.toBar Ω u z hzY = T7H.toBar Ω u (g * z * g⁻¹) hzgY := hB.eq hB'
    have hmem : (⟨z, hzY⟩ : ↥Y)⁻¹ * ⟨g * z * g⁻¹, hzgY⟩ ∈ N₀ := QuotientGroup.eq.mp heq
    have hmemG : z⁻¹ * (g * z * g⁻¹) ∈ oddCoreOf Y := ⟨_, hmem, rfl⟩
    have hconj := mem_normalizer_oddCoreOf_of_mem_normalizer (Subgroup.le_normalizer hzY) hmemG
    have e : z * (z⁻¹ * (g * z * g⁻¹)) * z⁻¹ = ⁅g, z⁆ := by
      simp only [commutatorElement_def]
      group
    rwa [e] at hconj
  refine Subgroup.mem_map.mpr ⟨⟨z, hzC⟩, ?_, rfl⟩
  rw [Subgroup.mem_comap, Subgroup.mem_center_iff]
  intro q
  induction q using QuotientGroup.induction_on with
  | H g =>
    have hc : ⁅(g : G), z⁆ ∈ oddCoreOf C := hOY (hcomm g g.2)
    obtain ⟨hcC, hco⟩ := mem_oddCoreOf_iff.mp hc
    have h1 : QuotientGroup.mk' (classicalInvolutionOddCore ↥C)
        (g * ⟨z, hzC⟩ * g⁻¹ * ⟨z, hzC⟩⁻¹) = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hco
    have h1' : ⁅QuotientGroup.mk' (classicalInvolutionOddCore ↥C) g,
        QuotientGroup.mk' (classicalInvolutionOddCore ↥C) ⟨z, hzC⟩⁆ = 1 := by
      rw [commutatorElement_def]
      simpa only [map_mul, map_inv] using h1
    exact commutatorElement_eq_one_iff_mul_comm.mp h1'

end Main

end S22

end CFSG.ClassicalInvolution.Asc77
