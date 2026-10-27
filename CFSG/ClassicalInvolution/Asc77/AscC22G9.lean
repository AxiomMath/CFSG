module

public import CFSG.ClassicalInvolution.Asc77.AscC22G5
public import CFSG.ClassicalInvolution.Asc77.AscC22G8
public import CFSG.ClassicalInvolution.Asc77.WP3FrameChain

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Disconnected AscE184Sect
open scoped commutatorElement

namespace C22G

set_option linter.unusedSectionVars false

section Conn

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}

theorem dstarConnected_quot_congr {Φ Φ' : Set (Subgroup G)} {Y Y' : Subgroup G} (hΦ : Φ = Φ')
    (hY : Y = Y')
    (h : T3.DStarConnected (quotFamily (restrictFamily Φ Y) (classicalInvolutionOddCore ↥Y))) :
    T3.DStarConnected (quotFamily (restrictFamily Φ' Y') (classicalInvolutionOddCore ↥Y')) := by
  subst hΦ hY
  exact h

theorem sectionConnected_of_layer (hΩ : HypOmegaMod p f Ω)
    (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    (h : T3.DStarConnected (oddQuotientFamily (exactPair Ω c))) : SectionConnected Ω c :=
  dstarConnected_quot_congr (sectionFamily_zpowers hΩ hc2).symm (sectionHull_zpowers hΩ hc2).symm h

end Conn

section Main

variable {p f : ℕ} [Fact p.Prime]


theorem third_mem_tqMembers {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]
    {Ω : Set (Subgroup G)} {K K' K₃ : Subgroup G} {z u₁ u₂ u₃ : G}
    (hs : Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃) : K₃ ∈ tqMembers Ω (u₁ * u₂) := by
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hKΩ : K ∈ Ω := hs.stand.mem
  have hK'Ω : K' ∈ Ω := hs.hK'.1
  have hK₃Ω : K₃ ∈ Ω := hs.hK₃.1
  have hu₁K₃ : u₁ ∈ trivialOnQuot K₃ :=
    T7J.twin_le_trivialOnQuot hΩ hKΩ hK₃Ω hs.hK₃K.symm hs.hz hs.hzK₃ hs.hu₁.1
  have hu₂K₃ : u₂ ∈ trivialOnQuot K₃ :=
    T7J.twin_le_trivialOnQuot hΩ hK'Ω hK₃Ω hs.hK₃K'.symm hs.hzK' hs.hzK₃ hs.hu₂.1
  exact ⟨hK₃Ω, Subgroup.mul_mem _ hu₁K₃ hu₂K₃⟩

theorem sectionConnected_of_hyp22 (h4 : Hyp22FourTwins p f) (hF : Hyp22Fuse p f)
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)}
    {K K' K₃ : Subgroup G} {z u₁ u₂ u₃ : G} (h : Hyp22 p f Ω K K' K₃ z u₁ u₂ u₃) :
    SectionConnected Ω (u₁ * u₂) := by
  have hs := h.setting
  have hp : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hKΩ : K ∈ Ω := hs.stand.mem
  have hK'Ω : K' ∈ Ω := hs.hK'.1
  have hK₃Ω : K₃ ∈ Ω := hs.hK₃.1
  have hz : IsUniqueInvolution K z := hs.hz
  have hzK₃ : IsUniqueInvolution K₃ z := hs.hzK₃
  have hc2 : (u₁ * u₂) * (u₁ * u₂) = 1 := hs.sq_12
  have hc1 : u₁ * u₂ ≠ 1 :=
    (T7S22.mul_ne_one_of_twins hΩ hKΩ hK'Ω hs.hne.symm hz hs.hu₁.1 hs.hu₂.1 hs.hu₂.2).1
  have hMz : IsClassicalMember p f K₃ z := isClassicalMember_of_twin hΩ hK₃Ω hzK₃
  have hnc : ¬ ({u₁ * u₂} : Set G) ⊆ Subgroup.center G :=
    Balance.not_subset_center_of_ne_one (exists_noncomm_of_isClassicalMember hMz) hc1
  have hcA : IsPGroup 2 (Subgroup.zpowers (u₁ * u₂)) := isPGroup_zpowers_of_sq_eq_one hc2
  have hL : LayerOrthType p f Ω (u₁ * u₂) 6 (piSign p f) := c22_8X_layer_of_inputs h4 hF h
  exact sectionConnected_of_layer hΩ hcA
    (layer_dstarConnected hp hq hΩ hs.stand.aEmpty hc2 hnc hL)

theorem layerStar_of_alpha (h4 : Hyp22FourTwins p f) (hF : Hyp22Fuse p f)
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)}
    {K K' K₃ : Subgroup G} {z u₁ u₂ u₃ : G} (h : Hyp22 p f Ω K K' K₃ z u₁ u₂ u₃)
    (hα : alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) = ⊥) :
    ∀ J ∈ tqMembers Ω (u₁ * u₂), J ∈ dstarComp Ω K := by
  have hs := h.setting
  have hp : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hKΩ : K ∈ Ω := hs.stand.mem
  have hK'Ω : K' ∈ Ω := hs.hK'.1
  have hz : IsUniqueInvolution K z := hs.hz
  have hc2 : (u₁ * u₂) * (u₁ * u₂) = 1 := hs.sq_12
  have hc1 : u₁ * u₂ ≠ 1 :=
    (T7S22.mul_ne_one_of_twins hΩ hKΩ hK'Ω hs.hne.symm hz hs.hu₁.1 hs.hu₂.1 hs.hu₂.2).1
  have hconn : SectionConnected Ω (u₁ * u₂) := sectionConnected_of_hyp22 h4 hF h
  have hK₃t : K₃ ∈ tqMembers Ω (u₁ * u₂) := third_mem_tqMembers hs
  have hK₃d : K₃ ∈ dstarComp Ω K := AscE186.mem_dstarComp_of_twin hp hΩ hKΩ hs.hK₃
  have hdK : dstarComp Ω K₃ = dstarComp Ω K := T7A.dstarComp_eq_of_mem hKΩ hK₃d
  intro M hM
  obtain ⟨n, hn, J', hJ't, hJ'd, rfl⟩ :=
    exists_conj_tqMembers_of_connected hp hq hΩ hc2 hK₃t hconn M hM
  rw [hdK] at hJ'd
  have hzA : z ∈ Subgroup.closure ({u₁ * u₂, z} : Set G) := Subgroup.subset_closure (by simp)
  have huA : u₁ * u₂ ∈ Subgroup.closure ({u₁ * u₂, z} : Set G) :=
    Subgroup.subset_closure (by simp)
  have hle := commutator_oddCore_le_alphaOf hc1 (Subgroup.closure ({u₁ * u₂, z} : Set G)) huA
  rw [hα] at hle
  have hmem : ⁅n, z⁆ ∈ ⁅oddCoreOf (Subgroup.centralizer ({u₁ * u₂} : Set G)),
      Subgroup.closure ({u₁ * u₂, z} : Set G)⁆ := Subgroup.commutator_mem_commutator hn hzA
  have hnz : n * z = z * n :=
    commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp (hle hmem))
  have hnzn : n * z * n⁻¹ = z := by
    calc n * z * n⁻¹ = (z * n) * n⁻¹ := by rw [hnz]
      _ = z := by group
  have hKn : conjSub n K ∈ twinSet Ω K :=
    ⟨hΩ.conjInvariant n K hKΩ, z, hz, hnzn ▸ hz.conj n⟩
  have hnN : n ∈ sigmaStarNorm Ω K :=
    T7A.mem_sigmaStarNorm_of_conj hΩ.conjInvariant hKΩ
      (AscE186.mem_dstarComp_of_twin hp hΩ hKΩ hKn)
  exact ((mem_sigmaStarNorm_iff.mp hnN) J').mp hJ'd

theorem c22_layerStar_of_alpha (h4 : Hyp22FourTwins p f) (hF : Hyp22Fuse p f) (h7 : C22_7 p f) :
    C22_layerStar p f := by
  intro G _ _ _ Ω K K' K₃ z u₁ u₂ u₃ h
  exact layerStar_of_alpha h4 hF h (h7 G Ω K K' K₃ z u₁ u₂ u₃ h)

end Main

end C22G

end CFSG.ClassicalInvolution.Asc77
