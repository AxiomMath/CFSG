module

public import CFSG.ClassicalInvolution.Asc77.AscC22G9

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Disconnected

namespace C22G

set_option linter.unusedSectionVars false

section Named

variable (p f : ℕ) [Fact p.Prime]

@[expose] def C22_layerNormAlpha : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' K₃ : Subgroup G) (z u₁ u₂ u₃ : G), Hyp22 p f Ω K K' K₃ z u₁ u₂ u₃ →
      rLayer Ω (u₁ * u₂) ≤
        Subgroup.normalizer (alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) : Set G)

end Named

section Reduction

variable {p f : ℕ} [Fact p.Prime]


theorem c22_7_trans_of_layerNormAlpha (h2 : C22_2 p f) (hY : C22_layerNormAlpha p f) :
    C22_7_trans p f := by
  intro G _ _ _ Ω K K' K₃ z u₁ u₂ u₃ h _ J hJ
  have hs := h.setting
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hKΩ : K ∈ Ω := hs.stand.mem
  have hz : IsUniqueInvolution K z := hs.hz
  have hCz := h.centralizer_le_normalizer_alpha h2
  have hVK : ∀ M ∈ twinSet Ω K,
      M ≤ Subgroup.normalizer (alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) : Set G) :=
    fun M hM m hm => hCz (by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact ((isUniqueInvolution_of_mem_twinSet hz hM).commute_of_mem hm).symm)
  have hgen : genGroup Ω K (u₁ * u₂) ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) : Set G) :=
    sup_le (iSup₂_le hVK) (hY G Ω K K' K₃ z u₁ u₂ u₃ h)
  obtain ⟨w, hw, y, hy, hyw⟩ := exists_conj_of_mem_dstarComp hs J hJ
  have hJΩ : J ∈ Ω := (T3.mem_dstarComp_symm hKΩ hJ).1
  have hM₀ : conjSub y⁻¹ J ∈ twinSet Ω K := conjSub_mem_twinSet hΩ.conjInvariant hz hJΩ hw hyw
  obtain ⟨g, hg⟩ := hs.stand.trans (conjSub y⁻¹ J) hM₀.1
  have hgz : g * z * g⁻¹ = z := by
    have h1 := hz.conj g
    rw [hg] at h1
    exact (isUniqueInvolution_of_mem_twinSet hz hM₀).eq h1 |>.symm
  have hgC : g ∈ Subgroup.centralizer ({z} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g * z = (g * z * g⁻¹) * g := by group
      _ = z * g := by rw [hgz]
  refine ⟨y * g, Subgroup.mul_mem _ (hgen hy) (hCz hgC), ?_⟩
  rw [conjSub_mul, hg, conjSub_conjSub_inv]

theorem c22_7_cent_of_layerNormAlpha (h4 : Hyp22FourTwins p f) (hF : Hyp22Fuse p f)
    (h2 : C22_2 p f) (hY : C22_layerNormAlpha p f) : C22_7_cent p f := by
  intro G _ _ _ Ω K K' K₃ z u₁ u₂ u₃ h hμ c hc
  have hs := h.setting
  have hp : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hKΩ : K ∈ Ω := hs.stand.mem
  have hK'Ω : K' ∈ Ω := hs.hK'.1
  have hz : IsUniqueInvolution K z := hs.hz
  have hzK' : IsUniqueInvolution K' z := hs.hzK'
  have hc2 : (u₁ * u₂) * (u₁ * u₂) = 1 := hs.sq_12
  have hc1 : u₁ * u₂ ≠ 1 :=
    (T7S22.mul_ne_one_of_twins hΩ hKΩ hK'Ω hs.hne.symm hz hs.hu₁.1 hs.hu₂.1 hs.hu₂.2).1
  have hCz := h.centralizer_le_normalizer_alpha h2
  have htrK := c22_7_trans_of_layerNormAlpha h2 hY G Ω K K' K₃ z u₁ u₂ u₃ h hμ
  have hconn : SectionConnected Ω (u₁ * u₂) := sectionConnected_of_hyp22 h4 hF h
  have hK₃t : K₃ ∈ tqMembers Ω (u₁ * u₂) := third_mem_tqMembers hs
  have hK₃d : K₃ ∈ dstarComp Ω K := AscE186.mem_dstarComp_of_twin hp hΩ hKΩ hs.hK₃
  have hdK : dstarComp Ω K₃ = dstarComp Ω K := T7A.dstarComp_eq_of_mem hKΩ hK₃d
  have hcK₃ : conjSub c K₃ ∈ tqMembers Ω (u₁ * u₂) :=
    conjSub_mem_tqMembers hΩ.conjInvariant hc hK₃t
  obtain ⟨n, hn, J', hJ't, hJ'd, hJ'eq⟩ :=
    exists_conj_tqMembers_of_connected hp hq hΩ hc2 hK₃t hconn _ hcK₃
  rw [hdK] at hJ'd
  obtain ⟨x₁, hx₁, hx₁eq⟩ := htrK J' hJ'd
  have hu₁z : u₁ * z = z * u₁ := (hz.commute_of_mem hs.hu₁.1).symm
  have hu₂z : u₂ * z = z * u₂ := (hzK'.commute_of_mem hs.hu₂.1).symm
  have huz : (u₁ * u₂) * z = z * (u₁ * u₂) := by
    calc (u₁ * u₂) * z = u₁ * (u₂ * z) := by group
      _ = u₁ * (z * u₂) := by rw [hu₂z]
      _ = (u₁ * z) * u₂ := by group
      _ = (z * u₁) * u₂ := by rw [hu₁z]
      _ = z * (u₁ * u₂) := by group
  have hnN := oddCoreOf_centralizer_le_normalizer_alphaOf hz.sq hc1 huz hn
  obtain ⟨c₃, hc₃⟩ := hs.stand.trans K₃ hs.hK₃.1
  have hc₃z : c₃ * z * c₃⁻¹ = z := by
    have h1 := hz.conj c₃
    rw [hc₃] at h1
    exact (hs.hzK₃.eq h1).symm
  have hc₃C : c₃ ∈ Subgroup.centralizer ({z} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc c₃ * z = (c₃ * z * c₃⁻¹) * c₃ := by group
      _ = z * c₃ := by rw [hc₃z]
  have hcK : conjSub (c * c₃) K = conjSub (n * x₁) K := by
    rw [conjSub_mul, hc₃, hJ'eq, conjSub_mul, hx₁eq]
  have hdK' : conjSub ((n * x₁)⁻¹ * (c * c₃)) K = K := by
    rw [conjSub_mul, hcK, conjSub_inv_conjSub]
  have hdz : ((n * x₁)⁻¹ * (c * c₃)) * z * ((n * x₁)⁻¹ * (c * c₃))⁻¹ = z := hz.conj_eq hdK'
  have hdC : (n * x₁)⁻¹ * (c * c₃) ∈ Subgroup.centralizer ({z} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc ((n * x₁)⁻¹ * (c * c₃)) * z
        = (((n * x₁)⁻¹ * (c * c₃)) * z * ((n * x₁)⁻¹ * (c * c₃))⁻¹) *
            ((n * x₁)⁻¹ * (c * c₃)) := by group
      _ = z * ((n * x₁)⁻¹ * (c * c₃)) := by rw [hdz]
  have hce : c = (n * x₁) * ((n * x₁)⁻¹ * (c * c₃)) * c₃⁻¹ := by group
  rw [hce]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hnN hx₁) (hCz hdC))
    (Subgroup.inv_mem _ (hCz hc₃C))

theorem c22_7_of_layerNormAlpha (hE : ThmEWithSylow p f) (h4 : Hyp22FourTwins p f)
    (hF : Hyp22Fuse p f) (h2 : C22_2 p f) (hμ : C22_4 p f) (hY : C22_layerNormAlpha p f) :
    C22_7 p f :=
  c22_7_of hE h2 hμ (c22_7_trans_of_layerNormAlpha h2 hY)
    (c22_7_cent_of_layerNormAlpha h4 hF h2 hY)

end Reduction

end C22G

end CFSG.ClassicalInvolution.Asc77
