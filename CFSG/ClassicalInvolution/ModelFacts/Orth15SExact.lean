module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15STrans
public import CFSG.ClassicalInvolution.AschTight.Sec6Gen64Ex
public import CFSG.ClassicalInvolution.ModelFacts.Orth15SOrbit

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen

section Exact

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}

theorem aEmpty_exactPair (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hA : ∀ M ∈ Ω, AEmpty Ω M) (hc2 : IsPGroup 2 (Subgroup.zpowers c)) :
    ∀ L ∈ restrictFamily (centralizingMembers (exactFamily Ω c) {c}) (exLayer Ω c),
      AEmpty (restrictFamily (centralizingMembers (exactFamily Ω c) {c}) (exLayer Ω c)) L := by
  have hΛ : HypOmegaMod p f
      (restrictFamily (centralizingMembers (exactFamily Ω c) {c}) (exLayer Ω c)) :=
    hypOmegaMod_restrictFamily_congr (centMembers_exactFamily Ω c).symm rfl
      (hypOmegaMod_exactPair hp hq hΩ hc2)
  have hΛg : HypOmegaGen
      (restrictFamily (centralizingMembers (exactFamily Ω c) {c}) (exLayer Ω c)) :=
    hypOmegaGen_of_mod hp hq hΛ
  rintro K₁ hK₁ J₁ hJs hJn zK zJ hzK hzJ
  have hK₁' := hK₁
  have hJ₁' := hJs.1
  obtain ⟨Kc, hKc, hKcY, rfl⟩ := hK₁
  obtain ⟨Jc, hJc, hJcY, rfl⟩ := hJs.1
  obtain ⟨⟨K, hK, rfl⟩, -⟩ := hKc
  obtain ⟨⟨J, hJ, rfl⟩, -⟩ := hJc
  obtain ⟨u, v, R, T, hcfg⟩ := exists_cfg64 hΛg hK₁' hJ₁' hzK hzJ hJs hJn
  have hcfgG := cfg64_of_exact hp hq hΩ hc2 hK hJ hcfg
  have hstar : J ∈ omegaStarNbr Ω K :=
    ⟨hJ.1, hcfgG.hKJ.symm, Subgroup.zpowers (v : G), hcfgG.hV, hcfgG.hVJ,
      hcfgG.symm.U_le_normalizer⟩
  obtain ⟨g, hg, hgK⟩ := hA K hK.1 J hstar hcfgG.notJ (zK : G) (zJ : G) hcfgG.hz hcfgG.hj
  obtain ⟨ρ, hρ, hρK⟩ := exists_mem_sup_conj_of_cfg64 hcfgG hg hgK
  rw [← Subgroup.map_sup] at hρ
  obtain ⟨ρ₁, hρ₁, rfl⟩ := hρ
  refine ⟨ρ₁, sup_le hcfg.R_le_Y hcfg.T_le_Y hρ₁, ?_⟩
  have hρc : (ρ₁ : G) ∈ Subgroup.centralizer ({c} : Set G) :=
    exactLayer_le_centralizer Ω c ρ₁.2
  have e : (ρ₁ : G) * c * (ρ₁ : G)⁻¹ = c := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp hρc]
    group
  have h1 := exactCore_conjSub (ρ₁ : G) c K
  rw [e] at h1
  have hρK' : conjSub (ρ₁ : G) K = J := hρK
  rw [hρK'] at h1
  rw [conjSub_subgroupOf (exLayer Ω c) ρ₁ (exactCore c K), ← h1]

end Exact

end CFSG.ClassicalInvolution.Asc77
