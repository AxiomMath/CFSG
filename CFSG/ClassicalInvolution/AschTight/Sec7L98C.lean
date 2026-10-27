module

public import Mathlib
public import CFSG.ClassicalInvolution.AschTight.Sec7L98B
public import CFSG.ClassicalInvolution.AschTight.Sec6GenTargets
public import CFSG.CharacterTheory.Semidihedral.CharacteristicSL2Layer
public import CFSG.ClassicalInvolution.Asc77.ThmEStatement
public import CFSG.ClassicalInvolution.AschTight.Sec19L98
public import CFSG.ClassicalInvolution.AschTight.Sec6Gen64H
public import CFSG.ClassicalInvolution.AschTight.Sec7L713M
public import CFSG.ClassicalInvolution.AschTight.Sec7L98A
public import CFSG.ClassicalInvolution.Balance.QNineFuzzyFree
public import CFSG.ClassicalInvolution.Balance.Theorem5Models
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalIsogeny
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Conj
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Roots
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherFactsL2Outer
public import CFSG.LocalAnalysis.ComponentClassification.BadTwoComponentSubgroup
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPreimages
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
public import CFSG.LocalAnalysis.SignalizerFunctor
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldPrimeOrderFixedSubfield
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OrderThreeNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PSLRangeCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinInvolutionCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinUDecomposition
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationEleven
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTen
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTenStructuralIdentities
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2FieldProjectionArithmetic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2OrderPSubgroupCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphReconstruction
public import Certificates.Certificate1
public import Certificates.Certificate10
public import Certificates.Certificate11
public import Certificates.Certificate12
public import Certificates.Certificate2
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate42
public import Certificates.Certificate44
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate8
public import Certificates.Certificate9

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Sec7

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable {G : Type} [Group G]

set_option hygiene false in
local notation "𝕌𝕍" => (Subgroup.zpowers u ⊔ Subgroup.zpowers v : Subgroup G)
set_option hygiene false in
local notation "𝕏𝕏" =>
  ((J ⊓ Subgroup.normalizer (K : Set G)) ⊔ (K ⊓ Subgroup.normalizer (J : Set G)) : Subgroup G)
set_option hygiene false in
local notation "𝕐𝕐" => (pairNormalizers K J z j)
set_option hygiene false in
local notation "ℤℤ" => (Subgroup.closure ({z, j} : Set G) : Subgroup G)

structure Tor98 (Ω : Set (Subgroup G)) (K J K' : Subgroup G) (z j u v : G) (R R' T : Subgroup G) :
    Prop where
  hΩ : HypOmegaGen Ω
  hK : K ∈ Ω
  hJ : J ∈ Ω
  hK' : K' ∈ Ω
  hz : IsUniqueInvolution K z
  hj : IsUniqueInvolution J j
  hzK' : IsUniqueInvolution K' z
  hne : K' ≠ K
  htw : twinSet Ω K = {K, K'}
  hzj : z ≠ j
  hU : Subgroup.zpowers u ∈ USet Ω
  hUK : Subgroup.zpowers u ≤ K
  hV : Subgroup.zpowers v ∈ USet Ω
  hVJ : Subgroup.zpowers v ≤ J
  hcomm : Commutes (Subgroup.zpowers u) (Subgroup.zpowers v)
  hR : IsSylow2In R K
  huR : Subgroup.zpowers u ≤ R
  hRN : R ≤ Subgroup.normalizer (𝕌𝕍 : Set G)
  hR' : IsSylow2In R' K'
  hR'N : R' ≤ Subgroup.normalizer (𝕌𝕍 : Set G)
  hT : IsSylow2In T J
  hvT : Subgroup.zpowers v ≤ T
  hTN : T ≤ Subgroup.normalizer (𝕌𝕍 : Set G)
  hXeq : 𝕏𝕏 = oddCoreOf 𝕏𝕏 ⊔ 𝕌𝕍
  hRY : ∀ R₀ : Subgroup G, IsSylow2In R₀ K → Subgroup.zpowers u ≤ R₀ →
    R₀ ≤ Subgroup.normalizer (𝕌𝕍 : Set G) → R₀ ≤ 𝕐𝕐
  hTY : T ≤ 𝕐𝕐
  hXY : 𝕏𝕏 ≤ 𝕐𝕐
  hYX : 𝕐𝕐 ≤ Subgroup.normalizer (𝕏𝕏 : Set G)
  hYZ : 𝕐𝕐 ≤ Subgroup.normalizer (ℤℤ : Set G)
  hR'Y : ∀ R₀ : Subgroup G, IsSylow2In R₀ K' → R₀ ≤ Subgroup.normalizer (𝕌𝕍 : Set G) → R₀ ≤ 𝕐𝕐
  hU' : ∃ u' : G, Subgroup.zpowers u' = R' ⊓ Subgroup.centralizer ({j} : Set G) ∧
    Subgroup.zpowers u' ∈ USet Ω ∧ 𝕌𝕍 = Subgroup.zpowers u' ⊔ Subgroup.zpowers v
  hcent : ∀ r ∈ R, r ∉ Subgroup.zpowers u → ∀ r' ∈ R', r' ∉ Subgroup.centralizer ({j} : Set G) →
    (∀ x ∈ 𝕌𝕍, (r * r') * x * (r * r')⁻¹ = x⁻¹) ∧
      𝕐𝕐 ⊓ Subgroup.centralizer (ℤℤ : Set G) = 𝕏𝕏 ⊔ Subgroup.zpowers (r * r')
  he1 : ∀ r ∈ R, r ∉ Subgroup.zpowers u → r * j * r⁻¹ = z * j
  he2 : ∀ t ∈ T, t ∉ Subgroup.zpowers v → t * z * t⁻¹ = z * j
  he3 : IsSylow2In (Subgroup.zpowers v) (J ⊓ Subgroup.centralizer ({z} : Set G))
  hf : 𝕐𝕐 ⊓ Subgroup.centralizer (𝕌𝕍 : Set G) ≤ 𝕏𝕏

namespace Cfg98

variable {Ω : Set (Subgroup G)} {K J K' X P : Subgroup G} {z j : G} {S : Sylow 2 G}
  {W : Subgroup G} (c : Cfg98 Ω K J K' X P z j S W)
include c

theorem R'_le_N_UV [Finite G] {u v : G} (hu : Subgroup.zpowers u = K ⊓ W)
    (hv : Subgroup.zpowers v = J ⊓ W) (hU' : K' ⊓ W ≤ 𝕌𝕍) :
    K' ⊓ (S : Subgroup G) ≤ Subgroup.normalizer (𝕌𝕍 : Set G) := by
  have hRW : K' ⊓ (S : Subgroup G) ≤ Subgroup.normalizer (W : Set G) :=
    c.le_normalizer_W c.hWS (mem_RSet_of_isSylow2In c.hK' c.sylow_R') inf_le_right
  have huKW : u ∈ K ⊓ W := hu ▸ Subgroup.mem_zpowers u
  have hvJW : v ∈ J ⊓ W := hv ▸ Subgroup.mem_zpowers v
  have hvR : v ∈ Subgroup.normalizer ((K' ⊓ (S : Subgroup G) : Subgroup G) : Set G) :=
    mem_normalizer_inf (c.V_le_N_K' hvJW) (Subgroup.le_normalizer (c.hWS hvJW.2))
  have hcomm : Commutes (Subgroup.zpowers u) (K' ⊓ (S : Subgroup G)) := by
    refine Sec6Gen.commutes_of_twin_of_isPGroup c.hΩ c.hK c.hK' c.hne.symm c.hz c.hzK'
      (hu ▸ inf_le_left) inf_le_left (S.isPGroup'.to_le (sup_le ?_ inf_le_right))
    rw [hu]
    exact inf_le_right.trans c.hWS
  refine le_normalizer_of_conjSub_le fun r hr => ?_
  rw [conjSub_sup_eq, AscL62.conjSub_zpowers_eq, AscL62.conjSub_zpowers_eq]
  refine sup_le ?_ ?_
  · rw [Subgroup.zpowers_le]
    apply Subgroup.mem_sup_left
    rw [show r * u * r⁻¹ = u by rw [← hcomm u (Subgroup.mem_zpowers u) r hr]; group]
    exact Subgroup.mem_zpowers u
  · rw [Subgroup.zpowers_le]
    have h1 : r * v * r⁻¹ * v⁻¹ ∈ K' ⊓ (S : Subgroup G) := by
      have h0 : v * r⁻¹ * v⁻¹ ∈ K' ⊓ (S : Subgroup G) :=
        (Subgroup.mem_normalizer_iff.mp hvR r⁻¹).mp (Subgroup.inv_mem _ hr)
      rw [show r * v * r⁻¹ * v⁻¹ = r * (v * r⁻¹ * v⁻¹) by group]
      exact Subgroup.mul_mem _ hr h0
    have h2 : r * v * r⁻¹ * v⁻¹ ∈ W :=
      W.mul_mem ((Subgroup.mem_normalizer_iff.mp (hRW hr) v).mp hvJW.2) (W.inv_mem hvJW.2)
    have h3 : r * v * r⁻¹ * v⁻¹ ∈ 𝕌𝕍 := hU' ⟨(Subgroup.mem_inf.mp h1).1, h2⟩
    rw [show r * v * r⁻¹ = (r * v * r⁻¹ * v⁻¹) * v by group]
    exact Subgroup.mul_mem _ h3 (Subgroup.mem_sup_right (Subgroup.mem_zpowers v))

theorem exists_tor [Finite G] (h64 : Sec6Gen.L6_4ThreeGenAll) :
    ∃ u v : G, ∃ T : Subgroup G, Subgroup.zpowers u = K ⊓ W ∧ Subgroup.zpowers v = J ⊓ W ∧
      Tor98 Ω K J K' z j u v (K ⊓ (S : Subgroup G)) (K' ⊓ (S : Subgroup G)) T := by
  have hUm := c.inf_W_mem c.hK c.two_lt_K
  have hVm := c.inf_W_mem c.hJ c.hJS
  have hU'm := c.inf_W_mem c.hK' c.two_lt_K'
  obtain ⟨-, -, -, -, -, -, hUc, -, -⟩ := Sec6Gen.exists_data_of_mem_USet c.hΩ hUm
  obtain ⟨-, -, -, -, -, -, hVc, -, -⟩ := Sec6Gen.exists_data_of_mem_USet c.hΩ hVm
  obtain ⟨u, hu⟩ := exists_zpowers_eq hUc
  obtain ⟨v, hv⟩ := exists_zpowers_eq hVc
  have hcomm : Commutes (Subgroup.zpowers u) (Subgroup.zpowers v) := by
    intro x hx y hy
    rw [hu] at hx
    rw [hv] at hy
    exact c.W_abelian x hx.2 y hy.2
  have huR : Subgroup.zpowers u ≤ K ⊓ (S : Subgroup G) := by
    rw [hu]
    exact inf_le_inf_left K c.hWS
  obtain ⟨T, hT, hvT, hTN⟩ := c.exists_T hu hv
  have hRN := c.R_le_N_UV hu hv
  have hUK : Subgroup.zpowers u ≤ K := hu ▸ inf_le_left
  have hVJ : Subgroup.zpowers v ≤ J := hv ▸ inf_le_left
  have hUU : Subgroup.zpowers u ∈ USet Ω := hu ▸ hUm
  have hVV : Subgroup.zpowers v ∈ USet Ω := hv ▸ hVm
  obtain ⟨⟨hXeq, hRTY⟩, ⟨hXY, hYX, hYZ, -⟩, ⟨Ks, hKs, htw', -, -, ⟨R₀, hR₀, hR₀N⟩, hall⟩,
    ⟨he1, he2, he3⟩, ⟨hf, -⟩⟩ := h64 G Ω c.hΩ K c.hK J c.hJ c.hA z j c.hz c.hj _ _ rfl rfl
      u v hUU hUK hVV hVJ hcomm (K ⊓ (S : Subgroup G)) T c.sylow_R hT huR hvT hRN hTN
  have hKsK' : Ks = K' := by
    have h1 : Ks ∈ twinSet Ω K := by rw [htw']; exact Or.inr rfl
    rw [c.htw] at h1
    rcases h1 with h | h
    · exact absurd h hKs
    · exact h
  subst hKsK'
  obtain ⟨-, ⟨u₀, hu₀, hu₀U, hUV₀⟩, -⟩ := hall R₀ hR₀ hR₀N
  have hU₀le : Subgroup.zpowers u₀ ≤ Ks ⊓ W := by
    refine le_inf ((hu₀ ▸ inf_le_left : Subgroup.zpowers u₀ ≤ R₀).trans hR₀.1) ?_
    have : Subgroup.zpowers u₀ ≤ Subgroup.zpowers u ⊔ Subgroup.zpowers v := hUV₀ ▸ le_sup_left
    refine this.trans (sup_le ?_ ?_)
    · rw [hu]; exact inf_le_right
    · rw [hv]; exact inf_le_right
  have hU₀eq : Subgroup.zpowers u₀ = Ks ⊓ W := by
    refine Subgroup.eq_of_le_of_card_ge hU₀le ?_
    rw [Sec6Gen.natCard_eq_of_mem_USet c.hΩ c.hK' hU'm hu₀U inf_le_left
      (hU₀le.trans inf_le_left)]
  have hU'UV : Ks ⊓ W ≤ Subgroup.zpowers u ⊔ Subgroup.zpowers v := by
    rw [← hU₀eq, hUV₀]
    exact le_sup_left
  have hR'N := c.R'_le_N_UV hu hv hU'UV
  obtain ⟨-, hU', hcent⟩ := hall (Ks ⊓ (S : Subgroup G)) c.sylow_R' hR'N
  refine ⟨u, v, T, hu, hv, ⟨c.hΩ, c.hK, c.hJ, c.hK', c.hz, c.hj, c.hzK', c.hne, c.htw, c.z_ne_j,
    hUU, hUK, hVV, hVJ, hcomm, c.sylow_R, huR, hRN, c.sylow_R', hR'N, hT, hvT, hTN, hXeq,
    ?_, hRTY.trans' le_sup_right, hXY, hYX, hYZ, fun R₁ hR₁ hR₁N => (hall R₁ hR₁ hR₁N).1, hU',
    hcent, he1, he2, he3, hf⟩⟩
  intro R₁ hR₁ huR₁ hR₁N
  have h := h64 G Ω c.hΩ K c.hK J c.hJ c.hA z j c.hz c.hj _ _ rfl rfl u v hUU hUK hVV hVJ hcomm
    R₁ T hR₁ hT huR₁ hvT hR₁N hTN
  exact le_sup_left.trans h.1.2

end Cfg98

end CFSG.ClassicalInvolution.Disconnected.AschTight.Sec7
