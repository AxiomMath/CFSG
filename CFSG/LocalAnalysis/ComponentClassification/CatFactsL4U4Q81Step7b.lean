module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4Q81Step7a
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitL219D
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitTypeStep
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.ClassicalInvolution.Models.LinearPairs
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7Cover
public import CFSG.ClassicalInvolution.SubnormalClosure
public import CFSG.ClassicalInvolution.WeakCT.Main
public import CFSG.GH74.Generic.Front.Final
public import CFSG.GH74.Generic.FrontEnd
public import CFSG.GH74.Generic.S1.LinFull
public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSLUnitary
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4Q81Step6
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4CoverCore
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitAschbacherCore
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitAschbacherOne
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLemma49Setup
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLemma49Tools
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitThm46
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB83Outer
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog516CL4
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma412
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma46d
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma47Count
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherAllInvolutionFourGroup
public import CFSG.Monster.B.TwoA.Unitary.Orbit1408Points
public import CFSG.Open.GeneralizedFittingSelfCentralizing
public import CFSG.RankThree.PartOne.LIT.RankMatrix
public import CFSG.Sporadic.Bridge.LyData
public import CFSG.Sporadic.Bridge.TableSurj
public import CFSG.Sporadic.HN.LevelChainSpec
public import CFSG.Sporadic.Ly.ActionBase
public import CFSG.Sporadic.Ly.CertificateBase
public import CFSG.Sporadic.Ly.FaithSpec
public import CFSG.Sporadic.Ly.OrbitSpec
public import CFSG.Sporadic.Ly.Simple
public import CFSG.Sporadic.LyBase
public import CFSG.Sporadic.McL
public import CFSG.Sporadic.Presentation.Ly
public import CFSG.Sporadic.Schreier.LyChain11
public import Certificates.Certificate3085Base
public import Certificates.Certificate7000
public import Certificates.Certificate7001
public import Certificates.Certificate7002
public import Certificates.Certificate7003
public import Certificates.Certificate7004
public import Certificates.Certificate7005
public import Certificates.Certificate7006
public import Certificates.Certificate7007
public import Certificates.Certificate7008
public import Certificates.Certificate7009
public import Certificates.Certificate7010
public import Certificates.Certificate7011
public import Certificates.Certificate9310
public import Certificates.Certificate9314

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup
open scoped commutatorElement

namespace Q81

variable {G : Type} [Group G] [Finite G]

abbrev conjAutOf {K : Subgroup G} {b : G} (hKb : K.map (MulAut.conj b).toMonoidHom = K) :
    MulAut ↥K :=
  (K.equivMapOfInjective (MulAut.conj b).toMonoidHom (MulAut.conj b).injective).trans
    (MulEquiv.subgroupCongr hKb)

omit [Finite G] in
theorem conjAutOf_apply {K : Subgroup G} {b : G} (hKb : K.map (MulAut.conj b).toMonoidHom = K)
    (k : ↥K) : ((conjAutOf hKb k : ↥K) : G) = b * k * b⁻¹ :=
  rfl

omit [Finite G] in
theorem fixedPoints_conjAutOf {K : Subgroup G} {b : G}
    (hKb : K.map (MulAut.conj b).toMonoidHom = K) :
    fixedPoints (conjAutOf hKb) = (K ⊓ centralizer {b}).subgroupOf K := by
  ext k
  rw [mem_fixedPoints, mem_subgroupOf, mem_inf, mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h1 : b * (k : G) * b⁻¹ = k := congrArg Subtype.val h
    refine ⟨k.2, ?_⟩
    calc (k : G) * b = b * k * b⁻¹ * b := by rw [h1]
      _ = b * k := by group
  · rintro ⟨-, h⟩
    apply Subtype.ext
    rw [conjAutOf_apply, ← h]
    group

theorem exists_component_isOfType (hO : pPrimeCore 2 G = ⊥) (hKG : SectionRank.IsKGroupCat G)
    {p : ℕ} {b : G} (hb : orderOf b = 2) {J : Subgroup G}
    (hJ : IsTwoComponentIn J (centralizer {b})) (hJt : IsOfType (HarrisF p) ↥J) :
    ∃ K : Subgroup G, IsComponent K ∧ IsOfType (HarrisF p) ↥K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hJq, Y₀, _, hY₀, ⟨eJ⟩⟩ := hJt
  obtain ⟨K, hK2, hcases, -⟩ := (harris82Lemma219Input_holds G b hb).2 J hJ
  have hKc : IsComponent K := (isTwoComponent_iff_isComponent hO K).mp hK2
  have hOK : pPrimeCore 2 ↥K = ⊥ := pPrimeCore_eq_bot_of_isSubnormal hO hKc.2
  have hZK : Open.fusionZStar ↥K = center ↥K := fusionZStar_eq_center_of_pPrimeCore_eq_bot hOK
  have hb2 : b * b = 1 := by rw [← sq, ← hb, pow_orderOf_eq_one]
  refine ⟨K, hKc, hK2.2, ?_⟩
  rcases hcases with ⟨hKb, hJK⟩ | ⟨hKb, hJeq⟩
  · by_cases hbK : b ∈ centralizer (K : Set G)
    ·
      have hKle : K ≤ centralizer {b} := fun k hk =>
        mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hbK k hk)
      rw [inf_eq_left.mpr hKle] at hJK
      have hK' : IsComponent (⊤ : Subgroup ↥K) :=
        ⟨LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm hKc.1, IsSubnormal.top⟩
      have hJKeq : J = K := by
        rcases LocalCores.component_subnormal_subgroup hK' hJK.2.1 with h | h
        · refine le_antisymm hJK.1 fun k hk => ?_
          have h1 : (⟨k, hk⟩ : ↥K) ∈ J.subgroupOf K := h (mem_top _)
          exact mem_subgroupOf.mp h1
        · exfalso
          have hc : ∀ x y : ↥J, x * y = y * x := by
            intro x y
            have h1 : ⁅(⟨x, hJK.1 x.2⟩ : ↥K), (⟨y, hJK.1 y.2⟩ : ↥K)⁆ ∈
                ⁅(⊤ : Subgroup ↥K), J.subgroupOf K⁆ :=
              commutator_mem_commutator (mem_top _) (show (⟨y, hJK.1 y.2⟩ : ↥K) ∈
                J.subgroupOf K from y.2)
            rw [h, mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
            have h2 : (x : G) * y = y * x := congrArg Subtype.val h1
            exact Subtype.ext h2
          have := ProperComplete.subsingleton_of_isPerfect_of_comm hJq.1 hc
          exact not_nontrivial ↥J (Cor441.nontrivial_of_isTwoQuasisimple hJq)
      subst hJKeq
      exact ⟨Y₀, inferInstance, hY₀, ⟨eJ⟩⟩
    ·
      set φ := conjAutOf hKb with hφ
      have hφ2 : φ * φ = 1 := by
        ext k
        rw [MulAut.mul_apply, MulAut.one_apply, conjAutOf_apply, conjAutOf_apply]
        calc b * (b * (k : G) * b⁻¹) * b⁻¹ = (b * b) * k * (b * b)⁻¹ := by group
          _ = k := by rw [hb2]; group
      have hφ1 : φ ≠ 1 := by
        intro h
        apply hbK
        rw [mem_centralizer_iff]
        intro k hk
        have h1 := congrArg (fun ψ : MulAut ↥K => ((ψ ⟨k, hk⟩ : ↥K) : G)) h
        simp only [MulAut.one_apply] at h1
        rw [conjAutOf_apply] at h1
        calc k * b = b * k * b⁻¹ * b := by rw [h1]
          _ = b * k := by group
      have hfix := fixedPoints_conjAutOf hKb
      have hJKl : J ≤ K := hJK.1.trans inf_le_left
      have hJA : J.subgroupOf K ≤ fixedPoints φ := by
        rw [hfix]
        intro k hk
        exact hJK.1 hk
      have hJs : ((J.subgroupOf K).subgroupOf (fixedPoints φ)).IsSubnormal := by
        rw [hfix]
        have hcomap : (J.subgroupOf K).subgroupOf ((K ⊓ centralizer {b}).subgroupOf K) =
            (J.subgroupOf (K ⊓ centralizer {b})).comap
              (subgroupOfEquivOfLe (inf_le_left : K ⊓ centralizer {b} ≤ K)).toMonoidHom := by
          ext x
          rfl
        rw [hcomap]
        exact hJK.2.1.comap _
      let eJK : ↥(J.subgroupOf K) ≃* ↥J := subgroupOfEquivOfLe hJKl
      have hJq' : IsTwoQuasisimple ↥(J.subgroupOf K) := isTwoQuasisimple_of_mulEquiv eJK.symm hJq
      obtain ⟨eZ⟩ := FooteLit.nonempty_quotient_fusionZStar_equiv eJK
      have hblow := isBlowup_of_fixed hKc.1 hφ2 hφ1 hJA hJs hJq' (eZ.trans eJ)
      exact ⟨↥K ⧸ center ↥K, inferInstance,
        InClosure.blowup hY₀ (hKG K (center ↥K) hKc.1.2.1) hblow,
        ⟨QuotientGroup.quotientMulEquivOfEq hZK⟩⟩
  ·
    obtain ⟨-, -, ψ, hψ⟩ := ((harris82Lemma219Input_holds G b hb).1 K hK2).2 hKb
    subst hJeq
    have : Group.IsPerfect ↥K := hK2.2.1
    have hYbot := pPrimeCore_quotient_pPrimeCore_eq_bot 2
      (G := ↥(centralizerResidual (K ⊔ K.map (MulAut.conj b).toMonoidHom) b))
    have hnt := LocalCores.isQuasisimple_nontrivial hJq.2
    have hYtop : pPrimeCore 2 (↥(centralizerResidual (K ⊔ K.map (MulAut.conj b).toMonoidHom) b) ⧸
        pPrimeCore 2 ↥(centralizerResidual (K ⊔ K.map (MulAut.conj b).toMonoidHom) b)) ≠ ⊤ := by
      rw [hYbot]
      exact bot_ne_top
    obtain ⟨e₁⟩ := GrSLit.nonempty_fusionZStar_equiv_of_surjective'
      (ψ.comp (QuotientGroup.mk' (pPrimeCore 2 ↥K))) (hψ.comp (QuotientGroup.mk'_surjective _))
      hK2.2.2 hYtop
    obtain ⟨e₂⟩ := GrSLit.nonempty_fusionZStar_equiv_of_quotient_equiv
      ((QuotientGroup.quotientMulEquivOfEq hYbot).trans QuotientGroup.quotientBot)
    exact ⟨Y₀, inferInstance, hY₀, ⟨(e₁.trans e₂).trans eJ⟩⟩

end Q81

end CFSG.ComponentClassification.HarrisLit
