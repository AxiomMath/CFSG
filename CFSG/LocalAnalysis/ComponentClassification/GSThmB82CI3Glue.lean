module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82CIUGlue
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82CI3Cfg
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82CI3Prod
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82CI3Red
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.ClassicalInvolution.Asc77.Lemma310
public import CFSG.ClassicalInvolution.Asc77.ThmEStatement
public import CFSG.ClassicalInvolution.Asc77.WP1Section18
public import CFSG.ClassicalInvolution.Asc77.WP1Section6
public import CFSG.ClassicalInvolution.Balance.QNineFuzzyFree
public import CFSG.ClassicalInvolution.Balance.Theorem5Models
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalIsogeny
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Conj
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Roots
public import CFSG.ClassicalInvolution.ModelFacts.Orth15D4Ord
public import CFSG.ClassicalInvolution.ModelFacts.Orth15Std
public import CFSG.ClassicalInvolution.Q3.Step
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.QuasiAssembly
public import CFSG.Foundations
public import CFSG.GH74.BNPair.Defs
public import CFSG.GH74.GLS.IVK.L2.Hilbert90Core
public import CFSG.GH74.GLS.IVK.L2.Lemma19c
public import CFSG.GH74.GLS.IVK.L2.SylowAux
public import CFSG.GH74.GLS.IVK.L2.Torus
public import CFSG.GH74.GLS.IVK.L2.TorusGeneral
public import CFSG.GH74.GLS.IVK.Prod.Basic
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsCentModel
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4AltCentB
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4CSLf
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OCLb
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OILf
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OILg
public import CFSG.LocalAnalysis.ComponentClassification.CatalogSchreierCases
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSporadicCasesC
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog82A10
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1C3Tools2
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3FGSolTop
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3Props
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1FourGroup
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitC3B
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitN36SporMult
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverModels
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedStdFamilies
public import CFSG.LocalAnalysis.ComponentClassification.TBLitCoreBasics
public import CFSG.LocalAnalysis.ComponentClassification.TBLitStepFour
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.Monster.B.TwoA.Base.FourNorm
public import CFSG.Monster.SteinbergMY443SimpleIsomorphism
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.B2Thompson
public import CFSG.Quasithin.Vol2.KGFactC31RuRef
public import CFSG.Quasithin.Vol2.KGFactC31RuRefBase
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import CFSG.Sporadic.HeldB.Common
public import CFSG.Sporadic.Schreier.LyFixedSet
public import CFSG.Sporadic.Schreier.TitsOther
public import CFSG.Sporadic.SuzOddCore.SmallActionData
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ConjugatedInvertedSubgroup
public import CFSG.Walter.J1
public import CFSG.YGroups.DCE.MaximalB
public import CFSG.YGroups.Y443.Native.Parabolic2CheckB
public import CFSG.YGroups.Y443.Native.Parabolic2CheckW
public import Certificates.Certificate10025
public import Certificates.Certificate7233Base
public import Certificates.Certificate8171
public import Certificates.Kernel.J4Count.FixC
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase
public import Certificates.Kernel.SporSch.J4S.NoCP

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open scoped MatrixGroups

namespace QPUJ

section General

variable {G : Type} [Group G] [Finite G]

theorem config63_of_component (hO : pPrimeCore 2 G = ⊥) {M : Subgroup G} (hM : IsComponent M)
    {P : Subgroup G} (hP : IsPGroup 2 P) (hPM : P ≤ normalizer (M : Set G))
    {L : Subgroup G} (hLM : L ≤ M) (hLC : L ≤ centralizer (P : Set G))
    (hLpc : IsPComponent 2 (L.subgroupOf (centralizer (P : Set G)))) (hLne : L ≠ M)
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hq3 : p = 3 ∧ f = 1)
    (hLLie : IsL4U4Mod4 (↥L ⧸ pPrimeCore 2 ↥L) p f)
    {t : G} (htL : t ∈ L) (ht2 : t * t = 1) (htZ : ∃ m ∈ M, m * t ≠ t * m)
    {J : Subgroup G} (hJM : J ≤ M) (hJC : J ≤ centralizer ({t} : Set G))
    (hJpc : IsPComponent 2 (J.subgroupOf (centralizer ({t} : Set G))))
    (hJLie : Blueprint.LieModel (↥J ⧸ pPrimeCore 2 ↥J) .PSL 2 p (2 * f))
    {J₀ : Subgroup G} (hJ₀L : J₀ ≤ L) (hJ₀J : J₀ ≤ J)
    (hJ₀ : J₀ ⊔ (pPrimeCore 2 ↥J).map J.subtype = J) :
    QPUJ6Config3 ↥M p f := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨hM.1, isPGroup_center_of_isComponent hO hM, hp, hp2, hf, hq3, ?_⟩
  set E : Subgroup (MulAut ↥M) :=
    (P.subgroupOf (normalizer (M : Set G))).map M.normalizerMonoidHom with hE
  have hE2 : IsPGroup 2 E := (hP.comap_subtype).map _
  have hfix : autFixed E = (M ⊓ centralizer (P : Set G)).subgroupOf M := by
    ext m
    rw [mem_autFixed, mem_subgroupOf, mem_inf]
    constructor
    · intro h
      refine ⟨m.2, mem_centralizer_iff.mpr fun β hβ => ?_⟩
      have h1 := h (M.normalizerMonoidHom ⟨β, hPM hβ⟩)
        (mem_map_of_mem _ (show (⟨β, hPM hβ⟩ : ↥(normalizer (M : Set G))) ∈
          P.subgroupOf (normalizer (M : Set G)) from mem_subgroupOf.mpr hβ))
      have h2 := congrArg Subtype.val h1
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at h2
      calc β * (m : G) = β * (m : G) * β⁻¹ * β := by group
        _ = (m : G) * β := by rw [h2]
    · rintro ⟨-, hmC⟩ e ⟨⟨β, hβN⟩, hβ, rfl⟩
      apply Subtype.ext
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
      show β * (m : G) * β⁻¹ = m
      rw [mem_centralizer_iff.mp hmC β (mem_subgroupOf.mp hβ)]
      group
  have hCt : centralizer ({(⟨t, hLM htL⟩ : ↥M)} : Set ↥M) =
      (M ⊓ centralizer ({t} : Set G)).subgroupOf M := by
    ext m
    rw [mem_centralizer_singleton_iff, mem_subgroupOf, mem_inf, mem_centralizer_singleton_iff]
    exact ⟨fun h => ⟨m.2, congrArg Subtype.val h⟩, fun h => Subtype.ext h.2⟩
  have htrans : ∀ {A D : Subgroup G}, A ≤ D → D ≤ M → IsPComponent 2 (A.subgroupOf D) →
      IsPComponent 2 ((A.subgroupOf M).subgroupOf (D.subgroupOf M)) := by
    intro A D hAD hDM hA
    have hAM := hAD.trans hDM
    rw [← OddStandard.Solomon75.isPComponent_subgroupOf_map_iff 2 M.subtype M.subtype_injective
      (fun x hx => mem_subgroupOf.mpr (hAD (mem_subgroupOf.mp hx))),
      map_subgroupOf_eq_of_le hAM, map_subgroupOf_eq_of_le hDM]
    exact hA
  have hquot : ∀ {A : Subgroup G}, A ≤ M →
      (↥A ⧸ pPrimeCore 2 ↥A) ≃* (↥(A.subgroupOf M) ⧸ pPrimeCore 2 ↥(A.subgroupOf M)) :=
    fun hAM => UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2
      (subgroupOfEquivOfLe hAM).symm
  refine ⟨E, L.subgroupOf M, ⟨t, hLM htL⟩, J.subgroupOf M, J₀.subgroupOf M, hE2, ?_, ?_, ?_,
    IsL4U4Mod4.of_mulEquiv (hquot hLM) hLLie, mem_subgroupOf.mpr htL, Subtype.ext ht2, ?_, ?_, ?_,
    OddQuot.lieModel_of_equiv (hquot hJM) hJLie,
    fun x hx => mem_subgroupOf.mpr (hJ₀L (mem_subgroupOf.mp hx)),
    fun x hx => mem_subgroupOf.mpr (hJ₀J (mem_subgroupOf.mp hx)), ?_⟩
  ·
    rw [hfix]
    intro l hl
    exact mem_subgroupOf.mpr (mem_inf.mpr ⟨l.2, hLC (mem_subgroupOf.mp hl)⟩)
  ·
    rw [hfix]
    exact htrans (le_inf hLM hLC) inf_le_left
      (OddStandard.Solomon75.isPComponent_subgroupOf_mono (le_inf hLM hLC) inf_le_right hLpc)
  ·
    intro h
    apply hLne
    refine le_antisymm hLM fun m hm => ?_
    have h1 : (⟨m, hm⟩ : ↥M) ∈ L.subgroupOf M := h ▸ mem_top _
    exact mem_subgroupOf.mp h1
  ·
    intro h
    obtain ⟨m, hmM, hm⟩ := htZ
    exact hm (congrArg Subtype.val (mem_center_iff.mp h ⟨m, hmM⟩))
  ·
    rw [hCt]
    intro j hj
    exact mem_subgroupOf.mpr (mem_inf.mpr ⟨j.2, hJC (mem_subgroupOf.mp hj)⟩)
  ·
    rw [hCt]
    exact htrans (le_inf hJM hJC) inf_le_left
      (OddStandard.Solomon75.isPComponent_subgroupOf_mono (le_inf hJM hJC) inf_le_right hJpc)
  ·
    apply map_injective M.subtype_injective
    have hcomp : M.subtype.comp (J.subgroupOf M).subtype =
        J.subtype.comp (subgroupOfEquivOfLe hJM).toMonoidHom := by
      ext x
      rfl
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le (hJ₀J.trans hJM), map_subgroupOf_eq_of_le hJM,
      map_map, hcomp, ← map_map, pPrimeCore_map_iso]
    exact hJ₀

end General

section Quotient

variable {Y : Type} [Group Y] [Finite Y]

local notation "π" => QuotientGroup.mk' (pPrimeCore 2 Y)

theorem le_and_equiv_or_config63 {M P K J JB : Subgroup Y} {t g w : Y} (hM : IsPComponent 2 M)
    (hP : IsPGroup 2 P) (hKC : K ≤ centralizer (P : Set Y))
    (hK : IsPComponent 2 (K.subgroupOf (centralizer (P : Set Y))))
    (hKM : K ≤ M ⊔ pPrimeCore 2 Y) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hq3 : p = 3 ∧ f = 1) (hKLie : IsL4U4Mod4 (↥K ⧸ pPrimeCore 2 ↥K) p f)
    (htK : t ∈ K) (ht2 : t * t = 1) (hgK : g ∈ K) (hgw : g⁻¹ * w * g = t) (hw2 : w * w = 1)
    (htw : t * w = w * t) (hwt : w ≠ t) (hJC : J ≤ centralizer ({t} : Set Y))
    (hJ : IsPComponent 2 (J.subgroupOf (centralizer ({t} : Set Y))))
    (hJLie : Blueprint.LieModel (↥J ⧸ pPrimeCore 2 ↥J) .PSL 2 p (2 * f))
    (hJBK : JB ≤ K) (hJBJ : JB ≤ J) (hJBp : ⁅JB, JB⁆ = JB) (hJB1 : JB ≠ ⊥)
    (hJB : JB ⊔ (pPrimeCore 2 ↥J).map J.subtype = J) :
    K ≤ M ∧ J ≤ M ∧ (Nonempty (↥M ⧸ pPrimeCore 2 ↥M ≃* ↥K ⧸ pPrimeCore 2 ↥K) ∨
      QPUJ6Config3 ↥(M.map π) p f) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hker : ¬ 2 ∣ Nat.card (π).ker := OddQuot.not_two_dvd_card_ker
  obtain ⟨Mb, hMb, hMs, hMbeq, -⟩ := id hM
  subst hMbeq
  have hsol : Group.IsSolvable (pPrimeCore 2 Y) :=
    CFSG.FeitThompson.isSolvable_of_odd_natCard _ OddQuot.odd_card_pPrimeCore
  have hKp : Group.IsPerfect ↥K := B5a.isPerfect_of_isPComponent_subgroupOf hKC hK
  have hJp : Group.IsPerfect ↥J := B5a.isPerfect_of_isPComponent_subgroupOf hJC hJ
  have hKM' : K ≤ M :=
    RankThree.GroupTheory.le_of_isPerfect_of_le_sup_of_isSubnormal hsol hMs hKp hKM
  have hKMb : K.map π ≤ M.map π := map_mono hKM'
  have hJBbp : ⁅JB.map π, JB.map π⁆ = JB.map π := by rw [← map_commutator, hJBp]
  have hJBb1 : JB.map π ≠ ⊥ := by
    intro h1
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h1
    exact hJB1 (Pump516.eq_bot_of_perfect_of_le_odd hJBp h1 OddQuot.odd_card_pPrimeCore)
  obtain ⟨hJbC, hJbpc⟩ :=
    Pump516.isPComponent_map_centralizer ⟨1, by rw [pow_one, pow_two, ht2]⟩ hJC hJ
  have hJBO : ¬ JB.map π ≤ (pPrimeCore 2 ↥(J.map π)).map (J.map π).subtype := by
    intro hle
    have hodd : Odd (Nat.card ↥((pPrimeCore 2 ↥(J.map π)).map (J.map π).subtype)) := by
      rw [card_map_of_injective (J.map π).subtype_injective]
      exact OddQuot.odd_card_pPrimeCore
    exact hJBb1 (Pump516.eq_bot_of_perfect_of_le_odd hJBbp hle hodd)
  have hJMb : J.map π ≤ M.map π := Pump516.le_of_isPComponent_of_perfect hJbC hJbpc hMb.2
    (map_mono hJBJ) ((map_mono hJBK).trans hKMb) hJBbp hJBO
  have hJM : J ≤ M := RankThree.GroupTheory.le_of_isPerfect_of_le_sup_of_isSubnormal hsol hMs
    hJp (Seven.le_sup_pPrimeCore_of_map_le hJMb)
  obtain ⟨eK⟩ := OddQuot.nonempty_quotient_pPrimeCore_equiv π hker K
  refine ⟨hKM', hJM, ?_⟩
  by_cases hKMeq : K.map π = M.map π
  · obtain ⟨eM⟩ := OddQuot.nonempty_quotient_pPrimeCore_equiv π hker M
    exact Or.inl ⟨eM.trans ((UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2
      (MulEquiv.subgroupCongr hKMeq.symm)).trans eK.symm)⟩
  refine Or.inr ?_
  have hO : pPrimeCore 2 (Y ⧸ pPrimeCore 2 Y) = ⊥ := pPrimeCore_quotient_pPrimeCore_eq_bot 2
  have hPM : P.map π ≤ normalizer ((M.map π : Subgroup (Y ⧸ pPrimeCore 2 Y)) :
      Set (Y ⧸ pPrimeCore 2 Y)) := by
    rintro _ ⟨β, hβ, rfl⟩
    refine Pump516.mem_normalizer_of_le_centralizer hMb ((map_mono hJBK).trans hKMb) hJBbp
      hJBb1 ?_
    rintro _ ⟨j, hj, rfl⟩
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      mem_centralizer_iff.mp (hKC (hJBK hj)) β hβ]
  have hLC : K.map π ≤ centralizer ((P.map π : Subgroup (Y ⧸ pPrimeCore 2 Y)) :
      Set (Y ⧸ pPrimeCore 2 Y)) := (map_mono hKC).trans (OddQuot.centralizer_map_eq hP).ge
  have hLpc := OddQuot.isPComponent_map π hker hKC hK
  rw [← OddQuot.centralizer_map_eq hP] at hLpc
  have ht2b : π t * π t = 1 := by rw [← map_mul, ht2, map_one]
  have htZ : ∃ m ∈ M.map π, m * π t ≠ π t * m := by
    refine ⟨π g, hKMb (mem_map_of_mem π hgK), fun h => hwt ?_⟩
    have h1 : π w = π t := by
      have h2 : π t = (π g)⁻¹ * π w * π g := by rw [← hgw, map_mul, map_mul, map_inv]
      calc π w = π g * ((π g)⁻¹ * π w * π g) * (π g)⁻¹ := by group
        _ = π g * π t * (π g)⁻¹ := by rw [← h2]
        _ = π t * π g * (π g)⁻¹ := by rw [h]
        _ = π t := by group
    exact OddQuot.injOn_of_isPGroup (Seven.isPGroup_closure_pair hw2 ht2 htw.symm)
      (subset_closure (by simp)) (subset_closure (by simp)) h1
  obtain ⟨eJ⟩ := OddQuot.nonempty_quotient_pPrimeCore_equiv π hker J
  have hJ₀ : JB.map π ⊔ (pPrimeCore 2 ↥(J.map π)).map (J.map π).subtype = J.map π := by
    have h1 : ((pPrimeCore 2 ↥J).map J.subtype).map π =
        (pPrimeCore 2 ↥(J.map π)).map (J.map π).subtype := OddQuot.map_oddCoreIn π hker J
    rw [← h1, ← Subgroup.map_sup, hJB]
  exact config63_of_component hO hMb (hP.map π) hPM hKMb hLC hLpc hKMeq hp hp2 hf hq3
    (IsL4U4Mod4.of_mulEquiv eK hKLie) (mem_map_of_mem π htK) ht2b htZ hJMb hJbC hJbpc
    (OddQuot.lieModel_of_equiv eJ hJLie) (map_mono hJBK) (map_mono hJBJ) hJ₀

end Quotient

end QPUJ

namespace Eight2

namespace CtxA0

variable {X : Type} [Group X] [Finite X] (c : CtxA0 X)

theorem exists_sl23_of_catalog (hS : SchreierFor Blueprint.Catalog) (hQ : CFQPUJ6Three)
    (hA : ¬ Nonempty (↥(generalizedFitting (c.s.h.subQuot c.s.y)) ≃* alternatingGroup (Fin 10)))
    (hq3 : c.s.p = 3 ∧ c.s.f = 1) :
    ∃ N : Subgroup X, N ≤ centralizer ({c.b} : Set X) ⊓
        centralizer ({c.s.h.a * c.b * c.Z.z} : Set X) ∧
      (N.subgroupOf (centralizer ({c.b} : Set X) ⊓
        centralizer ({c.s.h.a * c.b * c.Z.z} : Set X))).IsSubnormal ∧
      c.s.h.a * c.b * c.Z.z ∈ N ∧
      Nonempty (↥N ⧸ pPrimeCore 2 ↥N ≃* SL(2, ZMod 3)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨M, hMC, hMpc, hLM⟩ := c.exists_pComponent_le_sup hS
  have hLie : IsL4U4Mod4 (↥(Seven.Lay c.s.h c.s.y) ⧸ pPrimeCore 2 ↥(Seven.Lay c.s.h c.s.y))
      c.s.p c.s.f := c.lieModel_Lay hA
  set Y := centralizer ({c.b} : Set X) with hYdef
  have hKY : SectionRank.IsKGroupCat ↥Y := isKGroupCat_of_ne_top' c.s.kProper c.centralizer_b_ne_top
  have hbB0 : c.b ∈ c.s.h.secB0 c.s.y := c.hbB
  have hB0Y : c.s.h.secB0 c.s.y ≤ Y := c.secB0_le_centralizer_b
  have hCB0Y : centralizer (c.s.h.secB0 c.s.y : Set X) ≤ Y :=
    centralizer_le (Set.singleton_subset_iff.mpr hbB0)
  have hLY : Seven.Lay c.s.h c.s.y ≤ Y := c.s.Lay_le_centralizer.trans hCB0Y
  have haY : c.s.h.a ∈ Y := mem_centralizer_singleton_iff.mpr c.hba.symm
  have hbY : c.b ∈ Y := mem_centralizer_singleton_iff.mpr rfl
  have hzY : c.Z.z ∈ Y := mem_centralizer_singleton_iff.mpr c.hbz.symm
  set Jb := GSLit.fixedLayer c.s.h.J (zpowers c.b) with hJbdef
  have hJbC := c.Jb_le
  have hJbY : Jb ≤ Y := hJbC.trans inf_le_right
  obtain ⟨hJ0Jb, hJ0sup⟩ := c.J0_le_Jb
  have hJbty : IsSec8JType (↥Jb ⧸ pPrimeCore 2 ↥Jb) 3 1 := by
    obtain ⟨eJ⟩ := c.s.sec_J_equiv
    obtain ⟨eJb⟩ := QPUJ.nonempty_fixedLayer_quot_equiv (B5a.isQuasisimple_J c.s.h)
      c.zpowers_b_le_coreActionKernel c.isPGroup_zpowers_b
    have h1 := CatFactsL4U4.Cover82.isSec8JType_of_mulEquiv (eJ.trans eJb.symm) c.s.J_type
    rwa [hq3.1, hq3.2] at h1
  have hJbLie : Blueprint.LieModel (↥Jb ⧸ pPrimeCore 2 ↥Jb) .PSL 2 c.s.p (2 * c.s.f) := by
    rw [hq3.1, hq3.2]
    rcases hJbty with h1 | ⟨-, -, ⟨e6⟩⟩
    · exact h1
    · exact LieType.CurtisTits.lieModel_of_mulEquiv e6.symm
        Catalog82A10.lieModel_alternatingGroup_six
  have hJ0C := c.s.h.secJ0_le c.s.y
  have hJ0pc := Hyp52.isPComponent_secJ0 (h := c.s.h) (y := c.s.y)
  have hJ0p : ⁅c.s.h.secJ0 c.s.y, c.s.h.secJ0 c.s.y⁆ = c.s.h.secJ0 c.s.y :=
    Subgroup.isPerfect_iff.mp (B5a.isPerfect_of_isPComponent_subgroupOf hJ0C hJ0pc)
  have hJ01 : c.s.h.secJ0 c.s.y ≠ ⊥ := by
    intro hbot
    have := B5a.nontrivial_of_isPComponent_subgroupOf hJ0C hJ0pc
    rw [hbot] at this
    exact not_nontrivial _ this
  set a' : Y := ⟨c.s.h.a, haY⟩ with ha'
  set b' : Y := ⟨c.b, hbY⟩ with hb'
  set z' : Y := ⟨c.Z.z, hzY⟩ with hz'
  set g' : Y := ⟨c.s.t, hLY c.htL⟩ with hg'
  have hbZ : b' ∈ center Y := mem_center_iff.mpr fun w => Subtype.ext
    (mem_centralizer_singleton_iff.mp w.2)
  have hab2 : a' * b' * (a' * b') = 1 := Subtype.ext c.ab_mul_ab
  set P : Subgroup Y := (c.s.h.secB0 c.s.y).subgroupOf Y with hPdef
  have hP : IsPGroup 2 P := (c.s.h.isPGroup_secB0 c.s.y).comap_subtype
  have hCP : centralizer (P : Set Y) = (centralizer (c.s.h.secB0 c.s.y : Set X)).subgroupOf Y :=
    B5a.centralizer_subgroupOf hB0Y
  set K : Subgroup Y := (Seven.Lay c.s.h c.s.y).subgroupOf Y with hKdef
  have hKC : K ≤ centralizer (P : Set Y) := by
    rw [hCP]
    exact fun w hw => c.s.Lay_le_centralizer hw
  have hKpc : IsPComponent 2 (K.subgroupOf (centralizer (P : Set Y))) := by
    rw [hCP]
    exact (isPComponent_subgroupOf_subgroupOf_iff' hCB0Y 2 Nat.prime_two).mpr c.s.L_pc
  have htK : a' * b' ∈ K := c.ab_mem_Lay
  have hgK : g' ∈ K := c.htL
  have hgw : g'⁻¹ * z' * g' = a' * b' := Subtype.ext c.hzb
  have hz2 : z' * z' = 1 := Subtype.ext c.Z.hzz
  have htw : a' * b' * z' = z' * (a' * b') := Subtype.ext c.ab_comm_z
  have hwt : z' ≠ a' * b' := fun h1 => c.z_ne_ab (congrArg Subtype.val h1)
  set J : Subgroup Y := Jb.subgroupOf Y with hJdef
  have hCtY : (centralizer ({c.s.h.a} : Set X) ⊓ Y).subgroupOf Y =
      centralizer ({a' * b'} : Set Y) := by
    rw [QPUJ.centralizer_mul_of_mem_center hbZ]
    ext w
    simp only [mem_subgroupOf, mem_inf, SetLike.coe_mem, and_true,
      mem_centralizer_singleton_iff]
    exact ⟨fun h1 => Subtype.ext h1, fun h1 => congrArg Subtype.val h1⟩
  have hJC : J ≤ centralizer ({a' * b'} : Set Y) := by
    rw [← hCtY]
    exact fun w hw => hJbC hw
  have hJpc : IsPComponent 2 (J.subgroupOf (centralizer ({a' * b'} : Set Y))) := by
    rw [← hCtY]
    exact (isPComponent_subgroupOf_subgroupOf_iff' inf_le_right 2 Nat.prime_two).mpr
      c.isPComponent_Jb
  set JB : Subgroup Y := (c.s.h.secJ0 c.s.y).subgroupOf Y with hJBdef
  have hJ0L : c.s.h.secJ0 c.s.y ≤ Seven.Lay c.s.h c.s.y := Seven.J0_le_Lay c.s.h c.s.y
  have hJ0Y : c.s.h.secJ0 c.s.y ≤ Y := hJ0L.trans hLY
  have hJBK : JB ≤ K := fun w hw => hJ0L hw
  have hJBJ : JB ≤ J := fun w hw => hJ0Jb hw
  have hJBp : ⁅JB, JB⁆ = JB := by
    apply map_injective Y.subtype_injective
    rw [map_commutator, map_subgroupOf_eq_of_le hJ0Y, hJ0p]
  have hJB1 : JB ≠ ⊥ := by
    intro hbot
    apply hJ01
    have h1 : JB.map Y.subtype = c.s.h.secJ0 c.s.y := map_subgroupOf_eq_of_le hJ0Y
    rw [← h1, hbot, Subgroup.map_bot]
  have hJB : JB ⊔ (pPrimeCore 2 ↥J).map J.subtype = J := by
    apply map_injective Y.subtype_injective
    have hcomp : Y.subtype.comp J.subtype =
        Jb.subtype.comp (subgroupOfEquivOfLe hJbY).toMonoidHom := by
      ext x
      rfl
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hJ0Y, map_subgroupOf_eq_of_le hJbY, map_map,
      hcomp, ← map_map, pPrimeCore_map_iso]
    exact hJ0sup
  have hKM : K ≤ M.subgroupOf Y ⊔ pPrimeCore 2 ↥Y := by
    rw [← map_le_map_iff_of_injective Y.subtype_injective, Subgroup.map_sup,
      map_subgroupOf_eq_of_le hLY, map_subgroupOf_eq_of_le hMC]
    exact hLM
  have hKLie : IsL4U4Mod4 (↥K ⧸ pPrimeCore 2 ↥K) c.s.p c.s.f :=
    IsL4U4Mod4.of_mulEquiv (UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2
      (subgroupOfEquivOfLe hLY).symm) hLie
  have hJLie : Blueprint.LieModel (↥J ⧸ pPrimeCore 2 ↥J) .PSL 2 c.s.p (2 * c.s.f) :=
    OddQuot.lieModel_of_equiv (UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2
      (subgroupOfEquivOfLe hJbY)).symm hJbLie
  obtain ⟨hKM', hJM', hcase⟩ := QPUJ.le_and_equiv_or_config63 hMpc hP hKC hKpc hKM c.s.hp
    c.s.hp2 c.s.hf hq3 hKLie htK hab2 hgK hgw hz2 htw hwt hJC hJpc hJLie hJBK hJBJ hJBp hJB1 hJB
  have hLayM : Seven.Lay c.s.h c.s.y ≤ M := fun x hx => hKM' (show (⟨x, hLY hx⟩ : Y) ∈ K from hx)
  have hJbM : Jb ≤ M := fun x hx => hJM' (show (⟨x, hJbY hx⟩ : Y) ∈ J from hx)
  rcases hcase with heM | hconf
  ·
    obtain ⟨eM⟩ := heM
    have hLieM : IsL4U4Mod4 (↥M ⧸ pPrimeCore 2 ↥M) c.s.p c.s.f :=
      IsL4U4Mod4.of_mulEquiv ((UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2
        (subgroupOfEquivOfLe hMC).symm).trans (eM.trans
          (UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2
            (subgroupOfEquivOfLe hLY)))).symm hLie
    have hJbt : Jb ≤ centralizer ({c.s.h.a * c.b} : Set X) := by
      intro j hj
      obtain ⟨hja, hjb⟩ := mem_inf.mp (hJbC hj)
      have h1 : j * c.s.h.a = c.s.h.a * j := mem_centralizer_singleton_iff.mp hja
      have h2 : j * c.b = c.b * j := mem_centralizer_singleton_iff.mp hjb
      rw [mem_centralizer_singleton_iff]
      calc j * (c.s.h.a * c.b) = j * c.s.h.a * c.b := by group
        _ = c.s.h.a * (j * c.b) := by rw [h1]; group
        _ = c.s.h.a * c.b * j := by rw [h2]; group
    have hYt : M ⊓ centralizer ({c.s.h.a * c.b} : Set X) ≤
        centralizer ({c.s.h.a} : Set X) ⊓ Y := by
      intro m hm
      obtain ⟨hmM, hmab⟩ := mem_inf.mp hm
      have h1 : m * c.b = c.b * m := mem_centralizer_singleton_iff.mp (hMC hmM)
      have h2 : m * (c.s.h.a * c.b) = c.s.h.a * c.b * m := mem_centralizer_singleton_iff.mp hmab
      have h3 : m * c.s.h.a * c.b = c.s.h.a * m * c.b := by
        calc m * c.s.h.a * c.b = m * (c.s.h.a * c.b) := by group
          _ = c.s.h.a * c.b * m := h2
          _ = c.s.h.a * (c.b * m) := by group
          _ = c.s.h.a * (m * c.b) := by rw [h1]
          _ = c.s.h.a * m * c.b := by group
      exact mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr (mul_right_cancel h3), hMC hmM⟩
    have hLieM3 : Blueprint.LieModel (↥M ⧸ pPrimeCore 2 ↥M) .PSL 4 3 1 := by
      rcases hLieM with ⟨h1, -⟩ | ⟨-, h1⟩
      · rwa [hq3.1, hq3.2] at h1
      · rw [hq3.1, hq3.2] at h1
        norm_num at h1
    obtain ⟨N, hNX, hNs, habzN, ⟨eN⟩⟩ :=
      Seven.exists_sl23_of_l43 hLieM3 (hLayM c.ab_mem_Lay) c.ab_mul_ab c.ab_ne_one c.Z.hzz
        c.Z.hz1 c.ab_comm_z c.z_ne_ab hJbM hJbt hYt c.isPComponent_Jb hJbty
        (hJ0Jb (c.s.D_le_J0 c.Z.hzD))
    obtain ⟨-, -, hMs, -⟩ := id hMpc
    have h1 := Three.open_inf (Three.open_of_isSubnormal hMC hMs)
      (centralizer ({c.s.h.a * c.b * c.Z.z} : Set X))
    have h2 := Three.open_trans (Three.open_of_isSubnormal hNX hNs) h1
    exact ⟨N, le_inf (hNX.trans (inf_le_left.trans hMC)) (hNX.trans inf_le_right),
      Three.isSubnormal_of_open h2, habzN, ⟨eN⟩⟩
  ·
    exfalso
    have hKYb : SectionRank.IsKGroupCat (↥Y ⧸ pPrimeCore 2 ↥Y) :=
      OddQuot.isKGroupCat_of_surjective hKY _ (QuotientGroup.mk'_surjective _)
    have := hconf.1.2.1
    exact hQ _ c.s.p c.s.f hconf (SectionRank.catalog_of_isKGroupCat_of_surjective hKYb
      ((M.subgroupOf Y).map (QuotientGroup.mk' (pPrimeCore 2 ↥Y)))
      (QuotientGroup.mk' (center _)) (QuotientGroup.mk'_surjective _))

end CtxA0

end Eight2

theorem gs82Step6ThreeInputA0_of_catalog (hS : SchreierFor Blueprint.Catalog)
    (hCI : GSLit.ClassicalInvolutionInput) (hUc : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome)
    (hQ : CFQPUJ6Three) : GS82Step6ThreeInputA0 := by
  intro X _ _ c hA g hga hgz hp hf
  have := c.s.isSimpleGroup
  obtain ⟨N, hNX, hNs, hδN, ⟨eN⟩⟩ := c.exists_sl23_of_catalog hS hQ hA ⟨hp, hf⟩
  have hJt : IsSec8JType (↥c.s.h.J ⧸ pPrimeCore 2 ↥c.s.h.J) 3 1 := by
    obtain ⟨eJ⟩ := c.s.sec_J_equiv
    have h1 := CatFactsL4U4.Cover82.isSec8JType_of_mulEquiv eJ c.s.J_type
    rwa [hp, hf] at h1
  exact Eight2.false_of_sl23_conj hCI hUc c.s.nonab c.s.unbal c.s.notU c.s.h.orderOf_a hJt
    c.s.h.J_le c.s.J_normal (c.s.h.D_le_J c.Z.hzD) c.Z.hzz c.Z.hz1 hga hgz hNX hNs hδN eN

end CFSG.ComponentClassification.GSThmB
