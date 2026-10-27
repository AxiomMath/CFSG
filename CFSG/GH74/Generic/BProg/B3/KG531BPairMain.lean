module

public import CFSG.GH74.Generic.BProg.B3.KG531BPairAux
public import CFSG.GH74.Generic.BProg.B3.S1Lemma283bKGB
public import CFSG.GH74.Generic.BProg.B3.KG531RedAux
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87TwoA7OddLie
public import CFSG.Holt.General.ComponentsImage
public import CFSG.LocalAnalysis.ComponentClassification.PComponentNormalizerEnlargement
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBCentralQuotientDerived
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.Assembly.CompletedOddCoreElimination
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalIsogeny
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Chain
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Conj
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Roots
public import CFSG.ClassicalInvolution.ModelFacts.FundPerfectMain
public import CFSG.ClassicalInvolution.Models.LinearFrames.Frame
public import CFSG.ClassicalInvolution.Models.UnitaryPairs
public import CFSG.GH74.E2.ComponentsShape
public import CFSG.GH74.GLS.Bg.Iii2.L41Comp
public import CFSG.GH74.GLS.C3.Layer1.Th2V2Core
public import CFSG.GroupTheory.ElementaryAbelianBasis
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LieType.Ree.SmallReeInvolutionComponents
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneSpField
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafLieOrder
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddCentralFixed
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorOddE6
public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorInner
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTILinearSocle
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSLAllInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSUFieldOddCore
public import CFSG.LocalAnalysis.ComponentInitial.ProjectiveEigenspaceComponent
public import CFSG.LocalAnalysis.ComponentInitial.ProjectiveOrthogonalLocalComponentSplit
public import CFSG.LocalAnalysis.SectionRank.BruhatLift
public import CFSG.LocalAnalysis.SectionRank.EvenCover.LinearStep
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SLTwo
public import CFSG.LocalAnalysis.SectionRank.LargeReeCover
public import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl
public import CFSG.RankThree.PartOne.KC.OrthogonalFieldDescentCore
public import CFSG.RankThree.PartOne.KC.OrthogonalFieldDescentDisplayed
public import CFSG.RankThree.PartOne.KC.OrthogonalFieldDescentTags
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeOrbits
public import CFSG.RankThree.SteinbergR3EOrthogonalCoprimeCyclic
public import CFSG.Sporadic.Schreier.TitsOther
public import Certificates.Certificate5007

public section

namespace CFSG.GH74.Generic.BProg.B3

namespace KG531BP

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup
open CFSG.GH74.GLS.Stage2.Signalizer.Odd87
open scoped MatrixGroups

@[expose] def KG531BPairNine : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (M : Subgroup X), CFSG.IsQuasisimple ↥M →
    GHList (↥M ⧸ center ↥M) → pPrimeCore 2 ↥M = ⊥ → ∀ t ∈ M, orderOf t = 2 →
    ∀ L₁ L₂ : Subgroup X, IsPCompIn 2 (centralizer ({t} : Set X) ⊓ M) L₁ →
    IsPCompIn 2 (centralizer ({t} : Set X) ⊓ M) L₂ →
    ∀ s ∈ L₁, orderOf s = 2 → s ∈ (center ↥M).map M.subtype → t ∈ L₂ →
    ∀ (F : Type) [Field F] [Fintype F], Fintype.card F = 9 →
    Nonempty (↥L₁ ⧸ pPrimeCore 2 ↥L₁ ≃* SL(2, F)) →
    Nonempty (↥L₂ ⧸ pPrimeCore 2 ↥L₂ ≃* SL(2, F)) →
    pPrimeCoreOf 2 L₁ = ⊥ ∧ pPrimeCoreOf 2 L₂ = ⊥

@[expose] def KG531BPairOther : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (M : Subgroup X), CFSG.IsQuasisimple ↥M →
    GHList (↥M ⧸ center ↥M) → ¬ GHOddLie (↥M ⧸ center ↥M) → pPrimeCore 2 ↥M = ⊥ →
    ∀ (t : X) (htM : t ∈ M), orderOf t = 2 → (⟨t, htM⟩ : ↥M) ∉ center ↥M →
    ∀ L₁ L₂ : Subgroup X, IsPCompIn 2 (centralizer ({t} : Set X) ⊓ M) L₁ →
    IsPCompIn 2 (centralizer ({t} : Set X) ⊓ M) L₂ →
    ∀ s ∈ L₁, orderOf s = 2 → s ∈ (center ↥M).map M.subtype → t ∈ L₂ →
    ∀ (F : Type) [Field F] [Fintype F], Odd (Fintype.card F) → 5 ≤ Fintype.card F →
    Nonempty (↥L₁ ⧸ pPrimeCore 2 ↥L₁ ≃* SL(2, F)) →
    Nonempty (↥L₂ ⧸ pPrimeCore 2 ↥L₂ ≃* SL(2, F)) → False

theorem eq_top_of_pComponent_quasisimple {Q : Type*} [Group Q] [Finite Q] (hQ : IsQuasisimple Q)
    {J : Subgroup Q} (hJ : IsPComponent 2 J) : J = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hperf : Group.IsPerfect ↥J :=
    CFSG.ComponentClassification.CatalogueBHeldSmallCore.pComponent_perfect 2 J hJ
  obtain ⟨Kc, hKc, hsub, hmap, -⟩ := hJ
  rcases CFSG.LocalAnalysis.ComponentInitial.quasisimple_subnormal_subgroups hQ hsub with h | h
  · exact h
  · exfalso
    have : IsMulCommutative ↥J :=
      ⟨⟨fun a b => Subtype.ext ((Subgroup.mem_center_iff.mp (h a.2) (b : Q)).symm)⟩⟩
    have hss : Subsingleton ↥J := Group.IsPerfect.subsingleton_of_isMulCommutative
    have hJb : J = ⊥ := Subgroup.eq_bot_of_subsingleton J
    rw [hJb, Subgroup.map_bot] at hmap
    have hnt := CFSG.LocalCores.isQuasisimple_nontrivial hKc.1
    rw [← hmap] at hnt
    exact (Subgroup.nontrivial_iff_ne_bot _).1 hnt rfl

theorem isPComponent_image {K Q : Type} [Group K] [Group Q] [Finite K] [Finite Q] (κ : K →* Q)
    {u : Q} (hrange : κ.range = centralizer ({u} : Set Q)) {J : Subgroup K}
    (hJ : IsPComponent 2 J) (hJk : ¬ J ≤ ((QuotientGroup.mk' (center Q)).comp κ).ker) :
    J.map ((QuotientGroup.mk' (center Q)).comp κ) ≤
        centralizer ({QuotientGroup.mk' (center Q) u} : Set (Q ⧸ center Q)) ∧
      IsPComponent 2 ((J.map ((QuotientGroup.mk' (center Q)).comp κ)).subgroupOf
        (centralizer ({QuotientGroup.mk' (center Q) u} : Set (Q ⧸ center Q)))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (center Q) with hπ
  set ρ := π.comp κ with hρ
  set Cb := centralizer ({π u} : Set (Q ⧸ center Q)) with hCb
  have hmemC : ∀ k : K, κ k ∈ centralizer ({u} : Set Q) := fun k => hrange ▸ ⟨k, rfl⟩
  have hle : ρ.range ≤ Cb := KG531Red.range_le_centralizer κ hrange
  have hnorm : (ρ.range.subgroupOf Cb).Normal := by
    constructor
    intro n hn g
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨k, hk⟩ := hn
    obtain ⟨q, hq⟩ := QuotientGroup.mk'_surjective (center Q) (g : Q ⧸ center Q)
    have hgC : π q ∈ centralizer ({π u} : Set _) := by rw [hπ, hq]; exact g.2
    have h2 := KG531Red.conj_mem_centralizer hgC (hmemC k)
    rw [← hrange] at h2
    obtain ⟨k', hk'⟩ := h2
    refine ⟨k', ?_⟩
    simp only [hρ, MonoidHom.comp_apply, hk', map_mul, map_inv] at hk ⊢
    rw [hq, hk]
    rfl
  have hH : IsPComponent 2 (J.map ρ.rangeRestrict) :=
    CFSG.Holt.General.isPComponent_map ρ.rangeRestrict_surjective hJ
      (by rwa [MonoidHom.ker_rangeRestrict])
  have heq : (J.map ρ).subgroupOf ρ.range = J.map ρ.rangeRestrict := by
    ext ⟨x, hx⟩
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map]
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨j, hj, Subtype.ext rfl⟩
    · rintro ⟨j, hj, hjx⟩
      exact ⟨j, hj, congrArg Subtype.val hjx⟩
  have hJle : J.map ρ ≤ ρ.range := Subgroup.map_le_range ρ J
  refine ⟨hJle.trans hle, ?_⟩
  rw [CFSG.ComponentClassification.CatalogueBPrimeJoin.pComponent_subgroupOf_iff_of_subnormal hJle hle
    hnorm.isSubnormal, heq]
  exact hH

section OddLie


theorem bTwo_of_ghOddLie {S : Type} [Group S] [Finite S] (hZ : center S = ⊥) (h : GHOddLie S)
    {u : S} (hu : orderOf u = 2) : BTwo S u := by
  obtain ⟨p, f, hp, hf, h⟩ := h
  rcases h with ⟨hp2, hm | hm | hm | hm | hm | hm⟩ | ⟨hp2, -, hm⟩ | ⟨hp2, -, hm⟩ | ⟨h3, hm⟩ |
      ⟨h1, hm⟩ | hm
  · exact bTwo_psl hp hp2 (admissible_of_lieModel hm (by decide)) hm hZ hu
  · exact bTwo_psl hp hp2 (admissible_of_lieModel hm (by decide)) hm hZ hu
  · exact bTwo_psu hp hp2 (admissible_of_lieModel hm (by decide)) hm hZ hu
  · exact bTwo_psp hp hp2 (admissible_of_lieModel hm (by decide)) hm hZ hu
  · exact bTwo_g2 hp hp2 (admissible_of_lieModel hm (by decide)) hm hZ hu
  · exact bTwo_d4 hp hp2 (admissible_of_lieModel hm (by decide)) hm hZ hu
  · exact bTwo_psl hp hp2 (admissible_of_lieModel hm (by decide)) hm hZ hu
  · exact bTwo_psu hp hp2 (admissible_of_lieModel hm (by decide)) hm hZ hu
  · exact bTwo_psl hp (ne_two_of_pow_mod_four' hf (Or.inl h3))
      (admissible_of_lieModel hm (by decide)) hm hZ hu
  · exact bTwo_psu hp (ne_two_of_pow_mod_four' hf (Or.inr h1))
      (admissible_of_lieModel hm (by decide)) hm hZ hu
  · exact bTwo_ree Nat.prime_three (by norm_num) (admissible_of_lieModel hm (by decide)) hm hZ hu

theorem kg531BPair_of_parts (hOther : KG531BPairOther) (hNine : KG531BPairNine) : KG531BPair := by
  intro X _ _ M hM hGH hO t htM ht2 L₁ L₂ h₁ h₂ s hsL₁ hs2 hsZ htL₂ F _ _ hodd h5 e₁ e₂
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases h9 : Fintype.card F = 9
  · exact hNine X M hM hGH hO t htM ht2 L₁ L₂ h₁ h₂ s hsL₁ hs2 hsZ htL₂ F h9 e₁ e₂
  set K : Subgroup X := centralizer ({t} : Set X) ⊓ M with hK
  have hKM : K ≤ M := inf_le_right
  have hcore : ∀ L : Subgroup X, Nonempty (↥L ⧸ pPrimeCore 2 ↥L ≃* SL(2, F)) →
      IsQuasisimple ↥L → pPrimeCoreOf 2 L = ⊥ := by
    rintro L ⟨e⟩ hq
    rw [pPrimeCoreOf, pPrimeCore_eq_bot_of_qs_sl2 hq hodd h5 h9 e, Subgroup.map_bot]
  by_cases htZ : (⟨t, htM⟩ : ↥M) ∈ center ↥M
  ·
    have hKeq : K = M := by
      refine le_antisymm hKM fun m hm => Subgroup.mem_inf.2 ⟨?_, hm⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have := Subgroup.mem_center_iff.mp htZ ⟨m, hm⟩
      exact congrArg Subtype.val this
    have hKq : IsQuasisimple ↥K := by
      rw [hKeq]
      exact hM
    have hLM : ∀ L : Subgroup X, IsPCompIn 2 K L → pPrimeCoreOf 2 L = ⊥ := by
      intro L hL
      have htop := eq_top_of_pComponent_quasisimple hKq hL.2
      have hLK : L = K := by
        refine le_antisymm hL.1 fun k hk => ?_
        have : (⟨k, hk⟩ : ↥K) ∈ L.subgroupOf K := by rw [htop]; exact Subgroup.mem_top _
        exact this
      rw [hLK, hKeq, pPrimeCoreOf, hO, Subgroup.map_bot]
    exact ⟨hLM L₁ h₁, hLM L₂ h₂⟩
  by_cases hodl : GHOddLie (↥M ⧸ center ↥M)
  swap
  · exact (hOther X M hM hGH hodl hO t htM ht2 htZ L₁ L₂ h₁ h₂ s hsL₁ hs2 hsZ htL₂ F hodd h5 e₁
      e₂).elim
  set π : ↥M →* ↥M ⧸ center ↥M := QuotientGroup.mk' (center ↥M) with hπ
  set t' : ↥M := ⟨t, htM⟩ with ht'
  set κ : ↥K →* ↥M := Subgroup.inclusion hKM with hκdef
  have hrange : κ.range = centralizer ({t'} : Set ↥M) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply Subtype.ext
      have := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp y.2).1
      simpa [ht', hκdef] using this
    · intro hx
      rw [Subgroup.mem_centralizer_singleton_iff] at hx
      refine ⟨⟨x, Subgroup.mem_inf.mpr ⟨Subgroup.mem_centralizer_singleton_iff.mpr ?_, x.2⟩⟩, rfl⟩
      simpa [ht'] using congrArg Subtype.val hx
  set ρ : ↥K →* ↥M ⧸ center ↥M := π.comp κ with hρ
  have hρker : ρ.ker ≤ center ↥K := by
    intro k hk
    rw [MonoidHom.mem_ker, hρ, MonoidHom.comp_apply, hπ, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hk
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subgroup.inclusion_injective hKM
    simpa using (Subgroup.mem_center_iff.mp hk (κ g))
  have hZS : center (↥M ⧸ center ↥M) = ⊥ :=
    CFSG.LieType.CurtisTits.center_quotient_center_eq_bot_of_isQuasisimple hM
  have hu1 : π t' ≠ 1 := by
    intro h
    exact htZ ((QuotientGroup.eq_one_iff _).1 h)
  have hu2 : orderOf (π t') = 2 := by
    refine orderOf_eq_prime ?_ hu1
    have ht'2 : t' ^ 2 = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, ← ht2]
      exact pow_orderOf_eq_one t
    rw [← map_pow, ht'2, map_one]
  have hB := bTwo_of_ghOddLie hZS hodl hu2
  rw [BTwo, fixedSubgroup_conj_eq_centralizer_gen] at hB
  have hlift : ∀ L : Subgroup X, IsPCompIn 2 K L → IsQuasisimple ↥L := by
    intro L hL
    have hLnot : ¬ L.subgroupOf K ≤ ρ.ker := by
      intro hle
      have hperf : Group.IsPerfect ↥(L.subgroupOf K) :=
        CFSG.ComponentClassification.CatalogueBHeldSmallCore.pComponent_perfect 2 _ hL.2
      have : IsMulCommutative ↥(L.subgroupOf K) :=
        ⟨⟨fun a b => Subtype.ext ((Subgroup.mem_center_iff.mp (hρker (hle a.2)) (b : ↥K)).symm)⟩⟩
      have hss : Subsingleton ↥(L.subgroupOf K) := Group.IsPerfect.subsingleton_of_isMulCommutative
      have hb : L.subgroupOf K = ⊥ := Subgroup.eq_bot_of_subsingleton _
      have h2 := hL.2
      rw [hb] at h2
      obtain ⟨Kc, hKc, -, hmap, -⟩ := h2
      rw [Subgroup.map_bot] at hmap
      have hnt := CFSG.LocalCores.isQuasisimple_nontrivial hKc.1
      rw [← hmap] at hnt
      exact (Subgroup.nontrivial_iff_ne_bot _).1 hnt rfl
    obtain ⟨hBle, hBP⟩ := isPComponent_image κ hrange hL.2 hLnot
    have hBq : IsQuasisimple ↥((L.subgroupOf K).map ρ) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hBle) (hB _ hBP)
    have hJq : IsQuasisimple ↥(L.subgroupOf K) :=
      (CFSG.ComponentClassification.CatalogueBCentralQuotient.pComponent_quasisimple_iff ρ hρker 2
        _ hL.2).2 hBq
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hL.1) hJq
  exact ⟨hcore L₁ e₁ (hlift L₁ h₁), hcore L₂ e₂ (hlift L₂ h₂)⟩

end OddLie

end KG531BP

end CFSG.GH74.Generic.BProg.B3
