module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7QPUCat
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7QPUSporSROrd
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7QPUSporSRTr
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7QPUSporSRMon
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLift
public import CFSG.LocalAnalysis.ComponentClassification.Foote5EndKGSporBasic
public import CFSG.LocalAnalysis.ComponentClassification.SporRestrictedLocal
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSporadicCasesD
public import CFSG.LocalAnalysis.ComponentClassification.BMCaseOddCoreB
public import CFSG.Monster.B.CTIB.ComponentsSeventeen
public import CFSG.Monster.SteinbergMSporadicOddCoreFree

public section

namespace CFSG.ComponentClassification.GSThmB.QPUSpor

open CFSG Subgroup CFSG.Blueprint
open scoped MatrixGroups

theorem isComponent_subgroupOf {G : Type*} [Group G] {C K : Subgroup G} (hKC : K ≤ C)
    (hKs : (K.subgroupOf C).IsSubnormal) {T : Type*} [Group T] [IsSimpleGroup T]
    (hna : ∃ a b : T, a * b ≠ b * a) (eK : K ≃* T) :
    IsComponent (K.subgroupOf C) ∧ Nonempty (K.subgroupOf C ⧸ center (K.subgroupOf C) ≃* T) := by
  let e : K.subgroupOf C ≃* T := (Subgroup.subgroupOfEquivOfLe hKC).trans eK
  have : IsSimpleGroup (K.subgroupOf C) := e.isSimpleGroup
  obtain ⟨hq, hZ⟩ := LocalCores.isQuasisimple_of_isSimpleGroup (Q := K.subgroupOf C) (by
    obtain ⟨a, b, hab⟩ := hna
    exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩)
  exact ⟨⟨hq, hKs⟩,
    ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans e⟩⟩

theorem exists_component_of_cover {M : Type} [Group M] [Finite M] (hZ : IsPGroup 2 (center M))
    {t : M} {J : Subgroup M} (hJC : J ≤ centralizer ({t} : Set M))
    (hJs : (J.subgroupOf (centralizer ({t} : Set M))).IsSubnormal) {T : Type} [Group T]
    [IsSimpleGroup T] (hna : ∃ a b : T, a * b ≠ b * a) (eT : ↥J ⧸ pPrimeCore 2 ↥J ≃* T)
    (hO : pPrimeCore 2 ↥(centralizer ({(t : M ⧸ center M)} : Set (M ⧸ center M))) = ⊥) :
    ∃ B : Subgroup ↥(centralizer ({(t : M ⧸ center M)} : Set (M ⧸ center M))),
      IsComponent B ∧ Nonempty (B ⧸ center B ≃* T) := by
  obtain ⟨K, hKC, hKs, ⟨eK⟩⟩ := exists_subnormal_of_cover (QuotientGroup.mk' (center M))
    (QuotientGroup.mk'_surjective _) (by rwa [QuotientGroup.ker_mk'])
    (by rw [QuotientGroup.ker_mk']) hJC hJs eT inferInstance hna hO
  exact ⟨_, isComponent_subgroupOf hKC hKs hna eK⟩

theorem false_of_components {M : Type} [Group M] [Finite M] (hMq : IsQuasisimple M)
    (hZ : IsPGroup 2 (center M)) {s : TauCeti.SporadicName}
    (hs : CatalogueU.SporadicOddCoreFree s) (e : M ⧸ center M ≃* NativeSporadic.Carrier s)
    {t : M} (htt : t * t = 1) (htZ : t ∉ center M) {J : Subgroup M}
    (hJC : J ≤ centralizer ({t} : Set M))
    (hJc : IsPComponent 2 (J.subgroupOf (centralizer ({t} : Set M)))) {T : Type} [Group T]
    [IsSimpleGroup T] (hna : ∃ a b : T, a * b ≠ b * a) (eT : ↥J ⧸ pPrimeCore 2 ↥J ≃* T)
    (hT : ∀ u : M ⧸ center M, orderOf u = 2 → ∀ B : Subgroup ↥(centralizer ({u} : Set _)),
      IsComponent B → IsEmpty (B ⧸ center B ≃* T)) : False := by
  have : IsSimpleGroup (M ⧸ center M) := hMq.2.1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ht : orderOf (t : M ⧸ center M) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [sq, ← QuotientGroup.mk_mul, htt, QuotientGroup.mk_one]
    · exact fun h => htZ ((QuotientGroup.eq_one_iff t).1 h)
  have hO : pPrimeCore 2 ↥(centralizer ({(t : M ⧸ center M)} : Set (M ⧸ center M))) = ⊥ := by
    rw [← BMCase.gmat_oddCore_eq_pPrimeCore_two]
    exact Foote5.oddCore_centralizer_eq_bot_of_sporadicOddCoreFree hs hMq.2.2 e ht
  obtain ⟨-, -, hJs, -, -⟩ := hJc
  obtain ⟨B, hB, ⟨eB⟩⟩ := exists_component_of_cover hZ hJC hJs hna eT hO
  exact (hT _ ht B hB).false eB

theorem cfQPUJSpor_holds
    : CFQPUJSpor := by
  intro M _ _ p' f' p f hcfg hrep
  obtain ⟨s, ⟨e⟩⟩ := hrep
  obtain ⟨hMq, hZ, hp', hp'2, hf', h5', hp, hp2, hf, -, hpp, hff, _E, L, t, J, _J₀, -, -, -, -,
    hLmod, -, htt, htZ, hJC, hJc, hJmod, -, -, -⟩ := hcfg
  have : Fact p.Prime := ⟨hp⟩
  have : IsSimpleGroup (M ⧸ center M) := hMq.2.1
  obtain ⟨-, -, -, F, _, _, hF, ⟨eJ⟩⟩ := HarrisLit.exists_psl2_of_lieModel hJmod
  have : IsSimpleGroup (↥J ⧸ pPrimeCore 2 ↥J) := HarrisLit.isSimpleGroup_of_lieModel_psl2 hJmod
  have : IsSimpleGroup (PSL(2, F)) := eJ.symm.isSimpleGroup
  have hna : ∃ a b : PSL(2, F), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := HarrisLit.nonabelian_of_lieModel_psl2 hJmod
    exact ⟨eJ a, eJ b, fun h => hab (eJ.injective (by rw [map_mul, map_mul, h]))⟩
  by_cases hsM : s = .M
  · subst hsM
    exact false_of_components hMq hZ CatalogueU.sporadicOddCoreFree_M e htt htZ hJC hJc hna eJ
      fun u hu B hB => not_psl2_component_M e hp2 (by omega) hF u hu B hB
  obtain ⟨hs, hq⟩ := psp4_pair_of_le hZ e hsM hp' hp'2 hf' h5' hLmod
  have h5 : p ^ f = 5 := by rw [hpp, hff]; exact hq
  have h60 : Nat.card (PSL(2, F)) = 60 := by
    rw [SectionRank.OddCover.card_psl_two hp hp2 hF, h5]
    norm_num
  rcases hs with rfl | rfl
  · refine false_of_components hMq hZ CatalogueU.sporadicOddCoreFree_Co1 e htt htZ hJC hJc hna
      eJ fun u hu B hB => ⟨fun eB => ?_⟩
    have h13 := (RestrictedStd.Spor.co1LocalComponentsInput_holds _ e u hu B hB).2
    rw [Nat.card_congr eB.toEquiv, h60] at h13
    norm_num at h13
  · refine false_of_components hMq hZ BMCase.sporadicOddCoreFree_B e htt htZ hJC hJc hna
      eJ fun u hu B hB => ⟨fun eB => ?_⟩
    have h17 := (Monster.B.CTIB.involution_local_components_simple_quotient_divisible_by_seventeen
      ⟨e⟩ u hu B hB).2.2
    rw [Nat.card_congr eB.toEquiv, h60] at h17
    norm_num at h17

end CFSG.ComponentClassification.GSThmB.QPUSpor
