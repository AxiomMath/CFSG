module

public import CFSG.ClassicalInvolution.PerfectCase.Basic
public import CFSG.ClassicalInvolution.Reduction
public import CFSG.ClassicalInvolution.LBalance
import CFSG.ClassicalInvolution.SubnormalClosure
import CFSG.FeitThompson.OddOrderTheorem
import CFSG.Adapters.WholeGroupLayer

public section

namespace CFSG.ClassicalInvolution

open CFSG.Open CFSG.ComponentClassification

@[expose] def CITSimplePerfect : Prop :=
  ∀ (F : Type) [Group F] [Finite F] [IsSimpleGroup F], (∃ a b : F, a * b ≠ b * a) →
    ∀ z : F, orderOf z = 2 → ∀ K : Subgroup F, z ∈ K →
    IsSubnormal K (Subgroup.centralizer ({z} : Set F)) → classicalInvolutionWitness K →
    ¬ Group.IsSolvable K →
    Blueprint.OddLieType F ∨ Blueprint.NativeSporadic.IsSporadic F .M11

theorem even_natCard_of_nonabelian_simple {F : Type*} [Group F] [Finite F] [IsSimpleGroup F]
    (hnab : ∃ a b : F, a * b ≠ b * a) : Even (Nat.card F) := by
  by_contra h
  rw [Nat.not_even_iff_odd] at h
  obtain ⟨a, b, hab⟩ := hnab
  exact hab ((IsSimpleGroup.comm_iff_isSolvable).2 (CFSG.FeitThompson.isSolvable_of_odd_natCard _ h) a b)

theorem centralizer_genFittingFStar_eq_bot {G : Type} [Group G] [Finite G]
    [IsSimpleGroup (genFittingFStar G)] (hFnonab : ∃ a b : genFittingFStar G, a * b ≠ b * a) :
    Subgroup.centralizer (genFittingFStar G : Set G) = ⊥ := by
  have h : genFittingFStar G = CFSG.generalizedFitting G :=
    (CFSG.generalizedFitting_eq_componentClassification G).symm
  have hs : IsSimpleGroup (CFSG.generalizedFitting G) := h ▸ inferInstance
  rw [h] at hFnonab ⊢
  exact CFSG.Adapters.centralizer_generalizedFitting_eq_bot_of_isSimpleGroup G hs hFnonab

theorem exists_classicalSubgroup_of_l2PrimeBalance (hL : L2PrimeBalance) {G : Type} [Group G]
    [Finite G] (F : Subgroup G) [F.Normal] [IsSimpleGroup F] (hFeven : Even (Nat.card F))
    (hCen : Subgroup.centralizer (F : Set G) = ⊥) {z : G} (hz : orderOf z = 2) {J : Subgroup G}
    (hzJ : z ∈ J) (hJ : IsSubnormal J (Subgroup.centralizer ({z} : Set G)))
    (hw : classicalInvolutionWitness J) (hns : ¬ Group.IsSolvable J) :
    ∃ hzF : z ∈ F, ∃ K : Subgroup F, (⟨z, hzF⟩ : F) ∈ K ∧
      IsSubnormal K (Subgroup.centralizer ({(⟨z, hzF⟩ : F)} : Set F)) ∧
      classicalInvolutionWitness K ∧ ¬ Group.IsSolvable K := by
  have hXz : Subgroup.centralizer ((Subgroup.zpowers z : Subgroup G) : Set G) =
      Subgroup.centralizer ({z} : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  set X := Subgroup.centralizer ((Subgroup.zpowers z : Subgroup G) : Set G)
  have hJX : IsSubnormal J X := by rw [hXz]; exact hJ
  have hJXle : J ≤ X := isSubnormal_le hJX
  have hzX : z ∈ X := hJXle hzJ
  have hJsub : IsSubnormal (J.subgroupOf X) ⊤ := by
    have := isSubnormal_subgroupOf hJX X
    rwa [Subgroup.subgroupOf_self] at this
  have hwX : classicalInvolutionWitness (J.subgroupOf X) :=
    classicalInvolutionWitness_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJXle).symm hw
  have hnsX : ¬ Group.IsSolvable (J.subgroupOf X) := fun h =>
    hns (Group.isSolvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hJXle).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hJXle).surjective)
  have hq := isQuasisimple_oddCoreQuotient_of_witness hwX hnsX
  obtain ⟨L, hLle, hL2, hmap⟩ := exists_isTwoComponent_le (J.subgroupOf X) hJsub hq
  have hLsub : IsSubnormal L ⊤ := hL2.1
  have hLpc : CFSG.IsPComponent 2 L := (CatalogueBAlternating.pComponent_two_iff L).mpr hL2
  have hA : IsPGroup 2 (Subgroup.zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz]; simp)
  have hLF : L.map X.subtype ≤ F :=
    twoComponent_le_of_l2PrimeBalance hL F hFeven hCen _ hA L hLpc
  have hz'L : (⟨z, hzX⟩ : X) ∈ L :=
    mem_of_orderOf_eq_two_of_map_eq hLle hLsub hJsub hmap (Subgroup.mem_subgroupOf.mpr hzJ)
      (by rw [Subgroup.orderOf_mk]; exact hz)
  have hzL : z ∈ L.map X.subtype := ⟨⟨z, hzX⟩, hz'L, rfl⟩
  have hzF : z ∈ F := hLF hzL
  obtain ⟨e⟩ := nonempty_oddCoreQuotientEquiv_of_map_eq hLsub hJsub hmap
  let eLK : L ≃* (L.map X.subtype).subgroupOf F :=
    (L.equivMapOfInjective X.subtype X.subtype_injective).trans
      (Subgroup.subgroupOfEquivOfLe hLF).symm
  refine ⟨hzF, (L.map X.subtype).subgroupOf F, Subgroup.mem_subgroupOf.mpr hzL, ?_, ?_, ?_⟩
  · have h1 : IsSubnormal (L.map X.subtype) X := by
      have := Components.chain_map X.subtype hLsub
      rwa [Subgroup.map_top, Subgroup.range_subtype] at this
    have h1' : IsSubnormal (L.map X.subtype) (Subgroup.centralizer ({z} : Set G)) := by
      rw [← hXz]; exact h1
    have h2 : IsSubnormal (L.map X.subtype) (Subgroup.centralizer ({z} : Set G) ⊓ F) := by
      have := isSubnormal_inf h1' F
      rwa [inf_eq_left.mpr hLF] at this
    rw [← subgroupOf_centralizer_inf hzF]
    exact isSubnormal_subgroupOf h2 F
  · exact classicalInvolutionWitness_of_mulEquiv eLK
      (classicalInvolutionWitness_of_quotientEquiv e.symm hwX)
  · intro hKs
    have hLs : Group.IsSolvable L :=
      Group.isSolvable_of_surjective (f := eLK.symm.toMonoidHom) eLK.symm.surjective
    have hLq : Group.IsSolvable (L ⧸ componentClassificationOddCore L) :=
      Group.isSolvable_of_surjective (QuotientGroup.mk'_surjective _)
    exact not_isSolvable_of_open_isQuasisimple hq
      (Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective)

theorem partOne_nonsolvable (hL : L2PrimeBalance) (hC : CITSimplePerfect) :
    PartOneUnder fun _ J => ¬ Group.IsSolvable J := by
  intro G _ _ _ hFnonab z hz J hzJ hJ _ _ hw hns
  have : (genFittingFStar G).Normal := genFittingFStar_normal G
  obtain ⟨hzF, K, hzK, hKsub, hKw, hKns⟩ := exists_classicalSubgroup_of_l2PrimeBalance hL
    (genFittingFStar G) (even_natCard_of_nonabelian_simple hFnonab)
    (centralizer_genFittingFStar_eq_bot hFnonab) hz hzJ hJ hw hns
  exact hC (genFittingFStar G) hFnonab ⟨z, hzF⟩ (by rwa [Subgroup.orderOf_mk]) K hzK hKsub hKw
    hKns

theorem partOne_of_l2PrimeBalance (hL : L2PrimeBalance) (hC : CITSimplePerfect)
    (hs : PartOneSolvable) : PartOne := by
  intro G _ _ _ hnab z hz J hzJ hJ S hS hw _
  by_cases hsol : Group.IsSolvable J
  · exact hs G hnab z hz J hzJ hJ S hS hw hsol
  · exact partOne_nonsolvable hL hC G hnab z hz J hzJ hJ S hS hw hsol

end CFSG.ClassicalInvolution
