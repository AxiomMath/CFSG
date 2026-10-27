module

public import CFSG.ClassicalInvolution.Q3.Q3AMBadNbhd

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3AM

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q3.Q3T8.Asc77 CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Q3.Q3CP CFSG.ClassicalInvolution.Q3.Q3CH
open scoped MatrixGroups commutatorElement

section Defs


abbrev layerFam {G : Type} [Group G] (Ω : Set (Subgroup G)) (M : Subgroup G) (a : G) :
    Set (Subgroup (↥(nbrLayer Ω M a) ⧸ classicalInvolutionOddCore ↥(nbrLayer Ω M a))) :=
  oddQuotientFamily (restrictFamily (centralizingMembers (nbrCoreFam Ω M a) {a})
    (nbrLayer Ω M a))

@[expose] def LayerL3 {G : Type} [Group G] (Ω : Set (Subgroup G)) (M : Subgroup G) (a : G) :
    Prop :=
  ∃ (ι : Type) (_ : Finite ι) (D : LieSystemData3 ι
      (↥(nbrLayer Ω M a) ⧸ classicalInvolutionOddCore ↥(nbrLayer Ω M a)) (layerFam Ω M a)),
    ∃ i₁ : ι, (∀ i, i = i₁) ∧ D.kind i₁ = CompData.model .PSL 3

@[expose] def LayerM11 {G : Type} [Group G] (Ω : Set (Subgroup G)) (M : Subgroup G) (a : G) :
    Prop :=
  ∃ (ι : Type) (_ : Finite ι) (D : LieSystemData3 ι
      (↥(nbrLayer Ω M a) ⧸ classicalInvolutionOddCore ↥(nbrLayer Ω M a)) (layerFam Ω M a)),
    ∃ i₁ : ι, (∀ i, i = i₁) ∧ D.kind i₁ = CompData.m11

@[expose] def LayerS3 {G : Type} [Group G] (Ω : Set (Subgroup G)) (M : Subgroup G) (a : G) :
    Prop :=
  ∃ (ι : Type) (_ : Finite ι) (D : LieSystemData3 ι
      (↥(nbrLayer Ω M a) ⧸ classicalInvolutionOddCore ↥(nbrLayer Ω M a)) (layerFam Ω M a)),
    ∃ i₁ : ι, (∀ i, i = i₁) ∧ (D.kind i₁ = CompData.model .PSU 3 ∨
      D.kind i₁ = CompData.model .G2 0 ∨ D.kind i₁ = CompData.model .trialityD4 0)

@[expose] def ThinY {G : Type} [Group G] (Ω : Set (Subgroup G)) (M : Subgroup G) (a : G) :
    Prop :=
  ∃ W' ∈ CFSG.ClassicalInvolution.Asc77.WSet (layerFam Ω M a),
    CFSG.ClassicalInvolution.Asc77.MuIsoZ2 (layerFam Ω M a) W'

@[expose] def NoTriangleAtEdge {G : Type} [Group G] (Ω : Set (Subgroup G)) (K J : Subgroup G) :
    Prop :=
  ∀ K' ∈ omegaNbr Ω K, K' ∉ omegaNbr Ω J

end Defs

section Lie


variable {G : Type} [Group G] [Finite G]

theorem trivialOnQuot_of_edge [IsSimpleGroup G] {K : Subgroup G} {z : G} {M N : Subgroup G}
    {a b : G} (he : EdgeSetup K z M N a b) (hnab : ∃ x y : G, x * y ≠ y * x)
    (hBelow : Q3.CIT3Below (Nat.card G)) : a ∈ trivialOnQuot N := by
  have haM : a ∈ M ⊓ Subgroup.centralizer ({b} : Set G) := by
    obtain ⟨R, R', hp⟩ := he.exists_sylowPair
    refine ⟨he.uniqueM.mem, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    exact (hp.commutes b hp.mem_t a hp.mem_a).symm
  exact ⟨mem_normalizer_iff_conjSub_eq.mpr (he.conjSub_eq_of_mem_centM hnab hBelow a haM),
    fun n hn => he.commutator_centM_le_oddCore hnab hBelow a haM n hn⟩

theorem secData3_nbrCoreFam [IsSimpleGroup G] {Ω : Set (Subgroup G)} {K J : Subgroup G}
    {S : Sylow 2 G} {R T W : Subgroup G} {z t : G} (h : BadStd8 Ω K J S R T W z t)
    (hint : IsIntrinsicU (.sl2 3 1) K z) {M : Subgroup G} {a : G} (hM : M ∈ Ω)
    (ha : IsUniqueInvolution M a) : SecData3 a (nbrCoreFam Ω M a) := by
  classical
  have hstd := h.std
  have hΩ : HypOmegaMod Ω := hstd.stand.hyp
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hstd.stand.trans hstd.noTwins hM
  have hBelow : Q3.CIT3Below (Nat.card G) :=
    (citBelowT_three_iff (p := 3) (f := 1) (by norm_num) _).mp hstd.stand.below
  have hnab : ∃ x y : G, x * y ≠ y * x := h.nonabelian
  have hc2 : IsPGroup 2 (Subgroup.zpowers a) :=
    isPGroup_zpowers_of_mul_self_eq_one ha.sq ha.ne_one
  have hCM : ∀ g ∈ Subgroup.centralizer ({a} : Set G), conjSub g M = M := fun g hg =>
    mem_normalizer_iff_conjSub_eq.mp
      (T8.centralizer_le_normalizer_of_noTwins hΩ.conjInvariant hM (hnt M hM) ha hg)
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨g, hg⟩ := hstd.stand.trans M hM
    have hN : conjSub g J ∈ omegaNbr Ω M := by
      have := omegaNbr_conj hΩ.conjInvariant hstd.hJ g
      rwa [hg] at this
    exact ⟨exactCore3 a (conjSub g J), conjSub g J, hN, rfl⟩
  · rintro _ ⟨N, hN, rfl⟩
    exact exactCore3_le_centralizer a N
  · rintro n hn _ ⟨N, hN, rfl⟩
    refine ⟨conjSub n N, conjSub_mem_omegaNbr_of_conjSub_eq hΩ (hCM n hn) hN, ?_⟩
    have e := exactCore3_conjSub n a N
    rw [conj_eq_of_mem_centralizer_singleton hn] at e
    exact e.symm
  · rintro _ ⟨N, hN, rfl⟩
    obtain ⟨b, hb⟩ := hΩ.exists_uniqueInvolution hN.1
    have he := h.toEdgeSetup hint hM hN ha hb
    have hNc : IsClassicalMember3 N b :=
      Q3T8.Asc77.isClassicalMember3_of_uniqueInvolution hstd.stand.modU hN.1 hb
    exact ⟨b, isSectionMember3_exactCore3 hNc hc2 (trivialOnQuot_of_edge he hnab hBelow)⟩

theorem nbrLayer_lieSystem [IsSimpleGroup G] {Ω : Set (Subgroup G)} {K J : Subgroup G}
    {S : Sylow 2 G} {R T W : Subgroup G} {z t : G} (h : BadStd8 Ω K J S R T W z t)
    (hint : IsIntrinsicU (.sl2 3 1) K z) {M : Subgroup G} {a : G} (hM : M ∈ Ω)
    (ha : IsUniqueInvolution M a) :
    ∃ (ι : Type) (_ : Finite ι), Nonempty (LieSystemData3 ι
      (↥(nbrLayer Ω M a) ⧸ classicalInvolutionOddCore ↥(nbrLayer Ω M a)) (layerFam Ω M a)) := by
  have hstd := h.std
  have hBelow : Q3.CIT3Below (Nat.card G) :=
    (citBelowT_three_iff (p := 3) (f := 1) (by norm_num) _).mp hstd.stand.below
  have hZ : Subgroup.center G = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h' | h'
    · exact h'
    · exfalso
      obtain ⟨x, y, hxy⟩ := h.nonabelian
      exact hxy (Subgroup.mem_center_iff.mp (h' ▸ Subgroup.mem_top x) y).symm
  have hnc : ¬ ({a} : Set G) ⊆ Subgroup.center G := fun hs => ha.ne_one (by
    have h1 : a ∈ Subgroup.center G := hs (Set.mem_singleton a)
    rwa [hZ, Subgroup.mem_bot] at h1)
  exact lieSystemMod3_of_secData3 (secData3_nbrCoreFam h hint hM ha) hBelow hnc

theorem nbrLayer_exact_images [IsSimpleGroup G] {Ω : Set (Subgroup G)} {K J : Subgroup G}
    {S : Sylow 2 G} {R T W : Subgroup G} {z t : G} (h : BadStd8 Ω K J S R T W z t)
    (hint : IsIntrinsicU (.sl2 3 1) K z) {M : Subgroup G} {a : G} (hM : M ∈ Ω)
    (ha : IsUniqueInvolution M a) :
    ∀ N ∈ omegaNbr Ω M, Nat.card ↥(Subgroup.map
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥(nbrLayer Ω M a)))
      ((exactCore3 a N).subgroupOf (nbrLayer Ω M a))) = 24 := by
  obtain ⟨ι, -, ⟨D⟩⟩ := nbrLayer_lieSystem h hint hM ha
  exact fun N hN => nbrExact_of_lieSystem D hN

theorem commutator_mem_oddCoreOf_nbrLayer' [IsSimpleGroup G] {Ω : Set (Subgroup G)}
    {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}
    (h : BadStd8 Ω K J S R T W z t) (hint : IsIntrinsicU (.sl2 3 1) K z) {M : Subgroup G}
    {a : G} (hM : M ∈ Ω) (ha : IsUniqueInvolution M a) {g : G} (hg : g ∈ M) {y : G}
    (hy : y ∈ nbrLayer Ω M a) : ⁅g, y⁆ ∈ oddCoreOf (nbrLayer Ω M a) :=
  commutator_mem_oddCoreOf_nbrLayer h hint hM ha (nbrLayer_exact_images h hint hM ha) hg hy

end Lie

end CFSG.ClassicalInvolution.Q3.Q3AM
