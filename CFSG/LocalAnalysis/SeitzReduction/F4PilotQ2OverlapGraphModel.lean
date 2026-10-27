module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2OverlapInvMain

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.EvenSmallLie
  CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.Timmesfeld.LieEmbed
open CFSG.LieType.Ree (ReeTag)
open CFSG.LieType.Steinberg CFSG.Assembly.LowTwoRank
open CFSG.SeitzReduction.SymplecticPilot (nsTorusSp)

section Inj

variable {M G : Type*} [Group M] [Group G]

theorem centralizer_map_inf_map_of_injective {φ : M →* G} (hφ : Function.Injective φ)
    (A B : Subgroup M) :
    centralizer ((A.map φ : Subgroup G) : Set G) ⊓ B.map φ =
      (centralizer (A : Set M) ⊓ B).map φ := by
  ext x
  constructor
  · rintro ⟨hx, ⟨b, hb, rfl⟩⟩
    refine ⟨b, ⟨mem_centralizer_iff.2 fun a ha => hφ ?_, hb⟩, rfl⟩
    rw [map_mul, map_mul]
    exact mem_centralizer_iff.1 hx (φ a) ⟨a, ha, rfl⟩
  · rintro ⟨b, ⟨hbc, hb⟩, rfl⟩
    refine ⟨mem_centralizer_iff.2 ?_, ⟨b, hb, rfl⟩⟩
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul, ← map_mul, mem_centralizer_iff.1 hbc a ha]

end Inj

abbrev twoOverlapRootL : Fin 3 → ℤ := ![0, 2, 1]

abbrev twoOverlapRootS : Fin 3 → ℤ := ![0, 1, 1]

theorem c3ToF4_twoOverlapRootL : c3ToF4 twoOverlapRootL = v0120 := by
  rw [c3ToF4_apply]
  funext i
  fin_cases i <;> rfl

theorem c3ToF4_twoOverlapRootS : c3ToF4 twoOverlapRootS = v0110 := by
  rw [c3ToF4_apply]
  funext i
  fin_cases i <;> rfl

section Roots

theorem twoOverlapRootL_mem_roots : twoOverlapRootL ∈ roots (Symplectic.isFiniteType_cartanC 3) ∅ :=
  c3ToF4_mem_c3LeviRoots_iff.1 (by
    rw [c3ToF4_twoOverlapRootL]
    exact ⟨mem_rootFinset.1 (by decide +kernel), rfl⟩)

theorem twoOverlapRootS_mem_roots : twoOverlapRootS ∈ roots (Symplectic.isFiniteType_cartanC 3) ∅ :=
  c3ToF4_mem_c3LeviRoots_iff.1 (by
    rw [c3ToF4_twoOverlapRootS]
    exact ⟨mem_rootFinset.1 (by decide +kernel), rfl⟩)

end Roots

section Glue

theorem rootGroup_v0120_eq (K : Type) [Field K] [Finite K] [CharP K 2] :
    (Adjoint.f4Datum K).rootGroup v0120 =
      (Symplectic.rootGroup 3 K twoOverlapRootL).map (c3LeviHom K) := by
  rw [map_c3LeviHom_rootGroup twoOverlapRootL_mem_roots, c3ToF4_twoOverlapRootL]

theorem rootGroup_v0110_eq (K : Type) [Field K] [Finite K] [CharP K 2] :
    (Adjoint.f4Datum K).rootGroup v0110 =
      (Symplectic.rootGroup 3 K twoOverlapRootS).map (c3LeviHom K) := by
  rw [map_c3LeviHom_rootGroup twoOverlapRootS_mem_roots, c3ToF4_twoOverlapRootS]

@[expose] def TwoGraphModelValues (κ : Sp6Kind) (K : Type) [Field K] (M : Type) [Group M]
    (ι : StatedSp 3 K →* M) : Prop :=
  Nat.card (centralizerPerfectCore ((nsTorusSp K (0 : Fin 3)).map ι)) = twoDiagPieceOrder κ ∧
    (κ.IsGraphKind →
      Nat.card (centralizer (((Symplectic.rootGroup 3 K twoOverlapRootL).map ι : Subgroup M) :
          Set M) ⊓ centralizerPerfectCore ((nsTorusSp K (0 : Fin 3)).map ι) : Subgroup M) =
          twoOverlapInvOrderL κ ∧
        Nat.card (centralizer (((Symplectic.rootGroup 3 K twoOverlapRootS).map ι : Subgroup M) :
          Set M) ⊓ centralizerPerfectCore ((nsTorusSp K (0 : Fin 3)).map ι) : Subgroup M) =
          twoOverlapInvOrderS κ)

@[expose] def IsTwoGraphParam {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K]
    [Finite K] [CharP K 2] (e : L ≃* adjointGroup .F4 K) (X₀ : Subgroup (adjointGroup .F4 K))
    {M : Type} [Group M] (ι : StatedSp 3 K →* M)
    (Φ : M ≃* centralizerPerfectCore (subgroupToG e X₀)) : Prop :=
  ∀ g, ((Φ (ι g) : centralizerPerfectCore (subgroupToG e X₀)) : G) =
    ((e.symm (c3LeviHom K g) : L) : G)

@[expose] def TwoGraphModelInput (κ : Sp6Kind) : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 →
    ∀ X₀ : Subgroup (adjointGroup .F4 K),
      X₀ ≤ (highestRootRankOne K).subgroupOf (adjointGroup .F4 K) → IsCyclic X₀ →
      Nat.card X₀ = 3 →
      ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (e : L ≃* adjointGroup .F4 K) (t : G),
        F4Work L K t 1 → TwoKindAt e t X₀ κ →
          ∃ (M : Type) (_ : Group M) (_ : Finite M) (ι : StatedSp 3 K →* M)
            (Φ : M ≃* centralizerPerfectCore (subgroupToG e X₀)),
            IsTwoGraphParam e X₀ ι Φ ∧ TwoGraphModelValues κ K M ι

theorem centralizerPerfectCore_std_eq_map_of_param {G : Type} [Group G] [Finite G]
    {L : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2]
    (e : L ≃* adjointGroup .F4 K) (X₀ : Subgroup (adjointGroup .F4 K)) {M : Type} [Group M]
    [Finite M] (ι : StatedSp 3 K →* M) (Φ : M ≃* centralizerPerfectCore (subgroupToG e X₀))
    (hΦ : IsTwoGraphParam e X₀ ι Φ) :
    (∀ A : Subgroup (StatedSp 3 K), subgroupToG e (A.map (c3LeviHom K)) =
        (A.map ι).map ((centralizerPerfectCore (subgroupToG e X₀)).subtype.comp
          Φ.toMonoidHom)) ∧
      centralizerPerfectCore (subgroupToG e (X₀ ⊔ stdX K)) =
        (centralizerPerfectCore ((nsTorusSp K (0 : Fin 3)).map ι)).map
          ((centralizerPerfectCore (subgroupToG e X₀)).subtype.comp Φ.toMonoidHom) := by
  have hcomp : (L.subtype.comp e.symm.toMonoidHom).comp (c3LeviHom K) =
      ((centralizerPerfectCore (subgroupToG e X₀)).subtype.comp Φ.toMonoidHom).comp ι := by
    ext g
    exact (hΦ g).symm
  have hmap : ∀ A : Subgroup (StatedSp 3 K), subgroupToG e (A.map (c3LeviHom K)) =
      (A.map ι).map ((centralizerPerfectCore (subgroupToG e X₀)).subtype.comp
        Φ.toMonoidHom) := by
    intro A
    rw [subgroupToG, Subgroup.map_map, Subgroup.map_map, Subgroup.map_map, hcomp]
  refine ⟨hmap, ?_⟩
  have hY : subgroupToG e (stdX K) = (((nsTorusSp K (0 : Fin 3)).map ι).map
      Φ.toMonoidHom).map (centralizerPerfectCore (subgroupToG e X₀)).subtype := by
    rw [stdX, hmap, Subgroup.map_map, Subgroup.map_map, Subgroup.map_map]
  have hYE : subgroupToG e (stdX K) ≤ centralizerPerfectCore (subgroupToG e X₀) := by
    rw [hY]
    exact map_subtype_le _
  have hYsub : (subgroupToG e (stdX K)).subgroupOf (centralizerPerfectCore (subgroupToG e X₀)) =
      ((nsTorusSp K (0 : Fin 3)).map ι).map Φ.toMonoidHom := by
    rw [hY]
    exact Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _) _
  rw [subgroupToG_sup, centralizerPerfectCore_sup_eq_map hYE, hYsub,
    ← map_centralizerPerfectCore Φ, Subgroup.map_map]

theorem twoOverlapInvAt_of_modelInput {κ : Sp6Kind} (h : TwoGraphModelInput κ) :
    TwoOverlapInvAt κ := by
  intro K _ _ _ hK X₀ hXJ hcyc hX₀ G _ _ L e t hw hκ
  have : CharP K 2 := ‹CharP K ReeTag.F4.prime›
  obtain ⟨M, _, _, ι, Φ, hΦ, hV1, hV2⟩ := h K hK X₀ hXJ hcyc hX₀ G L e t hw hκ
  obtain ⟨hmap, hcore⟩ := centralizerPerfectCore_std_eq_map_of_param e X₀ ι Φ hΦ
  have hφinj : Function.Injective
      ((centralizerPerfectCore (subgroupToG e X₀)).subtype.comp Φ.toMonoidHom) :=
    (centralizerPerfectCore (subgroupToG e X₀)).subtype_injective.comp Φ.injective
  refine ⟨?_, fun hg => ?_⟩
  · rw [hcore, Subgroup.card_map_of_injective hφinj, hV1]
  · obtain ⟨hL, hS⟩ := hV2 hg
    refine ⟨?_, ?_⟩
    · unfold coreCentCard
      rw [rootGroup_v0120_eq, hmap, hcore, centralizer_map_inf_map_of_injective hφinj,
        Subgroup.card_map_of_injective hφinj, hL]
    · unfold coreCentCard
      rw [rootGroup_v0110_eq, hmap, hcore, centralizer_map_inf_map_of_injective hφinj,
        Subgroup.card_map_of_injective hφinj, hS]

end Glue

end CFSG.SeitzReduction.F4Pilot
