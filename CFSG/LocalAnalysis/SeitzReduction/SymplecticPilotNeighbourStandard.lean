module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHsyl
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotBLift
public import CFSG.LocalAnalysis.SeitzReduction.SeitzBranches
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotSetup
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotNeighbourStandard
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotBLift
import CFSG.LocalAnalysis.SeitzReduction.F4PilotHR7
import CFSG.LocalAnalysis.SeitzReduction.F4PilotFieldNormalizeSp
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticTwoSchreier
public import CFSG.LocalAnalysis.EvenSmallLie.Children
import CFSG.Assembly.GL83LieDefs

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.OuterAutomorphisms (Outer solvable_of_equiv)
open CFSG.SeitzReduction.F4Pilot (HasBLift)

variable {K : Type} [Field K] {n : ℕ}

section Model

theorem center_eq_bot_of_mulEquiv {D S : Type*} [Group D] [Group S] (ψ : D ≃* S)
    (h : center S = ⊥) : center D = ⊥ := by
  refine eq_bot_iff.2 fun z hz => ?_
  have hz' : ψ z ∈ center S := by
    rw [mem_center_iff] at hz ⊢
    intro g
    obtain ⟨g', rfl⟩ := ψ.surjective g
    rw [← map_mul, ← map_mul, hz g']
  rw [h, mem_bot] at hz'
  rw [mem_bot]
  exact ψ.injective (hz'.trans (map_one ψ).symm)

theorem isSolvable_outer_statedSp [Finite K] [CharP K 2] (hn : 2 ≤ n) :
    Group.IsSolvable (Outer (StatedSp n K)) := by
  have : NeZero n := ⟨by omega⟩
  have : Group.IsSolvable (Outer (StatedProj (StatedSp n K))) := by
    rcases (show n = 2 ∨ 3 ≤ n by omega) with rfl | hn3
    · exact (CFSG.ComponentClassification.CatalogueBSymplecticTwo.symplectic_two_schreier K).2
    · exact (SymplecticHigher.symplectic_schreier hn3).2
  exact solvable_of_equiv (F4Pilot.spProjEquiv n K).symm

end Model

section RootTorus

variable {G : Type*} [Group G] {L : Subgroup G} [Finite K] [CharP K 2]

theorem neighbour_data_rootTorusSp (hq : 4 ≤ Nat.card K) (hn : 2 ≤ n)
    (e : L ≃* StatedSp (n + 1) K) (k : Fin (n + 1)) {t : G} (htC : t ∈ centralizer (L : Set G))
    {X : Subgroup G} (hX : X = ((rootTorusSp K k).map e.symm.toMonoidHom).map L.subtype)
    {D : Subgroup G} (hDe : D = ((complSp K k).map e.symm.toMonoidHom).map L.subtype) :
    X ≤ L ∧ t ∈ centralizer (X : Set G) ∧ IsCyclic X ∧ Nat.card X = Nat.card K - 1 ∧
      Odd (Nat.card X) ∧ D = inSubgroup layer (L ⊓ centralizer (X : Set G)) ∧
      D ≤ centralizer (X : Set G) ⊓ centralizer ({t} : Set G) ∧
      CFSG.Open.IsQuasisimple D ∧ Nonempty (D ≃* StatedSp n K) ∧ center D = ⊥ ∧
      Group.IsSolvable (Outer D) := by
  subst hX hDe
  set ψ : (((complSp K k).map e.symm.toMonoidHom).map L.subtype : Subgroup G) ≃* StatedSp n K :=
    (LinearPilot.mapSymmMulEquiv e (complSp K k)).trans (complSpEquiv k).symm
  have hXc : Nat.card (((rootTorusSp K k).map e.symm.toMonoidHom).map L.subtype : Subgroup G) =
      Nat.card K - 1 := (LinearPilot.card_map_symm e _).trans (card_rootTorusSp k)
  have : Group.IsSolvable (Outer (StatedSp n K)) := isSolvable_outer_statedSp hn
  exact ⟨map_subtype_le _, LinearPilot.mem_centralizer_map_symm e _ htC,
    LinearPilot.isCyclic_map_symm e (isCyclic_rootTorusSp k), hXc,
    hXc ▸ LinearPilot.odd_natCard_sub_one,
    (layer_inf_centralizer_rootTorusSp hq (by omega) e k).symm,
    le_inf (LinearPilot.map_symm_le_centralizer_map_symm e (complSp_le_centralizer_rootTorusSp k))
      (LinearPilot.map_symm_le_centralizer_singleton e _ htC),
    isQuasisimple_open_map_complSp hq (by omega) e k, ⟨ψ⟩,
    center_eq_bot_of_mulEquiv ψ (center_statedSp_eq_bot n), solvable_of_equiv ψ.symm⟩

variable [Finite G]

theorem neighbour_standard (hL : standardComponentIsStandard L) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hq : 4 ≤ Nat.card K) (hn : 2 ≤ n) (e : L ≃* StatedSp (n + 1) K) (k : Fin (n + 1))
    {X : Subgroup G} (htX : t ∈ centralizer (X : Set G))
    (hX : ((rootTorusSp K k).map e.symm.toMonoidHom).map L.subtype ≤ X) {D : Subgroup G}
    (hDe : D = ((complSp K k).map e.symm.toMonoidHom).map L.subtype)
    (hD : D = inSubgroup layer (L ⊓ centralizer (X : Set G))) :
    CFSG.Open.IsComponentOf
        ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))))
        (centralizer ({QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩} :
          Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))))) ∧
      (∀ U : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
        IsPGroup 2 U →
        U ≤ centralizer ((D.subgroupOf (centralizer (X : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) :
          Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) →
        Nat.card U ≤ 2) ∧
      standardComponentIsStandard ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) :=
  F4Pilot.standard_inheritance_of_forall_fix_eq_one hL htC ht hKt htX hD
    (hDe ▸ isQuasisimple_open_map_complSp hq (by omega) e k)
    (eq_one_of_fix_map_rootTorusSp hq hn e k hX hDe.ge)

theorem neighbour_standard_rootTorusSp (hL : standardComponentIsStandard L) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hq : 4 ≤ Nat.card K) (hn : 2 ≤ n) (e : L ≃* StatedSp (n + 1) K) (k : Fin (n + 1))
    {X : Subgroup G} (hX : X = ((rootTorusSp K k).map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G}
    (hDe : D = ((complSp K k).map e.symm.toMonoidHom).map L.subtype) :
    CFSG.Open.IsComponentOf
        ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))))
        (centralizer ({QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩} :
          Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))))) ∧
      (∀ U : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
        IsPGroup 2 U →
        U ≤ centralizer ((D.subgroupOf (centralizer (X : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) :
          Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) →
        Nat.card U ≤ 2) ∧
      standardComponentIsStandard ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) := by
  obtain ⟨-, -, -, -, -, hD, -⟩ := neighbour_data_rootTorusSp hq hn e k htC hX hDe
  exact neighbour_standard hL htC ht hKt hq hn e k htX hX.ge hDe hD

theorem bLift_neighbour_rootTorusSp (hL : standardComponentIsStandard L) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hq : 4 ≤ Nat.card K) (hn : 2 ≤ n) (e : L ≃* StatedSp (n + 1) K) (k : Fin (n + 1))
    {X : Subgroup G} (hX : X = ((rootTorusSp K k).map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G}
    (hDe : D = ((complSp K k).map e.symm.toMonoidHom).map L.subtype) :
    (∀ c ∈ centralizer (X : Set G) ⊓ centralizer ({t} : Set G) ⊓ centralizer (D : Set G),
      Odd (orderOf c) → c ∈ X) ∧
      (∀ c ∈ oddCore (centralizer (X : Set G)), c * ⟨t, htX⟩ = ⟨t, htX⟩ * c →
        c ∈ center (centralizer (X : Set G))) ∧
      ∀ E : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
        ⁅E, E⁆ = E →
        QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ ∈
          normalizer (E : Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) →
        E ≤ ⁅E, zpowers (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)⁆ →
        HasBLift E := by
  have hLt := CFSG.EvenSmallLie.centralizer_le_normalizer_of_standard hL htC ht
  obtain ⟨-, -, -, -, -, hD, -⟩ := neighbour_data_rootTorusSp hq hn e k htC hX hDe
  have hDq : CFSG.IsQuasisimple D := hDe ▸ isQuasisimple_map_complSp hq (by omega) e k
  have hmax := mem_of_odd_of_mem_centralizer_rootTorusSp htC ht hLt hKt hq hn e k hX hDe
  exact ⟨hmax,
    LinearPilot.mem_center_of_mem_oddCore_of_commute_of_forall_odd_mem htC hLt htX hD hDq hmax,
    fun E hE htE hEt => LinearPilot.hasBLift_of_forall_odd_mem htC ht hLt htX hD hDq hmax hE htE
      hEt⟩

end RootTorus

section Siegel

variable {G : Type*} [Group G] {L : Subgroup G} [Finite K] [CharP K 2]

theorem neighbour_data_siegelTorus (hq : 4 ≤ Nat.card K) (hn : 3 ≤ n) (e : L ≃* StatedSp n K)
    {t : G} (htC : t ∈ centralizer (L : Set G))
    {X : Subgroup G} (hX : X = ((siegelTorus K n).map e.symm.toMonoidHom).map L.subtype)
    {D : Subgroup G} (hDe : D = ((siegelLevi K n).map e.symm.toMonoidHom).map L.subtype) :
    X ≤ L ∧ t ∈ centralizer (X : Set G) ∧ Odd (Nat.card X) ∧
      D = inSubgroup layer (L ⊓ centralizer (X : Set G)) ∧
      D ≤ centralizer (X : Set G) ⊓ centralizer ({t} : Set G) ∧
      CFSG.Open.IsQuasisimple D ∧ Nonempty (D ≃* Matrix.SpecialLinearGroup (Fin n) K) ∧
      Odd (Nat.card (center D)) ∧ Group.IsSolvable (Outer (D ⧸ center D)) := by
  subst hX hDe
  set ψ : (((siegelLevi K n).map e.symm.toMonoidHom).map L.subtype : Subgroup G) ≃*
      Matrix.SpecialLinearGroup (Fin n) K :=
    (LinearPilot.mapSymmMulEquiv e (siegelLevi K n)).trans siegelLeviEquiv.symm
  have hC := centralizer_siegelTorus (n := n) hq
  exact ⟨map_subtype_le _, LinearPilot.mem_centralizer_map_symm e _ htC,
    (LinearPilot.card_map_symm e _).symm ▸ odd_card_siegelTorus,
    (layer_inf_centralizer_siegelTorus hq (by omega) e).symm,
    le_inf (LinearPilot.map_symm_le_centralizer_map_symm e (siegelLevi_le_siegelLeviGL.trans hC.ge))
      (LinearPilot.map_symm_le_centralizer_singleton e _ htC),
    isQuasisimple_open_map_siegelLevi hq (by omega) e, ⟨ψ⟩,
    LinearPilot.odd_card_center_of_mulEquiv (by omega) ψ,
    LinearPilot.isSolvable_outer_quotient_center_of_mulEquiv hn ψ⟩

variable [Finite G]

theorem neighbour_standard_siegel (hL : standardComponentIsStandard L) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hq : 4 ≤ Nat.card K) (hn : 3 ≤ n) (e : L ≃* StatedSp n K)
    {X : Subgroup G} (htX : t ∈ centralizer (X : Set G))
    (hX : ((siegelTorus K n).map e.symm.toMonoidHom).map L.subtype ≤ X) {D : Subgroup G}
    (hDe : D = ((siegelLevi K n).map e.symm.toMonoidHom).map L.subtype)
    (hD : D = inSubgroup layer (L ⊓ centralizer (X : Set G))) :
    CFSG.Open.IsComponentOf
        ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))))
        (centralizer ({QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩} :
          Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))))) ∧
      (∀ U : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
        IsPGroup 2 U →
        U ≤ centralizer ((D.subgroupOf (centralizer (X : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) :
          Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) →
        Nat.card U ≤ 2) ∧
      standardComponentIsStandard ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) :=
  F4Pilot.standard_inheritance_of_forall_fix_eq_one hL htC ht hKt htX hD
    (hDe ▸ isQuasisimple_open_map_siegelLevi hq (by omega) e)
    (eq_one_of_fix_map_siegelTorus hq hn e hX hDe.ge)

theorem neighbour_standard_siegelTorus (hL : standardComponentIsStandard L) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hq : 4 ≤ Nat.card K) (hn : 3 ≤ n) (e : L ≃* StatedSp n K)
    {X : Subgroup G} (hX : X = ((siegelTorus K n).map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G}
    (hDe : D = ((siegelLevi K n).map e.symm.toMonoidHom).map L.subtype) :
    CFSG.Open.IsComponentOf
        ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))))
        (centralizer ({QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩} :
          Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))))) ∧
      (∀ U : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
        IsPGroup 2 U →
        U ≤ centralizer ((D.subgroupOf (centralizer (X : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) :
          Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) →
        Nat.card U ≤ 2) ∧
      standardComponentIsStandard ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) := by
  obtain ⟨-, -, -, hD, -⟩ := neighbour_data_siegelTorus hq hn e htC hX hDe
  exact neighbour_standard_siegel hL htC ht hKt hq hn e htX hX.ge hDe hD

theorem bLift_neighbour_siegelTorus (hL : standardComponentIsStandard L) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hq : 4 ≤ Nat.card K) (hn : 3 ≤ n) (e : L ≃* StatedSp n K)
    {X : Subgroup G} (hX : X = ((siegelTorus K n).map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G}
    (hDe : D = ((siegelLevi K n).map e.symm.toMonoidHom).map L.subtype) :
    (∀ c ∈ centralizer (X : Set G) ⊓ centralizer ({t} : Set G) ⊓ centralizer (D : Set G),
      Odd (orderOf c) → c ∈ X) ∧
      (∀ c ∈ oddCore (centralizer (X : Set G)), c * ⟨t, htX⟩ = ⟨t, htX⟩ * c →
        c ∈ center (centralizer (X : Set G))) ∧
      ∀ E : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
        ⁅E, E⁆ = E →
        QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ ∈
          normalizer (E : Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) →
        E ≤ ⁅E, zpowers (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)⁆ →
        HasBLift E := by
  have hLt := CFSG.EvenSmallLie.centralizer_le_normalizer_of_standard hL htC ht
  obtain ⟨-, -, -, hD, -⟩ := neighbour_data_siegelTorus hq hn e htC hX hDe
  have hDq : CFSG.IsQuasisimple D := hDe ▸ isQuasisimple_map_siegelLevi hq (by omega) e
  have hmax := mem_of_odd_of_mem_centralizer_siegelTorus htC ht hLt hKt hq hn e hX hDe
  exact ⟨hmax,
    LinearPilot.mem_center_of_mem_oddCore_of_commute_of_forall_odd_mem htC hLt htX hD hDq hmax,
    fun E hE htE hEt => LinearPilot.hasBLift_of_forall_odd_mem htC ht hLt htX hD hDq hmax hE htE
      hEt⟩

end Siegel

section Setting

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem inf_centralizer_eq_zpowers_of_mulEquiv (hset : SeitzSetting G L) {r f : ℕ}
    (hKc : Nat.card K = 2 ^ f) (hr : 3 ≤ r) (e : L ≃* StatedSp r K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) :
    centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t :=
  inf_centralizer_eq_zpowers hset hr (lieModel_of_mulEquiv_statedSp e hKc (by omega)
    (fun h => by simp only [Prod.mk.injEq] at h; omega)) htC ht

theorem neighbour_standard_rootTorusSp_of_seitzSetting (hset : SeitzSetting G L) {f : ℕ}
    (hKc : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K) (hn : 2 ≤ n) (e : L ≃* StatedSp (n + 1) K)
    {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) (k : Fin (n + 1))
    {X : Subgroup G} (hX : X = ((rootTorusSp K k).map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G}
    (hDe : D = ((complSp K k).map e.symm.toMonoidHom).map L.subtype) :
    CFSG.Open.IsComponentOf
        ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))))
        (centralizer ({QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩} :
          Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))))) ∧
      (∀ U : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
        IsPGroup 2 U →
        U ≤ centralizer ((D.subgroupOf (centralizer (X : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) :
          Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) →
        Nat.card U ≤ 2) ∧
      standardComponentIsStandard ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) := by
  have := LinearPilot.finite_of_card_eq_two_pow hKc
  have := LinearPilot.charP_two_of_card_eq_two_pow hKc
  exact neighbour_standard_rootTorusSp hset.standardSetting.standard htC ht
    (inf_centralizer_eq_zpowers_of_mulEquiv hset hKc (by omega) e htC ht) hq hn e k hX htX hDe

theorem bLift_neighbour_rootTorusSp_of_seitzSetting (hset : SeitzSetting G L) {f : ℕ}
    (hKc : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K) (hn : 2 ≤ n) (e : L ≃* StatedSp (n + 1) K)
    {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) (k : Fin (n + 1))
    {X : Subgroup G} (hX : X = ((rootTorusSp K k).map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G}
    (hDe : D = ((complSp K k).map e.symm.toMonoidHom).map L.subtype) :
    (∀ c ∈ centralizer (X : Set G) ⊓ centralizer ({t} : Set G) ⊓ centralizer (D : Set G),
      Odd (orderOf c) → c ∈ X) ∧
      (∀ c ∈ oddCore (centralizer (X : Set G)), c * ⟨t, htX⟩ = ⟨t, htX⟩ * c →
        c ∈ center (centralizer (X : Set G))) ∧
      ∀ E : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
        ⁅E, E⁆ = E →
        QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ ∈
          normalizer (E : Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) →
        E ≤ ⁅E, zpowers (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)⁆ →
        HasBLift E := by
  have := LinearPilot.finite_of_card_eq_two_pow hKc
  have := LinearPilot.charP_two_of_card_eq_two_pow hKc
  exact bLift_neighbour_rootTorusSp hset.standardSetting.standard htC ht
    (inf_centralizer_eq_zpowers_of_mulEquiv hset hKc (by omega) e htC ht) hq hn e k hX htX hDe

theorem neighbour_standard_siegelTorus_of_seitzSetting (hset : SeitzSetting G L) {f : ℕ}
    (hKc : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K) (hn : 3 ≤ n) (e : L ≃* StatedSp n K)
    {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    {X : Subgroup G} (hX : X = ((siegelTorus K n).map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G}
    (hDe : D = ((siegelLevi K n).map e.symm.toMonoidHom).map L.subtype) :
    CFSG.Open.IsComponentOf
        ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))))
        (centralizer ({QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩} :
          Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))))) ∧
      (∀ U : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
        IsPGroup 2 U →
        U ≤ centralizer ((D.subgroupOf (centralizer (X : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) :
          Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) →
        Nat.card U ≤ 2) ∧
      standardComponentIsStandard ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) := by
  have := LinearPilot.finite_of_card_eq_two_pow hKc
  have := LinearPilot.charP_two_of_card_eq_two_pow hKc
  exact neighbour_standard_siegelTorus hset.standardSetting.standard htC ht
    (inf_centralizer_eq_zpowers_of_mulEquiv hset hKc hn e htC ht) hq hn e hX htX hDe

theorem bLift_neighbour_siegelTorus_of_seitzSetting (hset : SeitzSetting G L) {f : ℕ}
    (hKc : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K) (hn : 3 ≤ n) (e : L ≃* StatedSp n K)
    {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    {X : Subgroup G} (hX : X = ((siegelTorus K n).map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G}
    (hDe : D = ((siegelLevi K n).map e.symm.toMonoidHom).map L.subtype) :
    (∀ c ∈ centralizer (X : Set G) ⊓ centralizer ({t} : Set G) ⊓ centralizer (D : Set G),
      Odd (orderOf c) → c ∈ X) ∧
      (∀ c ∈ oddCore (centralizer (X : Set G)), c * ⟨t, htX⟩ = ⟨t, htX⟩ * c →
        c ∈ center (centralizer (X : Set G))) ∧
      ∀ E : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
        ⁅E, E⁆ = E →
        QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ ∈
          normalizer (E : Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) →
        E ≤ ⁅E, zpowers (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)⁆ →
        HasBLift E := by
  have := LinearPilot.finite_of_card_eq_two_pow hKc
  have := LinearPilot.charP_two_of_card_eq_two_pow hKc
  exact bLift_neighbour_siegelTorus hset.standardSetting.standard htC ht
    (inf_centralizer_eq_zpowers_of_mulEquiv hset hKc hn e htC ht) hq hn e hX htX hDe

end Setting

end CFSG.SeitzReduction.SymplecticPilot
