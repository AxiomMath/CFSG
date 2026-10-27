module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusEightBasic
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotBLift
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotNeighbourStandard

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup CFSG.Open
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (coordinateQuadMinus regular_coordinateQuadMinus)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.SeitzReduction.F4Pilot (HasBLift oddCoreLift)

section Data

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
variable {G : Type} [Group G] {L : Subgroup G}

theorem neighbour_data_minusPairTorus_of_four_le {f : ℕ} (hKc : Nat.card K = 2 ^ f)
    (hq : 4 ≤ Nat.card K) (hn : 4 ≤ n) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (k : Fin (n - 1)) (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c))
    {t : G} (htC : t ∈ centralizer (L : Set G)) {X : Subgroup G}
    (hX : X = ((minusPairTorus (K := K) (by omega) b c k).map e.symm.toMonoidHom).map L.subtype)
    {D : Subgroup G}
    (hDe : D = ((minusPairPerp (K := K) (by omega) b c k).map e.symm.toMonoidHom).map L.subtype) :
    X ≤ L ∧ t ∈ centralizer (X : Set G) ∧ IsCyclic X ∧ Nat.card X = Nat.card K - 1 ∧
      Odd (Nat.card X) ∧ D = inSubgroup layer (L ⊓ centralizer (X : Set G)) ∧
      D ≤ centralizer (X : Set G) ⊓ centralizer ({t} : Set G) ∧ CFSG.IsQuasisimple D ∧
      center D = ⊥ ∧ Group.IsSolvable (Outer D) := by
  subst hX hDe
  have hDk := isQuasisimple_minusPairPerp_of_four_le (K := K) hn hirr k
  set ψ := LinearPilot.mapSymmMulEquiv e (minusPairPerp (K := K) (by omega : 1 ≤ n) b c k)
    with hψ
  have hOut := isSolvable_outer_minusPairPerp_of_four_le hKc hn hirr k
  have hZ : center ((minusPairPerp (K := K) (by omega : 1 ≤ n) b c k).map e.symm.toMonoidHom |>.map
      L.subtype) = ⊥ := by
    rw [← CFSG.ComponentClassification.OuterAutomorphisms.center_map_equiv ψ.symm,
      center_minusPairPerp_of_four_le hn hirr k, Subgroup.map_bot]
  refine ⟨map_subtype_le _, LinearPilot.mem_centralizer_map_symm e _ htC,
    LinearPilot.isCyclic_map_symm e (isCyclic_minusPairTorus _ b c k),
    (LinearPilot.card_map_symm e _).trans (card_minusPairTorus _ b c k),
    (LinearPilot.card_map_symm e _).symm ▸ odd_card_minusPairTorus hKc _ b c k,
    (F4Pilot.inSubgroup_layer_inf_centralizer_map_symm e (centralizer_minusPairTorus hq _ b c k)
      (isHypCoord_coordinateQuadMinus _ b c k).pairTorusOf_le_centralizer_pairPerpOf
      (F4Pilot.le_centralizer_self_of_isCyclic (isCyclic_minusPairTorus _ b c k)) hDk).symm,
    le_inf (LinearPilot.map_symm_le_centralizer_map_symm e
      ((isHypCoord_coordinateQuadMinus _ b c k).pairPerpOf_le_centralizer hq))
      (LinearPilot.map_symm_le_centralizer_singleton e _ htC),
    CFSG.LocalCores.isQuasisimple_of_mulEquiv ψ.symm hDk,
    hZ,
    CFSG.ComponentClassification.OuterAutomorphisms.solvable_of_equiv ψ.symm⟩

theorem lieModel_map_minusPairPerp_four {f : ℕ} (hKc : Nat.card K = 2 ^ f) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (k : Fin (4 - 1))
    (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus 4 K (by omega) b c)) {D : Subgroup G}
    (hDe : D = ((minusPairPerp (K := K) (n := 4) (by omega) b c k).map
      e.symm.toMonoidHom).map L.subtype) :
    CFSG.Blueprint.LieModel D .PSU 4 2 f := by
  subst hDe
  exact lieModel_of_mulEquiv
    (LinearPilot.mapSymmMulEquiv e (minusPairPerp (K := K) (n := 4) _ b c k)).symm
    (lieModel_minusPairPerp_four hKc hirr k)

end Data

section Standard

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem neighbour_standard_minusPairTorus_of_four_le (hL : standardComponentIsStandard L) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hq : 4 ≤ Nat.card K) (hn : 4 ≤ n) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (k : Fin (n - 1)) (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c))
    {X : Subgroup G}
    (hX : X = ((minusPairTorus (K := K) (by omega) b c k).map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G}
    (hDe : D = ((minusPairPerp (K := K) (by omega) b c k).map e.symm.toMonoidHom).map L.subtype) :
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
  neighbour_standard_of_mulEquiv hL htC ht hK e (centralizer_minusPairTorus hq _ b c k)
    (isHypCoord_coordinateQuadMinus _ b c k).pairTorusOf_le_centralizer_pairPerpOf
    (F4Pilot.le_centralizer_self_of_isCyclic (isCyclic_minusPairTorus _ b c k))
    (isQuasisimple_minusPairPerp_of_four_le hn hirr k)
    (fun _ hX hD _ hβ => eq_one_of_two_pow_fix_minusPairTorus hq hn hirr k hβ hX hD)
    hX htX hDe

end Standard

section Setting

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem neighbour_standard_minusPairTorus_of_seitzSetting_of_four_le (hset : SeitzSetting G L)
    {n f : ℕ} {K : Type} [Field K] (hKc : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K) (hn : 4 ≤ n)
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (k : Fin (n - 1))
    (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c)) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {X : Subgroup G}
    (hX : X = ((minusPairTorus (K := K) (by omega) b c k).map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G}
    (hDe : D = ((minusPairPerp (K := K) (by omega) b c k).map e.symm.toMonoidHom).map L.subtype) :
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
  exact neighbour_standard_minusPairTorus_of_four_le hset.standardSetting.standard htC ht
    (inf_centralizer_eq_zpowers_minus hset hn hKc hirr e htC ht) hq hn hirr k e hX htX hDe

theorem bLift_inputs_minusPairTorus_of_four_le (hset : SeitzSetting G L) {n f : ℕ} {K : Type}
    [Field K] (hKc : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K) (hn : 4 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (k : Fin (n - 1))
    (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c)) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {X : Subgroup G}
    (hX : X = ((minusPairTorus (K := K) (by omega) b c k).map e.symm.toMonoidHom).map L.subtype)
    {D : Subgroup G}
    (hDe : D = ((minusPairPerp (K := K) (by omega) b c k).map e.symm.toMonoidHom).map L.subtype) :
    centralizer ({t} : Set G) ≤ normalizer (L : Set G) ∧
      D = inSubgroup layer (L ⊓ centralizer (X : Set G)) ∧ CFSG.IsQuasisimple D ∧
      ∀ c ∈ centralizer (X : Set G) ⊓ centralizer ({t} : Set G) ⊓ centralizer (D : Set G),
        Odd (orderOf c) → c ∈ X := by
  have := LinearPilot.finite_of_card_eq_two_pow hKc
  have := LinearPilot.charP_two_of_card_eq_two_pow hKc
  obtain ⟨-, -, -, -, -, hD, -, hDq, -⟩ :=
    neighbour_data_minusPairTorus_of_four_le hKc hq hn hirr k e htC hX hDe
  exact ⟨CFSG.EvenSmallLie.centralizer_le_normalizer_of_standard hset.standardSetting.standard
    htC ht, hD, hDq, fun _ hc hco => mem_minusPairTorus_of_odd_of_commute hset hKc hq hn hirr k e
      htC ht hX hDe hc hco⟩

end Setting

end CFSG.SeitzReduction.OmegaPilot
