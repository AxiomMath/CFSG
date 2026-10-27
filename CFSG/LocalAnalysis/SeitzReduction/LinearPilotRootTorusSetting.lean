module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotRootTorusNeighbour
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotPositionBNotNormal
public import CFSG.LocalAnalysis.SeitzReduction.SeitzBranches
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotSetup
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotBLift

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.Open CFSG.LocalAnalysis.ComponentInitial
open CFSG.SeitzReduction.F4Pilot (HasBLift oddCoreLift)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

section NotNormal

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem not_normal_map_oddCore_rootTorus (hset : CFSG.EvenSmallLie.StandardSetting G L)
    (hOut : Group.IsSolvable (Outer L)) {n : ℕ} {K : Type*} [Field K] [Finite K] [CharP K 2]
    (hq : 4 ≤ Nat.card K) (hn : 5 ≤ n) (e : L ≃* LinearFlag.projectiveSL n K) {t : G}
    (ht : orderOf t = 2) (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {a b : Fin n} (hab : a ≠ b) {X : Subgroup G}
    (hX : X = ((rootTorus (K := K) hab).map e.symm.toMonoidHom).map L.subtype) {g y : G}
    (hyD : y ∈ ((blockSL (K := K) ({a, b}ᶜ : Finset (Fin n))).map e.symm.toMonoidHom).map
      L.subtype)
    (hy : orderOf y = 2) (hg : g⁻¹ * t * g = t * y) :
    ¬ (((((blockSL (K := K) ({a, b}ᶜ : Finset (Fin n))).map e.symm.toMonoidHom).map
        L.subtype).subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))).Normal := by
  have htK : t ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) := hKt ▸ mem_zpowers t
  have htC : t ∈ centralizer (L : Set G) := htK.1
  obtain ⟨-, htX, -, hXo, hXJ, -, hDC, hDq, -, hZD, hOutD⟩ :=
    neighbour_data_rootTorus e hn hq hab htC hX rfl
  have hstd := neighbour_standard_rootTorus hset.standard htC ht hKt e hn hq hab hX htX rfl
  exact not_normal_map_oddCore_of_conj_eq_mul hset hOut hq (by omega) e ht hKt hab hXo hXJ hyD hy
    hg htX (hDC.trans inf_le_left) hDq hZD hOutD hstd.2.1

end NotNormal

section Seitz

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem neighbour_standard_rootTorus_of_seitzSetting (hset : SeitzSetting G L) {n f : ℕ}
    {K : Type} [Field K] (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f)
    (e : L ≃* LinearFlag.projectiveSL n K) (hn : 5 ≤ n) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {a b : Fin n} (hab : a ≠ b)
    {X : Subgroup G}
    (hX : X = ((rootTorus (K := K) hab).map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G}
    (hDe : D = ((blockSL (({a, b} : Finset (Fin n))ᶜ)).map e.symm.toMonoidHom).map L.subtype) :
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
  have := finite_of_card_eq_two_pow hKc
  have := charP_two_of_card_eq_two_pow hKc
  exact neighbour_standard_rootTorus hset.standardSetting.standard htC ht
    (inf_centralizer_eq_zpowers hset e hKc (by omega) htC ht) e hn
    ((four_le_card_iff_two_le hKc).2 hf) hab hX htX hDe

theorem not_normal_map_oddCore_rootTorus_of_seitzSetting (hset : SeitzSetting G L) {n f : ℕ}
    {K : Type} [Field K] (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f)
    (e : L ≃* LinearFlag.projectiveSL n K) (hn : 5 ≤ n) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {a b : Fin n} (hab : a ≠ b)
    {X : Subgroup G}
    (hX : X = ((rootTorus (K := K) hab).map e.symm.toMonoidHom).map L.subtype) {g y : G}
    (hyD : y ∈ ((blockSL (K := K) ({a, b}ᶜ : Finset (Fin n))).map e.symm.toMonoidHom).map
      L.subtype)
    (hy : orderOf y = 2) (hg : g⁻¹ * t * g = t * y) :
    ¬ (((((blockSL (K := K) ({a, b}ᶜ : Finset (Fin n))).map e.symm.toMonoidHom).map
        L.subtype).subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))).Normal := by
  have := finite_of_card_eq_two_pow hKc
  have := charP_two_of_card_eq_two_pow hKc
  exact not_normal_map_oddCore_rootTorus hset.standardSetting
    (isSolvable_outer_of_mulEquiv (by omega) e) ((four_le_card_iff_two_le hKc).2 hf) hn e ht
    (inf_centralizer_eq_zpowers hset e hKc (by omega) htC ht) hab hX hyD hy hg

end Seitz

end CFSG.SeitzReduction.LinearPilot
