module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotNeighbourStandard
public import CFSG.LocalAnalysis.SeitzReduction.SeitzBranches
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotSetup

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.Open CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem neighbour_standard_torusQ1_of_seitzSetting (hset : SeitzSetting G L) {n f : ℕ}
    {K : Type} [Field K] (hKc : Nat.card K = 2 ^ f) (e : L ≃* LinearFlag.projectiveSL n K)
    (hn : 5 ≤ n) {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    {a b : Fin n} (hab : a ≠ b)
    {X₀ : Subgroup (LinearFlag.projectiveSL n K)} (hX₀ : X₀ ≤ rootSL2 a b)
    (hX₀c : Nat.card X₀ = Nat.card K + 1)
    {X : Subgroup G} (hX : X = (X₀.map e.symm.toMonoidHom).map L.subtype)
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
  exact neighbour_standard_torusQ1 hset.standardSetting.standard htC ht
    (inf_centralizer_eq_zpowers hset e hKc (by omega) htC ht) e hn hab hX₀ hX₀c hX htX hDe

theorem four_le_card_of_seitzSetting (hset : SeitzSetting G L) {f : ℕ} {K : Type} [Field K]
    (hKc : Nat.card K = 2 ^ f) (e : L ≃* LinearFlag.projectiveSL 4 K) : 4 ≤ Nat.card K := by
  have h := ne_four_one_of_mulEquiv hset e hKc
  have h1 := one_le_of_card_eq_two_pow hKc
  refine (four_le_card_iff_two_le hKc).2 ?_
  by_contra h2
  exact h (by rw [show f = 1 by omega])

theorem neighbour_standard_levTorus_of_seitzSetting (hset : SeitzSetting G L) {f : ℕ}
    {K : Type} [Field K] (hKc : Nat.card K = 2 ^ f) (e : L ≃* LinearFlag.projectiveSL 4 K)
    {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) (a : Fin 4)
    {X : Subgroup G} (hX : X = ((levTorus (K := K) a).map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G}
    (hDe : D = ((blockSL (({a} : Finset (Fin 4))ᶜ)).map e.symm.toMonoidHom).map L.subtype) :
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
  exact neighbour_standard_levTorus_four hset.standardSetting.standard htC ht
    (inf_centralizer_eq_zpowers hset e hKc le_rfl htC ht) e
    (four_le_card_of_seitzSetting hset hKc e) a hX htX hDe

end CFSG.SeitzReduction.LinearPilot
