module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR8RootTorus
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotHR8Field

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Blueprint CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.SeitzReduction.LinearPilot (NeighbourOvergroupSLm NeighbourOvergroupSLmField
  SLmCatalogueClausesAt SLmEvenTypeDetAt)

section Nontrivial

variable {K : Type} [Field K] {n : ℕ}

theorem siegelTorus_ne_bot (hK : 4 ≤ Nat.card K) (hn : 1 ≤ n) : siegelTorus K n ≠ ⊥ := by
  obtain ⟨κ, hκ⟩ := exists_units_mul_self_ne_one_of_four_le hK
  intro hbot
  have hmem : diagSp K n (fun _ => κ) ∈ siegelTorus K n := ⟨κ, rfl⟩
  rw [hbot, mem_bot, ← map_one (diagSp K n)] at hmem
  have h1 := congrFun (diagSp_injective hmem) ⟨0, by omega⟩
  exact units_ne_one_of_mul_self_ne_one hκ h1

theorem map_siegelTorus_ne_bot {G : Type*} [Group G] {L : Subgroup G} (hK : 4 ≤ Nat.card K)
    (hn : 1 ≤ n) (e : L ≃* StatedSp n K) :
    ((siegelTorus K n).map e.symm.toMonoidHom).map L.subtype ≠ ⊥ := by
  rw [Ne, map_eq_bot_iff_of_injective _ L.subtype_injective,
    map_eq_bot_iff_of_injective _ e.symm.injective]
  exact siegelTorus_ne_bot hK hn

end Nontrivial

section Siegel

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K]

theorem siegel_normal_or_overgroup {n f : ℕ} (hcat : SLmCatalogueClausesAt n)
    (hset : SeitzSetting G L) (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (hn : 3 ≤ n)
    (e : L ≃* StatedSp n K) {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    {X : Subgroup G} (hX : X = ((siegelTorus K n).map e.symm.toMonoidHom).map L.subtype)
    {D : Subgroup G} (hD : D = ((siegelLevi K n).map e.symm.toMonoidHom).map L.subtype) :
    ∃ htX : t ∈ centralizer (X : Set G),
      ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))).Normal ∨
        NeighbourOvergroupSLm (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
          ((D.subgroupOf (centralizer (X : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) n f := by
  have : Finite K := LinearPilot.finite_of_card_eq_two_pow hKc
  have : CharP K 2 := LinearPilot.charP_two_of_card_eq_two_pow hKc
  have hq : 4 ≤ Nat.card K := hKc ▸ four_le_two_pow hf
  obtain ⟨-, htX, -, -, hDXt, -, ⟨ψ⟩, -, -⟩ := neighbour_data_siegelTorus hq hn e htC hX hD
  obtain ⟨hcomp, hsyl, hstd⟩ :=
    neighbour_standard_siegelTorus_of_seitzSetting hset hKc hq hn e htC ht hX htX hD
  refine ⟨htX, ?_⟩
  by_cases hnn : ((D.subgroupOf (centralizer (X : Set G))).map
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))).Normal
  · exact Or.inl hnn
  · right
    have hDq : CFSG.IsQuasisimple D := hD ▸ isQuasisimple_map_siegelLevi hq (by omega) e
    have hDm : LieModel (D ⧸ center D) .PSL n 2 f :=
      LinearPilot.lieModel_quotient_center_of_mulEquiv_specialLinear hKc hn ψ
    have hXG : centralizer (X : Set G) ≠ ⊤ :=
      centralizer_ne_top_of_ne_bot_of_simple hset.standardSetting.simple
        hset.standardSetting.nonab (hX ▸ map_siegelTorus_ne_bot hq (by omega) e)
    exact LinearPilot.neighbour_overgroup_slm_center hn (Or.inr hf) hcat
      hset.standardSetting.kProper hXG htX ht (hDXt.trans inf_le_left) hDq hDm hcomp hsyl hstd hnn

theorem siegel_normal_or_overgroup_field {n f : ℕ} (hcat : SLmCatalogueClausesAt n)
    (hdet : SLmEvenTypeDetAt n) (hset : SeitzSetting G L) (hKc : Nat.card K = 2 ^ f)
    (hf : 2 ≤ f) (hn : 3 ≤ n) (e : L ≃* StatedSp n K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    {X : Subgroup G} (hX : X = ((siegelTorus K n).map e.symm.toMonoidHom).map L.subtype)
    {D : Subgroup G} (hD : D = ((siegelLevi K n).map e.symm.toMonoidHom).map L.subtype) :
    ∃ htX : t ∈ centralizer (X : Set G),
      ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))).Normal ∨
        (NeighbourOvergroupSLmField
            (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
            ((D.subgroupOf (centralizer (X : Set G))).map
              (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) n f ∧
          center ((D.subgroupOf (centralizer (X : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) = ⊥) := by
  have : Finite K := LinearPilot.finite_of_card_eq_two_pow hKc
  have : CharP K 2 := LinearPilot.charP_two_of_card_eq_two_pow hKc
  have hq : 4 ≤ Nat.card K := hKc ▸ four_le_two_pow hf
  obtain ⟨-, -, -, -, hDXt, -, ⟨ψ⟩, -, -⟩ := neighbour_data_siegelTorus hq hn e htC hX hD
  obtain ⟨htX, hcase⟩ := siegel_normal_or_overgroup hcat hset hKc hf hn e htC ht hX hD
  refine ⟨htX, hcase.imp id fun h => ?_⟩
  obtain ⟨hcomp, -, -⟩ :=
    neighbour_standard_siegelTorus_of_seitzSetting hset hKc hq hn e htC ht hX htX hD
  have hDq : CFSG.IsQuasisimple D := hD ▸ isQuasisimple_map_siegelLevi hq (by omega) e
  exact h.field_oddCore htX ht (hDXt.trans inf_le_left) hDq hn (Or.inr hf) hdet
    (LinearPilot.lieModel_quotient_center_of_mulEquiv_specialLinear hKc hn ψ) hcomp

end Siegel

end CFSG.SeitzReduction.SymplecticPilot
