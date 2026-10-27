module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotHR8Field
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotHR7iii

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial

section Basic

theorem levTorus_ne_bot {K : Type*} [Field K] {n : ℕ} (hn : 2 ≤ n) (a : Fin n) {c : Kˣ}
    (hc : c ^ n ≠ 1) : levTorus (K := K) a ≠ ⊥ := by
  obtain ⟨i, hi⟩ : ∃ i : Fin n, i ≠ a := by
    by_cases ha : (a : ℕ) = 0
    · refine ⟨⟨1, by omega⟩, fun h => ?_⟩
      rw [← h] at ha
      exact absurd ha (by simp)
    · exact ⟨⟨0, by omega⟩, fun h => ha (by rw [← h])⟩
  intro hbot
  have hmem := proj_levTorusHom_mem (K := K) a c
  rw [hbot, mem_bot, LinearFlag.proj_eq_one_iff, LinearFlag.mem_scalars] at hmem
  obtain ⟨μ, -, hμ⟩ := hmem
  apply levDiag_ne (by omega) hc hi
  rw [coe_levTorusHom] at hμ
  have h1 := congrFun (congrFun hμ a) a
  have h2 := congrFun (congrFun hμ i) i
  rw [Matrix.diagonal_apply_eq] at h1 h2
  rw [h1, h2, Matrix.scalar_apply, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]

theorem centralizer_ne_top_of_ne_bot_of_isSimpleGroup {G : Type*} [Group G]
    (hG : IsSimpleGroup G) (hnonab : ∃ a b : G, a * b ≠ b * a) {X : Subgroup G} (hX : X ≠ ⊥) :
    centralizer (X : Set G) ≠ ⊤ := by
  intro htop
  obtain ⟨a, b, hab⟩ := hnonab
  apply hX
  rcases hG.eq_bot_or_eq_top_of_normal (center G) with hZ | hZ
  · rw [eq_bot_iff, ← hZ]
    intro x hx
    rw [mem_center_iff]
    intro g
    exact (mem_centralizer_iff.mp (htop ▸ mem_top g) x hx).symm
  · exact absurd (mem_center_iff.mp (hZ ▸ mem_top b) a) hab

end Basic

section Seitz

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem neighbour_overgroup_levTorus_of_not_normal (hset : SeitzSetting G L)
    (hcat : SLmCatalogueClausesAt 3) {f : ℕ} {K : Type} [Field K] (hKc : Nat.card K = 2 ^ f)
    (hf : 2 ≤ f) (e : L ≃* LinearFlag.projectiveSL 4 K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) (a : Fin 4) {X : Subgroup G}
    (hX : X = ((levTorus (K := K) a).map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G}
    (hDe : D = ((blockSL (({a} : Finset (Fin 4))ᶜ)).map e.symm.toMonoidHom).map L.subtype)
    (hnn : ¬ ((D.subgroupOf (centralizer (X : Set G))).map
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))).Normal) :
    NeighbourOvergroupSLm (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
      ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) 3 f := by
  have := finite_of_card_eq_two_pow hKc
  have := charP_two_of_card_eq_two_pow hKc
  have hq : 4 ≤ Nat.card K := (four_le_card_iff_two_le hKc).2 hf
  obtain ⟨hcomp, hsyl, hstd⟩ :=
    neighbour_standard_levTorus_of_seitzSetting hset hKc e htC ht a hX htX hDe
  obtain ⟨c, hc⟩ := exists_pow_four_ne_one hq
  obtain ⟨-, -, -, -, -, hDC, -, ⟨φ⟩, -, -⟩ :=
    neighbour_data_levTorus e le_rfl a ⟨c, hc⟩ htC hX hDe
  have hcard : (({a} : Finset (Fin 4))ᶜ).card = 3 := by
    rw [Finset.card_compl, Finset.card_singleton, Fintype.card_fin]
  have hDq : CFSG.IsQuasisimple D :=
    hDe ▸ isQuasisimple_map_blockSL e (by omega) (by omega) (Or.inl (by omega))
  have hXne : X ≠ ⊥ := by
    rw [hX, Ne, map_eq_bot_iff_of_injective _ L.subtype_injective,
      map_eq_bot_iff_of_injective _ e.symm.injective]
    exact levTorus_ne_bot (by norm_num) a hc
  exact neighbour_overgroup_slm_center le_rfl (Or.inr hf) hcat hset.standardSetting.kProper
    (centralizer_ne_top_of_ne_bot_of_isSimpleGroup hset.standardSetting.simple
      hset.standardSetting.nonab hXne)
    htX ht (hDC.trans inf_le_left) hDq
    (lieModel_quotient_center_of_mulEquiv_specialLinear hKc le_rfl φ) hcomp hsyl hstd hnn

theorem neighbour_overgroup_levTorus (hset : SeitzSetting G L) (hcat : SLmCatalogueClausesAt 3)
    {f : ℕ} {K : Type} [Field K] (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f)
    (e : L ≃* LinearFlag.projectiveSL 4 K) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2)
    (hR5 : ∃ (g : G) (z : L), IsInvolutionClass 1 (e z) ∧ g⁻¹ * t * g = t * (z : G))
    (a : Fin 4) {X : Subgroup G}
    (hX : X = ((levTorus (K := K) a).map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G}
    (hDe : D = ((blockSL (({a} : Finset (Fin 4))ᶜ)).map e.symm.toMonoidHom).map L.subtype) :
    NeighbourOvergroupSLm (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
      ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) 3 f :=
  neighbour_overgroup_levTorus_of_not_normal hset hcat hKc hf e htC ht a hX htX hDe
    (not_normal_neighbour_levTorus hset hKc e htC ht hR5 a hX hDe)

theorem neighbour_overgroup_levTorus_field (hset : SeitzSetting G L)
    (hcat : SLmCatalogueClausesAt 3) (hdet : SLmEvenTypeDetAt 3) {f : ℕ} {K : Type} [Field K]
    (hKc : Nat.card K = 2 ^ f)
    (hf : 2 ≤ f) (e : L ≃* LinearFlag.projectiveSL 4 K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hR5 : ∃ (g : G) (z : L), IsInvolutionClass 1 (e z) ∧ g⁻¹ * t * g = t * (z : G))
    (a : Fin 4) {X : Subgroup G}
    (hX : X = ((levTorus (K := K) a).map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G}
    (hDe : D = ((blockSL (({a} : Finset (Fin 4))ᶜ)).map e.symm.toMonoidHom).map L.subtype) :
    NeighbourOvergroupSLmField (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
        ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) 3 f ∧
      center ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) = ⊥ := by
  have := finite_of_card_eq_two_pow hKc
  have := charP_two_of_card_eq_two_pow hKc
  have hq : 4 ≤ Nat.card K := (four_le_card_iff_two_le hKc).2 hf
  obtain ⟨hcomp, -, -⟩ :=
    neighbour_standard_levTorus_of_seitzSetting hset hKc e htC ht a hX htX hDe
  obtain ⟨c, hc⟩ := exists_pow_four_ne_one hq
  obtain ⟨-, -, -, -, -, hDC, -, ⟨φ⟩, -, -⟩ :=
    neighbour_data_levTorus e le_rfl a ⟨c, hc⟩ htC hX hDe
  have hcard : (({a} : Finset (Fin 4))ᶜ).card = 3 := by
    rw [Finset.card_compl, Finset.card_singleton, Fintype.card_fin]
  have hDq : CFSG.IsQuasisimple D :=
    hDe ▸ isQuasisimple_map_blockSL e (by omega) (by omega) (Or.inl (by omega))
  exact (neighbour_overgroup_levTorus hset hcat hKc hf e htC ht hR5 a hX htX
    hDe).field_oddCore htX ht (hDC.trans inf_le_left) hDq le_rfl (Or.inr hf)
    hdet (lieModel_quotient_center_of_mulEquiv_specialLinear hKc le_rfl φ)
    hcomp

end Seitz

end CFSG.SeitzReduction.LinearPilot
