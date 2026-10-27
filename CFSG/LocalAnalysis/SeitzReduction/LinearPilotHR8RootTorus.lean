module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotHR8
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotRootTorusSetting
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotSetup

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.Blueprint CFSG.Open CFSG.LocalAnalysis.ComponentInitial

section Basic

theorem lieModel_quotient_center_of_mulEquiv_specialLinear {D : Type} [Group D] {K : Type}
    [Field K] {m f : ℕ} (hK : Nat.card K = 2 ^ f) (hm : 3 ≤ m)
    (φ : D ≃* Matrix.SpecialLinearGroup (Fin m) K) : LieModel (D ⧸ center D) .PSL m 2 f := by
  have := finite_of_card_eq_two_pow hK
  have hf : 1 ≤ f := one_le_of_card_eq_two_pow hK
  refine Or.inl ⟨by decide, ⟨Nat.prime_two, hf, by omega, fun h => ?_, fun h => ?_⟩, K,
    inferInstance, inferInstance, hK, ⟨(quotientCenterEquivProjectiveSL φ).trans
      ((LinearCover.projectiveSpecialLinearEquivProjectiveSL m K).symm.trans
        (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj m K))⟩⟩
  · rw [Prod.mk.injEq] at h
    omega
  · rw [Prod.mk.injEq] at h
    omega

theorem IsRootSplit.proj_ne_one {K : Type*} [Field K] {n : ℕ} {a b : Fin n}
    {h : Matrix.SpecialLinearGroup (Fin n) K} (hh : IsRootSplit a b h) :
    LinearFlag.proj n K h ≠ 1 := by
  rw [Ne, LinearFlag.proj_eq_one_iff, LinearFlag.mem_scalars]
  rintro ⟨c, -, hc⟩
  apply hh.2.2
  rw [hc, Matrix.scalar_apply, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]

theorem rootTorus_ne_bot {K : Type*} [Field K] [Finite K] {n : ℕ} (hq : 4 ≤ Nat.card K)
    {a b : Fin n} (hab : a ≠ b) : rootTorus (K := K) hab ≠ ⊥ := by
  obtain ⟨h, hh, hhX⟩ := exists_isRootSplit_proj_mem_rootTorus (n := n) hq hab
  intro hbot
  rw [hbot, mem_bot] at hhX
  exact hh.proj_ne_one hhX

private theorem centralizer_ne_top_of_ne_bot' {G : Type*} [Group G] (hG : IsSimpleGroup G)
    (hnonab : ∃ a b : G, a * b ≠ b * a) {X : Subgroup G} (hX : X ≠ ⊥) :
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

theorem neighbour_overgroup_rootTorus_of_not_normal (hset : SeitzSetting G L) {n f : ℕ}
    (hcat : SLmCatalogueClausesAt (n - 2)) {K : Type} [Field K] (hKc : Nat.card K = 2 ^ f)
    (hf : 2 ≤ f) (e : L ≃* LinearFlag.projectiveSL n K) (hn : 5 ≤ n) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {a b : Fin n} (hab : a ≠ b)
    {X : Subgroup G}
    (hX : X = ((rootTorus (K := K) hab).map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G}
    (hDe : D = ((blockSL (({a, b} : Finset (Fin n))ᶜ)).map e.symm.toMonoidHom).map L.subtype)
    (hnn : ¬ ((D.subgroupOf (centralizer (X : Set G))).map
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))).Normal) :
    NeighbourOvergroupSLm (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
      ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) (n - 2) f := by
  have := finite_of_card_eq_two_pow hKc
  have := charP_two_of_card_eq_two_pow hKc
  have hq : 4 ≤ Nat.card K := (four_le_card_iff_two_le hKc).2 hf
  have hcard : (({a, b} : Finset (Fin n))ᶜ).card = n - 2 := by
    rw [Finset.card_compl, Fintype.card_fin, Finset.card_pair hab]
  obtain ⟨hcomp, hsyl, hstd⟩ :=
    neighbour_standard_rootTorus_of_seitzSetting hset hKc hf e hn htC ht hab hX htX hDe
  obtain ⟨-, -, -, -, -, -, hDC, -, ⟨φ⟩, -, -⟩ :=
    neighbour_data_rootTorus e hn hq hab htC hX hDe
  have hDq : CFSG.IsQuasisimple D :=
    hDe ▸ isQuasisimple_map_blockSL e (by omega) (by omega) (Or.inl (by omega))
  have hXne : X ≠ ⊥ := by
    rw [hX, Ne, map_eq_bot_iff_of_injective _ L.subtype_injective,
      map_eq_bot_iff_of_injective _ e.symm.injective]
    exact rootTorus_ne_bot hq hab
  exact neighbour_overgroup_slm_center (by omega) (Or.inr hf) hcat hset.standardSetting.kProper
    (centralizer_ne_top_of_ne_bot' hset.standardSetting.simple hset.standardSetting.nonab hXne)
    htX ht (hDC.trans inf_le_left) hDq
    (lieModel_quotient_center_of_mulEquiv_specialLinear hKc (by omega) φ) hcomp hsyl hstd hnn

theorem neighbour_overgroup_rootTorus (hset : SeitzSetting G L) {n f : ℕ}
    (hcat : SLmCatalogueClausesAt (n - 2)) {K : Type} [Field K] (hKc : Nat.card K = 2 ^ f)
    (hf : 2 ≤ f) (e : L ≃* LinearFlag.projectiveSL n K) (hn : 5 ≤ n) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {a b : Fin n} (hab : a ≠ b)
    {X : Subgroup G}
    (hX : X = ((rootTorus (K := K) hab).map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G}
    (hDe : D = ((blockSL (({a, b} : Finset (Fin n))ᶜ)).map e.symm.toMonoidHom).map L.subtype)
    {g y : G} (hyD : y ∈ D) (hy : orderOf y = 2) (hg : g⁻¹ * t * g = t * y) :
    NeighbourOvergroupSLm (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
      ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) (n - 2) f := by
  subst hDe
  exact neighbour_overgroup_rootTorus_of_not_normal hset hcat hKc hf e hn htC ht hab hX htX rfl
    (not_normal_map_oddCore_rootTorus_of_seitzSetting hset hKc hf e hn htC ht hab hX hyD hy hg)

end Seitz

end CFSG.SeitzReduction.LinearPilot
