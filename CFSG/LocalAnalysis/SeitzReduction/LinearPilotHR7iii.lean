module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotHR7iiiLevi
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotNeighbourStandardSetting
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotFusionGenericSetting

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.Open CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

omit [Finite G] in
theorem coe_mem_map_symm {n : ℕ} {K : Type*} [Field K] (e : L ≃* LinearFlag.projectiveSL n K)
    {B : Subgroup (LinearFlag.projectiveSL n K)} {z : L} (hz : e z ∈ B) :
    (z : G) ∈ (B.map e.symm.toMonoidHom).map L.subtype :=
  ⟨z, ⟨e z, hz, by simp⟩, rfl⟩

omit [Finite G] in
theorem orderOf_coe_eq_two_of_isInvolutionClass_one {n : ℕ} {K : Type*} [Field K] [CharP K 2]
    (e : L ≃* LinearFlag.projectiveSL n K) {z : L} (hz : IsInvolutionClass 1 (e z)) :
    orderOf (z : G) = 2 := by
  rw [Subgroup.orderOf_coe, ← MulEquiv.orderOf_eq e z]
  exact hz.orderOf_eq_two one_ne_zero

theorem not_normal_neighbour_levTorus (hset : SeitzSetting G L) {f : ℕ} {K : Type} [Field K]
    (hKc : Nat.card K = 2 ^ f) (e : L ≃* LinearFlag.projectiveSL 4 K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hR5 : ∃ (g : G) (z : L), IsInvolutionClass 1 (e z) ∧ g⁻¹ * t * g = t * (z : G))
    (a : Fin 4) {X : Subgroup G}
    (hX : X = ((levTorus (K := K) a).map e.symm.toMonoidHom).map L.subtype) {D : Subgroup G}
    (hDe : D = ((blockSL (({a} : Finset (Fin 4))ᶜ)).map e.symm.toMonoidHom).map L.subtype) :
    ¬ ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))).Normal := by
  have := finite_of_card_eq_two_pow hKc
  have := charP_two_of_card_eq_two_pow hKc
  have hq := four_le_card_of_seitzSetting hset hKc e
  have hKt := inf_centralizer_eq_zpowers hset e hKc le_rfl htC ht
  have hOut := isSolvable_outer_of_mulEquiv (by norm_num : 3 ≤ 4) e
  obtain ⟨-, htX, hXcyc, hXodd, -, hDC, hDq, -, hZ, hOutD⟩ :=
    neighbour_data_levTorus e le_rfl a (exists_pow_four_ne_one hq) htC hX hDe
  obtain ⟨-, hsyl, -⟩ := neighbour_standard_levTorus_of_seitzSetting hset hKc e htC ht a hX htX hDe
  have hI : 2 ≤ (({a} : Finset (Fin 4))ᶜ).card := by
    rw [Finset.card_compl, Finset.card_singleton, Fintype.card_fin]
    omega
  obtain ⟨g, y, hy1, hyD, hg⟩ :=
    exists_conj_eq_mul_mem_blockSL e (le_centralizer_of_mem_centralizer htC) hI hR5
  have hXt : X ≤ centralizer ({t} : Set G) := fun x hx =>
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 htX x hx)
  subst hDe
  exact not_normal_map_oddCore_of_conj_eq_mul_levi hset.standardSetting hOut hq e ht hKt a hXcyc
    hXodd hXt (hDC.trans inf_le_left) (coe_mem_map_symm e hyD)
    (orderOf_coe_eq_two_of_isInvolutionClass_one e hy1) hg hDq hZ hOutD hsyl

end CFSG.SeitzReduction.LinearPilot
