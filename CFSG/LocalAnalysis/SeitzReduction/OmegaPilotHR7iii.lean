module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotF6
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotFusion
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotNeighbourStandard
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPositionRouteBSingle
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotNeighbourStandard

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.Open
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (plusIndexEquiv coordinateQuadPlus regular_coordinateQuadPlus)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

section Setting

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

omit [Finite G] in
theorem exists_recentred_of_twoSided {X : Type*} [Group X] (e : L ≃* X) {t : G}
    (htC : t ∈ centralizer (L : Set G)) {x z : G} (hzL : z ∈ L) (hzx : z ∈ CFSG.conjugate L x)
    (hxz : x⁻¹ * t * x = t * z) (hact : ∀ l ∈ CFSG.conjugate L x, t * l * t⁻¹ = z * l * z⁻¹)
    {z₀ : X} (hc : IsConj (e ⟨z, hzL⟩) z₀) :
    ∃ g : G, g⁻¹ * t * g = t * (e.symm z₀ : G) ∧ ∃ w' : G, g * w' * g⁻¹ ∈ L ∧
      (∀ l ∈ CFSG.conjugate L g, t * l * t⁻¹ = w' * l * w'⁻¹) ∧ g * w' * g⁻¹ = x * z * x⁻¹ := by
  obtain ⟨c', hc'⟩ := isConj_iff.mp hc
  set c : L := e.symm c'⁻¹ with hcdef
  have htc : ∀ m ∈ L, t * m = m * t := fun m hm => (mem_centralizer_iff.mp htC m hm).symm
  have hxzx : x * z * x⁻¹ ∈ L := by
    obtain ⟨m, hm, hmz⟩ := hzx
    rw [← hmz]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [show x * (x⁻¹ * m * x) * x⁻¹ = m by group]
    exact hm
  refine ⟨x * c, ?_, (c : G)⁻¹ * z * c, ?_, ?_, ?_⟩
  · have h := conj_mul_eq_mul_conj htC (z := ⟨z, hzL⟩) hxz c
    rw [h]
    congr 2
    apply e.injective
    rw [MulEquiv.apply_symm_apply, map_mul, map_mul, map_inv, hcdef, MulEquiv.apply_symm_apply,
      inv_inv, ← hc']
  · rw [show x * (c : G) * ((c : G)⁻¹ * z * c) * (x * c)⁻¹ = x * z * x⁻¹ by group]
    exact hxzx
  · intro l hl
    obtain ⟨m, hm, rfl⟩ := hl
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    have hm' : x⁻¹ * m * x ∈ CFSG.conjugate L x :=
      ⟨m, hm, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]⟩
    have h := hact _ hm'
    have hc1 : t * (c : G) = c * t := htc _ c.2
    have hc2 : t * (c : G)⁻¹ = (c : G)⁻¹ * t := htc _ (inv_mem c.2)
    calc t * ((x * c)⁻¹ * m * (x * c)) * t⁻¹
        = (c : G)⁻¹ * (t * (x⁻¹ * m * x) * t⁻¹) * c := by
          rw [show (x * (c : G))⁻¹ * m * (x * c) = (c : G)⁻¹ * (x⁻¹ * m * x) * c by group]
          rw [← mul_assoc t, ← mul_assoc t, hc2]
          have hc3 : (c : G) * t⁻¹ = t⁻¹ * c := by
            rw [mul_inv_eq_iff_eq_mul, mul_assoc, ← hc1, ← mul_assoc, inv_mul_cancel, one_mul]
          rw [mul_assoc _ (c : G) t⁻¹, hc3]
          group
      _ = (c : G)⁻¹ * (z * (x⁻¹ * m * x) * z⁻¹) * c := by rw [h]
      _ = ((c : G)⁻¹ * z * c) * ((x * c)⁻¹ * m * (x * c)) * ((c : G)⁻¹ * z * c)⁻¹ := by group
  · group

end Setting

section Main

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem not_normal_neighbour_pairTorus_of_twoSided (hset : SeitzSetting G L) {n f : ℕ}
    {K : Type} [Field K] (hKc : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K) (hn : 5 ≤ n)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus n K)) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hR5 : ∃ x : G, ∃ z ∈ L ⊓ CFSG.conjugate L x, x⁻¹ * t * x = t * z ∧
      (∃ hz : z ∈ L, IsLongRoot _ (e ⟨z, hz⟩)) ∧
      (∃ hz : z ∈ CFSG.conjugate L x,
        IsLongRoot _ (((conjugateMulEquiv L x).symm.trans e) ⟨z, hz⟩)) ∧
      ∀ l ∈ CFSG.conjugate L x, t * l * t⁻¹ = z * l * z⁻¹)
    (k : Fin n) {X D : Subgroup G}
    (hX : X = ((pairTorus (K := K) k).map e.symm.toMonoidHom).map L.subtype)
    (hDe : D = ((pairPerp (K := K) k).map e.symm.toMonoidHom).map L.subtype) :
    ¬ ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))).Normal := by
  have := LinearPilot.finite_of_card_eq_two_pow hKc
  have := LinearPilot.charP_two_of_card_eq_two_pow hKc
  obtain ⟨i, j, hij, hik, hjk⟩ := exists_pair_ne_fin (by omega : 3 ≤ n) k
  obtain ⟨hz₀D, hz₀L, hF3, hQz, hMN, hQM, hM, hJ⟩ := plusRootElt_decomp hq hn hij hik hjk
  have hF6 := refinedF6_pairTorus hq hn hij hik hjk
  set z₀ := plusRootElt K (by omega) hij hik hjk with hz₀
  obtain ⟨x, z, -, hxz, ⟨hzL, hzl⟩, ⟨hzx, hzl'⟩, hact⟩ := hR5
  obtain ⟨g, hg, w', hw', hact', hgw⟩ := exists_recentred_of_twoSided e htC hzL hzx hxz hact
    (isConj_of_isLongRoot_plus (by omega) hzl hz₀L)
  have hconj : IsConj (e ⟨g * w' * g⁻¹, hw'⟩) z₀ := by
    have hw : (⟨g * w' * g⁻¹, hw'⟩ : L) = (conjugateMulEquiv L x).symm ⟨z, hzx⟩ := by
      apply (conjugateMulEquiv L x).injective
      rw [MulEquiv.apply_symm_apply]
      apply Subtype.ext
      rw [coe_conjugateMulEquiv]
      change x⁻¹ * (g * w' * g⁻¹) * x = z
      rw [hgw]
      group
    rw [hw]
    exact isConj_of_isLongRoot_plus (by omega) hzl' hz₀L
  have hOut := isSolvable_outer_of_mulEquiv_plus (by omega)
    (LinearPilot.one_le_of_card_eq_two_pow hKc) hKc e
  have hKt := inf_centralizer_eq_zpowers_plus hset (by omega) hKc e htC ht
  obtain ⟨P, hP, hPD⟩ := EPilot.exists_le_centralizer_mulEquiv_of_conj_eq_mul_single_of_isConj
    hset.standardSetting hOut e ht hKt hg ⟨w', hw', hact', hconj⟩ (plusRadical K i j)
    (plusLevi K i j) hF3 hQz hMN hQM hM hJ (odd_card_pairTorus hKc k) hF6
  obtain ⟨-, htX, -, -, -, -, hDC, hDq, hZD, -, hOutD⟩ :=
    neighbour_data_pairTorus hKc hq hn k e htC hX hDe
  obtain ⟨-, hsyl, -⟩ :=
    neighbour_standard_pairTorus_of_seitzSetting hset hKc hq hn k e htC ht hX htX hDe
  have hyD : (e.symm z₀ : G) ∈ D := by
    rw [hDe]
    exact ⟨e.symm z₀, ⟨z₀, hz₀D, rfl⟩, rfl⟩
  have hy1 : (e.symm z₀ : G) ≠ 1 := by
    intro h1
    have h2 : e.symm z₀ = 1 := Subtype.ext h1
    rw [MulEquiv.symm_apply_eq, map_one] at h2
    exact rootPairElt_ne_one _ _ _ _ h2
  have hP' : P ≤ centralizer (X : Set G) ⊓ centralizer ({t * (e.symm z₀ : G)} : Set G) := by
    rw [hX, ← hg]
    exact hP
  have hPD' : Nonempty (P ≃* D) := by
    obtain ⟨ePD⟩ := hPD
    subst hDe
    exact ⟨ePD.trans (LinearPilot.mapSymmMulEquiv e (pairPerp (K := K) k)).symm⟩
  exact F4Pilot.not_normal_map_oddCore_centralizer_of_mulEquiv htX ht (hDC.trans inf_le_left)
    ⟨hDq.1.commutator_eq_top, hDq.2.1⟩ hZD hOutD (hDC.trans inf_le_right) hsyl hyD hy1
    (Or.inr rfl) hP' hPD'

theorem not_normal_neighbour_pairTorus_of_habel (hset : SeitzSetting G L) {n f : ℕ}
    {K : Type} [Field K] (hKc : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K) (hn : 5 ≤ n)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus n K)) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (habel : ∀ S : Sylow 2 G, (S : Subgroup G) ≤ centralizer ({t} : Set G) →
      ∀ y ∈ (S : Subgroup G), ∀ z ∈ (S : Subgroup G), y * z * y⁻¹ * z⁻¹ ∈ L)
    (k : Fin n) {X D : Subgroup G}
    (hX : X = ((pairTorus (K := K) k).map e.symm.toMonoidHom).map L.subtype)
    (hDe : D = ((pairPerp (K := K) k).map e.symm.toMonoidHom).map L.subtype) :
    ¬ ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))).Normal := by
  have := LinearPilot.finite_of_card_eq_two_pow hKc
  have := LinearPilot.charP_two_of_card_eq_two_pow hKc
  have hKt := inf_centralizer_eq_zpowers_plus hset (by omega) hKc e htC ht
  exact not_normal_neighbour_pairTorus_of_twoSided hset hKc hq hn e htC ht
    (exists_conj_eq_mul_longRoot_twoSided_plus_of_habel hset hn hKc hq e ht hKt habel) k hX hDe

theorem not_normal_neighbour_pairTorus_of_odd (hset : SeitzSetting G L) {n f : ℕ} (hf : Odd f)
    {K : Type} [Field K] (hKc : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K) (hn : 5 ≤ n)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus n K)) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) (k : Fin n) {X D : Subgroup G}
    (hX : X = ((pairTorus (K := K) k).map e.symm.toMonoidHom).map L.subtype)
    (hDe : D = ((pairPerp (K := K) k).map e.symm.toMonoidHom).map L.subtype) :
    ¬ ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))).Normal := by
  have := LinearPilot.finite_of_card_eq_two_pow hKc
  have hKt := inf_centralizer_eq_zpowers_plus hset (by omega) hKc e htC ht
  exact not_normal_neighbour_pairTorus_of_habel hset hKc hq hn e htC ht
    (habel_plus_of_odd hset hn hf hKc e ht hKt) k hX hDe

end Main

end CFSG.SeitzReduction.OmegaPilot
