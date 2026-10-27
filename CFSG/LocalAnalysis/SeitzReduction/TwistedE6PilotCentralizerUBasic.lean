module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCentralizerYF3Exact
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneTwistedE6CascadeBasic
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotCentralizerTBasic

public section

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint
open CFSG.Quasithin (perfectCore perfectCore_le perfectCore_mono map_perfectCore
  le_perfectCore_of_perfect perfectCore_eq_self_of_perfect)

local instance twistedE6PilotCentralizerUBasicNeZero : NeZero Tag.E6.rank := ⟨by decide⟩

local instance twistedE6PilotCentralizerUBasicNeZeroF4 : NeZero Tag.F4.rank := ⟨by decide⟩

local instance twistedE6PilotCentralizerUBasicNeZeroTw : NeZero TwistTag.E6.tag.rank :=
  ⟨by decide⟩

section General

variable {G : Type*} [Group G]

theorem map_conj_inv_map_conj (H : Subgroup G) (n : G) :
    (H.map (MulAut.conj n).toMonoidHom).map (MulAut.conj n⁻¹).toMonoidHom = H := by
  rw [Subgroup.map_map]
  convert Subgroup.map_id H
  ext x
  simp only [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.id_apply]
  change n⁻¹ * (n * x * n⁻¹) * n⁻¹⁻¹ = x
  group

end General


section ClassU

variable {K : Type} [Field K]

theorem twistedE6ClassU_eq_e6ASRep :
    twistedE6ClassU K = (E6Pilot.e6ASRep K 1 : ModGL .E6 K) := by
  rw [E6Pilot.coe_e6ASRep_one_eq, twistedE6ClassU]
  have hα : IsRoot .E6 E6Pilot.yAlphaAS :=
    mem_rootFinset.1 (by decide +kernel : E6Pilot.yAlphaAS ∈ rootFinset .E6)
  have hβ : IsRoot .E6 E6Pilot.yBetaAS :=
    mem_rootFinset.1 (by decide +kernel : E6Pilot.yBetaAS ∈ rootFinset .E6)
  have h0 : 0 ≤ iform E6Pilot.yBetaAS E6Pilot.yAlphaAS := by decide
  exact (classD4_commute_pinnedX E6Pilot.e6_simplyLaced hβ hα h0 1 1).eq

end ClassU

section Core


variable {K : Type} [Field K]

theorem perfectCore_centralizer_e6ASRep_one [Finite K] [CharP K 2] :
    perfectCore (centralizer ({E6Pilot.e6ASRep K 1} : Set (adjointGroup .E6 K))) =
      (parabolicRadical .E6 K E6Pilot.nodes16).subgroupOf (adjointGroup .E6 K) ⊔
        (E6Pilot.yLeviF4 K).subgroupOf (adjointGroup .E6 K) := by
  have : Finite (ModGL .E6 K) := finite_modGL
  have hy : (E6Pilot.e6RepConj K 1)⁻¹ * E6Pilot.e6Rep K 1 * (E6Pilot.e6RepConj K 1)⁻¹⁻¹ =
      E6Pilot.e6ASRep K 1 := by
    rw [← E6Pilot.e6RepConj_mul_e6ASRep_mul_inv (K := K) 1]
    group
  set n : adjointGroup .E6 K := E6Pilot.e6RepConj K 1 with hn
  have hQ : (parabolicRadical .E6 K E6Pilot.nodes16) ≤ adjointGroup .E6 K :=
    (parabolicRadical_le_posUnipotent _).trans posUnipotent_le_adjointGroup
  have hL : E6Pilot.yLeviF4 K ≤ adjointGroup .E6 K := by
    have h := E6Pilot.yLeviGL_le_adjointGroup (K := K)
    rw [E6Pilot.yLeviGL_eq_map_yLeviF4] at h
    intro x hx
    have hx' : (n : ModGL .E6 K) * x * (n : ModGL .E6 K)⁻¹ ∈ adjointGroup .E6 K :=
      h ⟨x, hx, rfl⟩
    have e : x = (n : ModGL .E6 K)⁻¹ * ((n : ModGL .E6 K) * x * (n : ModGL .E6 K)⁻¹) *
        (n : ModGL .E6 K) := by group
    rw [e]
    exact mul_mem (mul_mem (inv_mem n.2) hx') n.2
  rw [← hy, centralizer_conj_eq_map, ← map_perfectCore, (E6Pilot.factF3y (K := K)).1,
    Subgroup.map_sup]
  congr 1
  · rw [E6Pilot.yRadical, CFSG.LieType.Chevalley.map_conj_subgroupOf
      (E6Pilot.rootSpan_yRadicalRoots_le_adjointGroup) n⁻¹,
      E6Pilot.rootSpan_yRadicalRoots_eq_map, coe_inv]
    rw [map_conj_inv_map_conj]
  · rw [E6Pilot.yLevi, CFSG.LieType.Chevalley.map_conj_subgroupOf
      E6Pilot.yLeviGL_le_adjointGroup n⁻¹, E6Pilot.yLeviGL_eq_map_yLeviF4, coe_inv]
    rw [map_conj_inv_map_conj]

end Core

section Factors

variable {K : Type} [Field K]

theorem iform_permLattice_yLamAS_check : ∀ γ ∈ rootFinset .E6,
    iform (permLattice TwistTag.E6.perm γ) E6Pilot.yLamAS = iform γ E6Pilot.yLamAS := by
  decide +kernel

theorem permLattice_mem_parabolicRadicalRoots_nodes16 {γ : Fin Tag.E6.rank → ℤ}
    (hγ : γ ∈ parabolicRadicalRoots .E6 E6Pilot.nodes16) :
    permLattice TwistTag.E6.perm γ ∈ parabolicRadicalRoots .E6 E6Pilot.nodes16 := by
  rw [E6Pilot.parabolicRadicalRoots_nodes16] at hγ ⊢
  refine ⟨hγ.1.permLattice TwistTag.E6.cartan_perm, ?_⟩
  exact lt_of_lt_of_eq hγ.2 (iform_permLattice_yLamAS_check γ (mem_rootFinset.2 hγ.1)).symm

theorem twistHom_mem_parabolicRadical_nodes16 [CharP K 2] (σ : K →+* K) {g : ModGL .E6 K}
    (hg : g ∈ parabolicRadical .E6 K E6Pilot.nodes16) :
    twistHom TwistTag.E6 K σ g ∈ parabolicRadical .E6 K E6Pilot.nodes16 :=
  twistHom_mem_rootSpan_of_perm σ (fun _ hβ => hβ.1.1)
    (fun _ hβ => permLattice_mem_parabolicRadicalRoots_nodes16 hβ) hg

theorem commute_xUnit_two_four (c d : K) :
    Commute (xUnit .E6 K 2 c) (xUnit .E6 K 4 d) ∧ Commute (yUnit .E6 K 2 c) (yUnit .E6 K 4 d) := by
  have h0 : 0 ≤ iform (Pi.single 2 1 : Fin Tag.E6.rank → ℤ) (Pi.single 4 1) := by decide
  have h0' : 0 ≤ iform (-Pi.single 2 1 : Fin Tag.E6.rank → ℤ) (-Pi.single 4 1) := by decide
  refine ⟨?_, ?_⟩
  · rw [← pinnedX_single, ← pinnedX_single]
    exact classD4_commute_pinnedX E6Pilot.e6_simplyLaced (isRoot_single _ _) (isRoot_single _ _)
      h0 c d
  · rw [← pinnedX_neg_single, ← pinnedX_neg_single]
    exact classD4_commute_pinnedX E6Pilot.e6_simplyLaced (isRoot_neg_single _ _)
      (isRoot_neg_single _ _) h0' c d


theorem perm_nodes_check : TwistTag.E6.perm 1 = 1 ∧ TwistTag.E6.perm 3 = 3 ∧
    TwistTag.E6.perm 2 = 4 ∧ TwistTag.E6.perm 4 = 2 := by
  decide

theorem twistHom_mem_yLeviF4Gens (σ : K →+* K) {g : ModGL .E6 K}
    (hg : g ∈ E6Pilot.yLeviF4Gens K) :
    twistHom TwistTag.E6 K σ g ∈ E6Pilot.yLeviF4Gens K := by
  obtain ⟨h1, h3, h2, h4⟩ := perm_nodes_check
  obtain ⟨j, hj, c, rfl | rfl⟩ := hg
  · refine ⟨j, hj, σ c, Or.inl ?_⟩
    rcases (by decide : ∀ j : Fin Tag.F4.rank, j ≠ 3 → j = 0 ∨ j = 1 ∨ j = 2) j hj with
      rfl | rfl | rfl
    · rw [E6Pilot.f4OrbitXUnit_zero, E6Pilot.f4OrbitXUnit_zero]
      exact (twistHom_xUnit TwistTag.E6 K σ 1 c).trans (by rw [h1]; rfl)
    · rw [E6Pilot.f4OrbitXUnit_one, E6Pilot.f4OrbitXUnit_one]
      exact (twistHom_xUnit TwistTag.E6 K σ 3 c).trans (by rw [h3]; rfl)
    · rw [E6Pilot.f4OrbitXUnit_two, E6Pilot.f4OrbitXUnit_two]
      change twistHom TwistTag.E6 K σ (xUnit TwistTag.E6.tag K 2 c * xUnit TwistTag.E6.tag K 4 c) = _
      rw [map_mul, twistHom_xUnit, twistHom_xUnit, h2, h4]
      exact ((commute_xUnit_two_four _ _).1).symm.eq
  · refine ⟨j, hj, σ c, Or.inr ?_⟩
    rcases (by decide : ∀ j : Fin Tag.F4.rank, j ≠ 3 → j = 0 ∨ j = 1 ∨ j = 2) j hj with
      rfl | rfl | rfl
    · rw [E6Pilot.f4OrbitYUnit_zero, E6Pilot.f4OrbitYUnit_zero]
      exact (twistHom_yUnit TwistTag.E6 K σ 1 c).trans (by rw [h1]; rfl)
    · rw [E6Pilot.f4OrbitYUnit_one, E6Pilot.f4OrbitYUnit_one]
      exact (twistHom_yUnit TwistTag.E6 K σ 3 c).trans (by rw [h3]; rfl)
    · rw [E6Pilot.f4OrbitYUnit_two, E6Pilot.f4OrbitYUnit_two]
      change twistHom TwistTag.E6 K σ (yUnit TwistTag.E6.tag K 2 c * yUnit TwistTag.E6.tag K 4 c) = _
      rw [map_mul, twistHom_yUnit, twistHom_yUnit, h2, h4]
      exact ((commute_xUnit_two_four _ _).2).symm.eq

theorem twistHom_mem_yLeviF4 (σ : K →+* K) {g : ModGL .E6 K} (hg : g ∈ E6Pilot.yLeviF4 K) :
    twistHom TwistTag.E6 K σ g ∈ E6Pilot.yLeviF4 K := by
  have hle : E6Pilot.yLeviF4 K ≤ (E6Pilot.yLeviF4 K).comap (twistHom TwistTag.E6 K σ) :=
    (closure_le _).2 fun x hx => subset_closure (twistHom_mem_yLeviF4Gens σ hx)
  exact hle hg

theorem yLeviF4_le_rootSpan_parabolicRoots :
    E6Pilot.yLeviF4 K ≤ rootSpan .E6 K (parabolicRoots .E6 E6Pilot.nodes16) := by
  have hx : ∀ i : Fin Tag.E6.rank, i ≠ 0 → i ≠ 5 → ∀ c : K,
      xUnit .E6 K i c ∈ rootSpan .E6 K (parabolicRoots .E6 E6Pilot.nodes16) := by
    intro i h0 h5 c
    rw [← pinnedX_single]
    have hmem : (Pi.single i 1 : Fin Tag.E6.rank → ℤ) ∈ parabolicRoots .E6 E6Pilot.nodes16 := by
      refine ⟨isRoot_single _ _, fun j hj => ?_⟩
      have hj' : j = 0 ∨ j = 5 := by
        by_contra h
        exact hj ⟨fun h0 => h (Or.inl h0), fun h5 => h (Or.inr h5)⟩
      rcases hj' with rfl | rfl
      · simp [Ne.symm h0]
      · simp [Ne.symm h5]
    exact pinnedX_mem_rootSpan hmem c
  have hy : ∀ i : Fin Tag.E6.rank, i ≠ 0 → i ≠ 5 → ∀ c : K,
      yUnit .E6 K i c ∈ rootSpan .E6 K (parabolicRoots .E6 E6Pilot.nodes16) := by
    intro i h0 h5 c
    rw [← pinnedX_neg_single]
    have hmem : (-Pi.single i 1 : Fin Tag.E6.rank → ℤ) ∈ parabolicRoots .E6 E6Pilot.nodes16 := by
      refine ⟨isRoot_neg_single _ _, fun j hj => ?_⟩
      have hj' : j = 0 ∨ j = 5 := by
        by_contra h
        exact hj ⟨fun h0 => h (Or.inl h0), fun h5 => h (Or.inr h5)⟩
      rcases hj' with rfl | rfl
      · simp [Ne.symm h0]
      · simp [Ne.symm h5]
    exact pinnedX_mem_rootSpan hmem c
  refine (closure_le _).2 ?_
  rintro _ ⟨j, hj, c, rfl | rfl⟩
  · rcases (by decide : ∀ j : Fin Tag.F4.rank, j ≠ 3 → j = 0 ∨ j = 1 ∨ j = 2) j hj with
      rfl | rfl | rfl
    · change _ ∈ rootSpan .E6 K (parabolicRoots .E6 E6Pilot.nodes16)
      rw [E6Pilot.f4OrbitXUnit_zero]
      exact hx 1 (by decide) (by decide) c
    · change _ ∈ rootSpan .E6 K (parabolicRoots .E6 E6Pilot.nodes16)
      rw [E6Pilot.f4OrbitXUnit_one]
      exact hx 3 (by decide) (by decide) c
    · change _ ∈ rootSpan .E6 K (parabolicRoots .E6 E6Pilot.nodes16)
      rw [E6Pilot.f4OrbitXUnit_two]
      exact mul_mem (hx 2 (by decide) (by decide) c) (hx 4 (by decide) (by decide) c)
  · rcases (by decide : ∀ j : Fin Tag.F4.rank, j ≠ 3 → j = 0 ∨ j = 1 ∨ j = 2) j hj with
      rfl | rfl | rfl
    · change _ ∈ rootSpan .E6 K (parabolicRoots .E6 E6Pilot.nodes16)
      rw [E6Pilot.f4OrbitYUnit_zero]
      exact hy 1 (by decide) (by decide) c
    · change _ ∈ rootSpan .E6 K (parabolicRoots .E6 E6Pilot.nodes16)
      rw [E6Pilot.f4OrbitYUnit_one]
      exact hy 3 (by decide) (by decide) c
    · change _ ∈ rootSpan .E6 K (parabolicRoots .E6 E6Pilot.nodes16)
      rw [E6Pilot.f4OrbitYUnit_two]
      exact mul_mem (hy 2 (by decide) (by decide) c) (hy 4 (by decide) (by decide) c)

theorem yLeviF4_le_normalizer_parabolicRadical :
    E6Pilot.yLeviF4 K ≤
      normalizer (parabolicRadical .E6 K E6Pilot.nodes16 : Set (ModGL .E6 K)) :=
  yLeviF4_le_rootSpan_parabolicRoots.trans
    (F4Pilot.rootSpan_parabolicRoots_le_normalizer E6Pilot.nodes16)

theorem parabolicRadical_inf_yLeviF4 :
    parabolicRadical .E6 K E6Pilot.nodes16 ⊓ E6Pilot.yLeviF4 K = ⊥ :=
  eq_bot_iff.2 ((inf_le_inf_left _ yLeviF4_le_rootSpan_parabolicRoots).trans
    (F4Pilot.parabolicRadical_inf_rootSpan E6Pilot.nodes16).le)

theorem exists_mul_of_mem_sup_of_twistHom_eq [CharP K 2] (σ : K →+* K) {g : ModGL .E6 K}
    (hg : g ∈ parabolicRadical .E6 K E6Pilot.nodes16 ⊔ E6Pilot.yLeviF4 K)
    (hF : twistHom TwistTag.E6 K σ g = g) :
    ∃ q ∈ parabolicRadical .E6 K E6Pilot.nodes16, ∃ l ∈ E6Pilot.yLeviF4 K,
      twistHom TwistTag.E6 K σ q = q ∧ twistHom TwistTag.E6 K σ l = l ∧ g = q * l := by
  have huniq := E6GraphHighestRootNormalizer.existsUnique_mul_of_le_normalizer
    (parabolicRadical_inf_yLeviF4 (K := K)) (yLeviF4_le_normalizer_parabolicRadical (K := K))
  obtain ⟨⟨q, l⟩, ⟨hq, hl, rfl⟩, hu⟩ := huniq g hg
  have hFq := twistHom_mem_parabolicRadical_nodes16 σ hq
  have hFl := twistHom_mem_yLeviF4 σ hl
  have h := hu (twistHom TwistTag.E6 K σ q, twistHom TwistTag.E6 K σ l)
    ⟨hFq, hFl, hF.symm.trans (map_mul (twistHom TwistTag.E6 K σ) q l)⟩
  obtain ⟨h1, h2⟩ := Prod.ext_iff.1 h
  exact ⟨q, hq, l, hl, h1, h2, rfl⟩

end Factors

end CFSG.SeitzReduction.TwistedE6Pilot
