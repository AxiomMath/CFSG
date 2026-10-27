module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T123CParityCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionTransport
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBStabilizerFamilyBasic
import CFSG.LocalAnalysis.GLTheoremA.CatA.T123CParityFamily
import CFSG.ClassicalGroups.Orthogonal.RootGroupFixedInf
import CFSG.ClassicalGroups.Orthogonal.RootGroupStabilizer

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T123C

open CFSG.Open CFSG.ClassicalGroups.Orthogonal
open CFSG.ComponentClassification.CatalogueBOrthogonalPointAction
open CFSG.ComponentClassification.CatalogueBStabilizerFamily (family familyAut exists_image_point)

section Projective

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem pCoreOf_projective_stabilizer_ne_bot [CharP K 2] [FiniteDimensional K V]
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (h3 : 2 < Module.finrank K V)
    (L : Points Q) : pCoreOf 2 (actionStabilizer Q (projectivePointAction Q) L) ≠ ⊥ := by
  obtain ⟨u, hu0, hu, rfl⟩ := exists_eq_pointMk L
  set π := QuotientGroup.mk' (scalarKernel Q) with hπ
  have hstab : ∀ g : Gom Q,
      π g ∈ actionStabilizer Q (projectivePointAction Q) (pointMk u hu0 hu) ↔
        g ∈ CFSG.ClassicalGroups.Orthogonal.pointStabilizer Q u := fun g => by
    change g • pointMk u hu0 hu = pointMk u hu0 hu ↔ _
    rw [smul_pointMk, pointMk_eq_iff, CFSG.ClassicalGroups.Orthogonal.mem_pointStabilizer]
    exact ⟨fun ⟨a, ha⟩ => ⟨a, ha.symm⟩, fun ⟨a, ha⟩ => ⟨a, ha.symm⟩⟩
  set N : Subgroup (ProjectiveGroup Q) := (Lom Q u).map π with hN
  have hNS : N ≤ actionStabilizer Q (projectivePointAction Q) (pointMk u hu0 hu) := by
    rintro _ ⟨g, hg, rfl⟩
    exact (hstab g).2 (Lom_le_pointStabilizer u hg)
  have hSN : actionStabilizer Q (projectivePointAction Q) (pointMk u hu0 hu) ≤
      Subgroup.normalizer (N : Set (ProjectiveGroup Q)) := by
    intro x hx
    obtain ⟨g, rfl⟩ : ∃ g, π g = x := QuotientGroup.mk'_surjective (scalarKernel Q) x
    have hg := (hstab g).1 hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨l, hl, rfl⟩
      exact ⟨g * l * g⁻¹, conj_mem_Lom_of_mem_pointStabilizer hg hl, by
        simp only [map_mul, map_inv]⟩
    · rintro ⟨l, hl, hly⟩
      refine ⟨g⁻¹ * l * g⁻¹⁻¹, conj_mem_Lom_of_mem_pointStabilizer (inv_mem hg) hl, ?_⟩
      simp only [map_mul, map_inv, inv_inv, hly]
      group
  have hNne : N ≠ ⊥ := by
    intro hbot
    apply Lom_ne_bot hQ h3 hu hu0
    rw [eq_bot_iff]
    intro l hl
    have h1 : π l ∈ N := ⟨l, hl, rfl⟩
    rw [hbot, Subgroup.mem_bot, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have h1' : (l : V ≃ₗ[K] V) ∈ scalars K V := h1
    obtain ⟨c, hc⟩ := mem_scalars.1 h1'
    have hlu : l.app u = u := app_eq_self_of_mem_Lom hl
    have hc1 : c = 1 := by
      have h2 : c • u = (1 : K) • u := by
        rw [one_smul, ← hc u]
        exact hlu
      exact smul_left_injective K hu0 h2
    rw [Subgroup.mem_bot]
    exact Gom.ext' fun x => by
      rw [Gom.app_one]
      exact (hc x).trans (by rw [hc1, one_smul])
  have hle := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hNS hSN
    ((isPGroup_Lom u).map π)
  intro hbot
  rw [hbot, le_bot_iff] at hle
  exact hNne hle

end Projective

section Stated

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
variable {Q : QuadraticForm K (ι → K)} {Q₀ : (ι → K) → K}

theorem pCoreOf_statedPointStabilizer_ne_bot [CharP K 2] (hQ : ⇑Q = Q₀)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q)
    (hnd : (QuadraticMap.polarBilin Q).Nondegenerate) (h3 : 2 < Module.finrank K (ι → K))
    (L : Points Q) :
    pCoreOf 2 (CFSG.ComponentClassification.CatalogueBStabilizerFamily.pointStabilizer
      (statedPointAction hQ) L) ≠ ⊥ := by
  set e := statedActionEquiv hQ hE
  have hcomap := actionStabilizer_comap Q (statedPointAction hQ) (projectivePointAction Q) e
    (statedPointAction_equiv hQ hE) L
  have hmap : (actionStabilizer Q (statedPointAction hQ) L).map e.toMonoidHom =
      actionStabilizer Q (projectivePointAction Q) L := by
    rw [← hcomap, Subgroup.map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective]
  intro hbot
  apply pCoreOf_projective_stabilizer_ne_bot hnd h3 L
  rw [← hmap, CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2 e]
  change (pCoreOf 2 (CFSG.ComponentClassification.CatalogueBStabilizerFamily.pointStabilizer
    (statedPointAction hQ) L)).map e.toMonoidHom = ⊥
  rw [hbot, Subgroup.map_bot]

theorem parityCoreAt_of_statedPointAction [Finite K] [CharP K 2] (hQ : ⇑Q = Q₀)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q)
    (hnd : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K (ι → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hAut : familyAut (statedPointAction hQ) = ⊤) {p : ℕ} (hp : p.Prime)
    (hcard : ¬ p ∣ Nat.card (Points Q)) : ParityCoreAt p (StatedProj (StatedOmega Q₀)) := by
  have hinj := (stated_action_properties hQ hE hnd hT).2.2.2.2.2.1
  have h3 : 2 < Module.finrank K (ι → K) := by
    obtain ⟨T, hT3, -⟩ := hT
    have := Submodule.finrank_le T
    omega
  have : Finite (StatedProj (StatedOmega Q₀)) := inferInstance
  have hfam : Nat.card (family (statedPointAction hQ)) = Nat.card (Points Q) :=
    (Nat.card_congr (Equiv.ofInjective _ hinj)).symm
  refine parityCoreAt_of_pCoreOf_family hp (family (statedPointAction hQ)) (hfam ▸ hcard)
    (fun α M hM => ?_) ?_
  · obtain ⟨L, rfl⟩ := hM
    obtain ⟨L', hL'⟩ := exists_image_point (statedPointAction hQ)
      ⟨α, hAut ▸ Subgroup.mem_top α⟩ L
    exact ⟨L', hL'.symm⟩
  · rintro M ⟨L, rfl⟩
    exact pCoreOf_statedPointStabilizer_ne_bot hQ hE hnd h3 L

end Stated

end CFSG.LocalAnalysis.GLTheoremA.T123C

end
