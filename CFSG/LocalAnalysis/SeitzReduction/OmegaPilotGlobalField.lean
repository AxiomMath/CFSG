module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCoverExists
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotGlobal
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotHR8Kind

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.LieType CFSG.LieType.Universal
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadPlus)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

omit [Finite G] in
theorem exists_fieldAlt_of_rowAt {t : G} {m f : ℕ} {X D : Subgroup G}
    (h8 : OmegaHR8FieldAt t m f .POmegaPlus X D) (hrow : OmegaRowAt t X D .field)
    (hDq : CFSG.Open.IsQuasisimple ((D.subgroupOf (centralizer (X : Set G))).map
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))))) :
    ∃ htX : t ∈ centralizer (X : Set G),
      ∃ Kc : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
        IsComponent Kc ∧
        OmegaNeighbourAlternativeField
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
          ((D.subgroupOf (centralizer (X : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) Kc m f .POmegaPlus ∧
        Kc.map (MulAut.conj
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)).toMonoidHom = Kc := by
  obtain ⟨htX, -, hall, -⟩ := h8
  obtain ⟨htX', Kc, hKc, hDK, hr⟩ := hrow
  have hKt := hr.1 rfl
  refine ⟨htX, Kc, hKc, hall Kc hKc ?_, hKt⟩
  have hDle : (D.subgroupOf (centralizer (X : Set G))).map
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) ≤ Kc := by
    have h1 := hDK
    rw [hKt, sup_idem] at h1
    exact h1
  have hperf : ⁅(D.subgroupOf (centralizer (X : Set G))).map
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))),
      (D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))⁆ =
      (D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) :=
    SymplecticPilot.commutator_eq_self_of_isQuasisimple hDq
  intro hbot
  apply ne_bot_of_isQuasisimple hDq
  rw [← hperf, eq_bot_iff, ← hbot]
  exact Subgroup.commutator_mono le_rfl hDle


theorem exists_weakCT_plus_of_fieldRow (hset : SeitzSetting G L) {m f : ℕ} {K : Type} [Field K]
    [Finite K] [CharP K 2] (hKc : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K) (hm : 5 ≤ m)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus (m + 1) K)) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (h8 : ∀ k : Fin (m + 1), OmegaHR8FieldAt t m f .POmegaPlus (modelToG e (pairTorus (K := K) k))
      (modelToG e (pairPerp (K := K) k)))
    (hrow : ∀ k : Fin (m + 1), OmegaRowAt t (modelToG e (pairTorus (K := K) k))
      (modelToG e (pairPerp (K := K) k)) .field)
    {F : Type} [Field F] [Finite F] [CharP F 2] (ι : K →+* F) {σ : F ≃+* F}
    (hσ : orderOf σ = 2) (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι)
    {G₀ : Subgroup G} (hG₀ : G₀ = ⨆ j, plusNode e j) :
    (∀ k, Nonempty (PlusFieldCover e ι k)) ∧
      ∃ Ψ : spinGroup (Spin.quadPlus (m + 1) F) →* G₀, Function.Surjective Ψ ∧
        Ψ.ker ≤ Subgroup.center _ ∧ CFSG.IsQuasisimple G₀ ∧
        CFSG.Blueprint.LieModel (G₀ ⧸ center G₀) .POmegaPlus (m + 1) 2 (2 * f) ∧
        (∀ j, (CurtisTits.rankOne (Spin.plusDatum (m + 1) F (by omega)).rootGroup j).map Ψ =
          (plusNode e j).subgroupOf G₀) ∧
        t ∈ normalizer (G₀ : Set G) := by
  have hC : ∀ k, Nonempty (PlusFieldCover e ι k) := by
    intro k
    obtain ⟨-, htX, -⟩ := neighbour_data_pairTorus hKc hq (by omega : 5 ≤ m + 1) k e htC rfl rfl
    obtain ⟨hcomp, -, -⟩ := neighbour_standard_pairTorus_of_seitzSetting hset hKc hq
      (by omega : 5 ≤ m + 1) k e htC ht rfl htX rfl
    obtain ⟨htX', Kc, hKcomp, hfield, hKt⟩ := exists_fieldAlt_of_rowAt (h8 k) (hrow k) hcomp.2.2
    exact nonempty_plusFieldCover_of_field hset hKc hq hm k e htC ht rfl htX' rfl hKcomp hfield
      hKt ι hσ hfix
  have hF : Nat.card F = 2 ^ (2 * f) :=
    SymplecticPilot.natCard_eq_two_pow_two_mul_of_fix ι hKc hσ hfix
  exact ⟨hC, exists_weakCT_plus_of_forall_cover (by omega) hKc hq hF (fun k => (hC k).some) hG₀
    htC⟩

end CFSG.SeitzReduction.OmegaPilot
