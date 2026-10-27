module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotKleinThreeMinus

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived
  coordinateFieldMap)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadMinus
  minusIndexEquiv)
open CFSG.SeitzReduction.UnitaryPilot (modelToG modelToGEquiv symm_mem_modelToG
  SUmCatalogueClausesAt)
open CFSG.RankThree.PartOne.KCOrthogonalSubfield (incl fieldAutT)
open CFSG.SeitzReduction.TwistedE6Pilot (isExtension_coordinateQuadMinus)

section Cover


variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem exists_normalizedCover_minus_four (hset : SeitzSetting G L)
    (hcat : SUmCatalogueClausesAt 4) {f : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hKc : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus (2 + 2) K (by omega) b c)) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) (k : Fin (2 + 1))
    (hrow : OmegaRowAt t (modelToG e (minusPairTorus (K := K) (n := 2 + 2) (by omega) b c k))
      (modelToG e (minusPairPerp (K := K) (n := 2 + 2) (by omega) b c k)) .field)
    {F : Type} [Field F] [Finite F] [CharP F 2] (ι : K →+* F) {σ : F ≃+* F}
    (hσ : orderOf σ = 2) (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι) :
    ∃ π : minusNeighbourCore e k →* matrixProjectiveDerived (coordinateQuadMinus (2 + 1) F
        (by omega) ((ι.rangeRestrictFieldEquiv b : ι.fieldRange) : F)
        ((ι.rangeRestrictFieldEquiv c : ι.fieldRange) : F)),
      Function.Surjective π ∧ π.ker ≤ center (minusNeighbourCore e k) ∧
      (∀ (hQσ : ∀ v, coordinateQuadMinus (2 + 1) F (by omega)
          ((ι.rangeRestrictFieldEquiv b : ι.fieldRange) : F)
          ((ι.rangeRestrictFieldEquiv c : ι.fieldRange) : F) (coordinateFieldMap _ σ v) =
        σ (coordinateQuadMinus (2 + 1) F (by omega)
          ((ι.rangeRestrictFieldEquiv b : ι.fieldRange) : F)
          ((ι.rangeRestrictFieldEquiv c : ι.fieldRange) : F) v))
        (x : minusNeighbourCore e k),
        π ((minusNeighbourCore e k).normalizerMonoidHom
            ⟨t, mem_normalizer_minusNeighbourCore e htC k⟩ x) =
          fieldAutT _ σ hQσ (π x)) ∧
      ∃ hDE : modelToG e (minusPairPerp (K := K) (n := 2 + 2) (by omega) b c k) ≤
          minusNeighbourCore e k,
        ∀ d : modelToG e (minusPairPerp (K := K) (n := 2 + 2) (by omega) b c k),
          π (Subgroup.inclusion hDE d) =
            incl ι.fieldRange (isExtension_coordinateQuadMinus ι.fieldRange (by omega)
              (ι.rangeRestrictFieldEquiv b) (ι.rangeRestrictFieldEquiv c))
              (minusPairPerpFieldEquivOfLe (r := 2) le_rfl hirr e k ι.rangeRestrictFieldEquiv
                d) := by
  have hF : Nat.card F = 2 ^ (2 * f) :=
    SymplecticPilot.natCard_eq_two_pow_two_mul_of_fix ι hKc hσ hfix
  set X := modelToG e (minusPairTorus (K := K) (n := 2 + 2) (by omega) b c k) with hXdef
  set D := modelToG e (minusPairPerp (K := K) (n := 2 + 2) (by omega) b c k) with hDdef
  obtain ⟨htX, Kc, hKcomp, hDKK, hiff⟩ := hrow
  have hKt := hiff.1 rfl
  obtain ⟨hcomp, -, -⟩ := neighbour_standard_minusPairTorus_of_seitzSetting_of_four_le (X := X)
    (D := D) hset hKc hq le_rfl hirr k e htC ht rfl htX rfl
  obtain ⟨-, -, -, -, -, -, hDC, -, -, -⟩ :=
    neighbour_data_minusPairTorus_of_four_le (X := X) (D := D) hKc hq le_rfl hirr k e htC rfl rfl
  have hDK : ⁅(D.subgroupOf (centralizer (X : Set G))).map
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))), Kc⁆ ≠ ⊥ := by
    rw [hKt, sup_idem] at hDKK
    intro hbot
    apply ne_bot_of_isQuasisimple hcomp.2.2
    rw [eq_bot_iff, ← SymplecticPilot.commutator_eq_self_of_isQuasisimple hcomp.2.2, ← hbot]
    exact Subgroup.commutator_mono le_rfl hDKK
  obtain ⟨hsN, -, -, ⟨K', _, _, hK', eK, φ, hφ, hτ⟩, q, hqs, hqker, -, -, ⟨htE, hqt⟩, hDE, hqinj,
    -⟩ := neighbourCore_minusPairTorus_four (X := X) (D := D) hset hcat hKc hq hirr k e htC ht rfl
      htX rfl Kc hKcomp hDK hKt
  have hσk : ∀ x, x ∈ ι.fieldRange ↔ σ x = x := fun x => by
    rw [hfix, RingHom.mem_fieldRange, Set.mem_range]
  have : CharP ι.fieldRange 2 := RingHom.charP ι.fieldRange.subtype Subtype.val_injective 2
  have hirr₀ : ∀ s : ι.fieldRange, s ^ 2 + ι.rangeRestrictFieldEquiv b * s +
      ι.rangeRestrictFieldEquiv c ≠ 0 := by
    intro s hs
    apply hirr (ι.rangeRestrictFieldEquiv.symm s)
    apply ι.rangeRestrictFieldEquiv.injective
    rw [map_add, map_add, map_mul, map_pow, RingEquiv.apply_symm_apply, map_zero]
    exact hs
  have hk₀ : Nat.card ι.fieldRange = 2 ^ f :=
    (Nat.card_congr ι.rangeRestrictFieldEquiv.toEquiv).symm.trans hKc
  have hφk : ∀ x, φ x = x ^ Nat.card ι.fieldRange := fun x => by rw [hk₀]; exact hφ x
  have hεfix : (q.comp (Subgroup.inclusion hDE)).range ≤
      fixedSubgroup (Kc.normalizerMonoidHom ⟨_, hsN⟩) := by
    rintro _ ⟨d, rfl⟩
    change Kc.normalizerMonoidHom ⟨_, hsN⟩ (q (Subgroup.inclusion hDE d)) =
      q (Subgroup.inclusion hDE d)
    rw [← hqt]
    congr 1
    apply Subtype.ext
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    change t * (d : G) * t⁻¹ = d
    rw [mem_centralizer_iff.1 (hDC d.2).2 t (Set.mem_singleton t), mul_inv_cancel_right]
  obtain ⟨ψ, hψ, hψτ⟩ := minusNormalizationThreeInput_holds F σ hσ ι.fieldRange hσk
    (ι.rangeRestrictFieldEquiv b) (ι.rangeRestrictFieldEquiv c) hirr₀ Kc
    (Kc.normalizerMonoidHom ⟨_, hsN⟩) K' (hK'.trans hF.symm) eK φ hφk hτ _
    (q.comp (Subgroup.inclusion hDE)) hqinj hεfix
    (minusPairPerpFieldEquivOfLe (r := 2) le_rfl hirr e k ι.rangeRestrictFieldEquiv)
  refine ⟨ψ.toMonoidHom.comp q, ψ.surjective.comp hqs, ?_, ?_, hDE, fun d => hψ d⟩
  · intro x hx
    have h1 : ψ (q x) = 1 := hx
    have h2 : x ∈ q.ker := MonoidHom.mem_ker.2 ((MulEquiv.map_eq_one_iff ψ).1 h1)
    rw [hqker] at h2
    exact h2
  · intro hQσ x
    change ψ (q ((F4Pilot.centralizerPerfectCore X).normalizerMonoidHom ⟨t, htE⟩ x)) = _
    rw [hqt x]
    have h2 := congrArg (fun α : MulAut _ => α (ψ (q x))) hψτ
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at h2
    exact h2

end Cover

end CFSG.SeitzReduction.OmegaPilot
