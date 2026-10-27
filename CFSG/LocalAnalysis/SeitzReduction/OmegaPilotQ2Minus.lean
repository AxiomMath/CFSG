module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusCoverHR8Main
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotHR8Tori
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotNeighbourStandardAniso

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (coordinateQuadPlus coordinateQuadMinus regular_coordinateQuadMinus)

section HR8

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem neighbour_overgroup_anisoTorus_of_ne (hset : SeitzSetting G L) {n f : ℕ}
    (hcat : OmegaCatalogueClausesAt (n - 1)) {K : Type} [Field K] [Finite K] [CharP K 2]
    (hKc : Nat.card K = 2 ^ f) (hmf : (n - 1, f) ≠ (4, 1)) (hn : 5 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c))
    {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {X : Subgroup G}
    (hX : X = ((anisoTorus (K := K) (by omega) b c).map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G}
    (hDe : D = ((anisoPerp (K := K) (by omega) b c).map e.symm.toMonoidHom).map L.subtype)
    (hnn : ¬ ((D.subgroupOf (centralizer (X : Set G))).map
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))).Normal) :
    NeighbourOvergroupOmega (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
        ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) (n - 1) f ∧
      ∀ Lc : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
        IsComponent Lc →
        ⁅(D.subgroupOf (centralizer (X : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))), Lc⁆ ≠ ⊥ →
        OmegaNeighbourAlternative
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
          ((D.subgroupOf (centralizer (X : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) Lc (n - 1) f := by
  obtain ⟨-, -, -, -, -, hDC, hDq, hZ⟩ := neighbour_data_anisoTorus (by omega) hirr e htC hX hDe
  obtain ⟨hLie, -⟩ := lieModel_map_anisoPerp hKc hn hirr e hDe
  have hreg := regular_coordinateQuadMinus n K b c (by omega) hirr
  have hXne : X ≠ ⊥ := by
    rw [hX, Ne, map_eq_bot_iff_of_injective _ L.subtype_injective,
      map_eq_bot_iff_of_injective _ e.symm.injective]
    exact (isAnisoCoord_coordinateQuadMinus (by omega) hirr).anisoTorusOf_ne_bot hreg.1 hreg.2
  obtain ⟨hcomp, hsyl, hstd⟩ :=
    neighbour_standard_anisoTorus_of_seitzSetting hset hKc (by omega) hirr e htC ht hX htX hDe
  exact neighbour_overgroup_omega_of_seitzSetting hset hmf hcat hXne htX ht
    (hDC.trans inf_le_left) hDq hZ (Or.inl rfl) hLie hcomp hsyl hstd hnn

theorem ne_four_one_of_six_le {n : ℕ} (hn : 6 ≤ n) : (n - 1, 1) ≠ (4, 1) := by
  intro h
  have := congrArg Prod.fst h
  simp only at this
  omega

theorem neighbour_overgroup_anisoTorus_two (hset : SeitzSetting G L) {n : ℕ}
    (hcat : OmegaCatalogueClausesAt (n - 1)) {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK2 : Nat.card K = 2) (hn : 6 ≤ n) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c))
    {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {X : Subgroup G}
    (hX : X = ((anisoTorus (K := K) (by omega) b c).map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G}
    (hDe : D = ((anisoPerp (K := K) (by omega) b c).map e.symm.toMonoidHom).map L.subtype)
    (hnn : ¬ ((D.subgroupOf (centralizer (X : Set G))).map
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))).Normal) :
    NeighbourOvergroupOmega (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
        ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) (n - 1) 1 :=
  (neighbour_overgroup_anisoTorus_of_ne hset hcat (f := 1) (by rw [hK2, pow_one])
    (ne_four_one_of_six_le hn) (by omega) hirr e htC ht hX htX hDe hnn).1

theorem exists_omegaRowAt_anisoTorus_two (hset : SeitzSetting G L) {n : ℕ}
    (hcat : OmegaCatalogueClausesAt (n - 1)) {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK2 : Nat.card K = 2) (hn : 6 ≤ n) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c))
    {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {X : Subgroup G}
    (hX : X = ((anisoTorus (K := K) (by omega) b c).map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G}
    (hDe : D = ((anisoPerp (K := K) (by omega) b c).map e.symm.toMonoidHom).map L.subtype)
    (hnn : ¬ ((D.subgroupOf (centralizer (X : Set G))).map
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))).Normal) :
    ∃ r : OmegaRow, OmegaRowAt t X D r :=
  exists_omegaRowAt_of_neighbourOvergroupOmega htX
    (neighbour_overgroup_anisoTorus_two hset hcat hK2 hn hirr e htC ht hX htX hDe hnn)

end HR8

section Reduction

open CFSG.SeitzReduction.UnitaryPilot (modelToG)

@[expose] def OmegaMinusTwoPositionInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (n : ℕ) (hn : 5 ≤ n) (K : Type) [Field K] [Finite K] [CharP K 2] (b c : K),
      (∀ s : K, s ^ 2 + b * s + c ≠ 0) → Nat.card K = 2 →
      ∀ (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c)) (t : G),
        t ∈ centralizer (L : Set G) → orderOf t = 2 →
        ¬ (((modelToG e (anisoPerp (K := K) (by omega) b c)).subgroupOf
            (centralizer (modelToG e (anisoTorus (K := K) (by omega) b c) : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer
            (modelToG e (anisoTorus (K := K) (by omega) b c) : Set G))))).Normal

@[expose] def OmegaMinusTwoTenInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (b c : K),
      (∀ s : K, s ^ 2 + b * s + c ≠ 0) → Nat.card K = 2 →
      ∀ (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus 5 K (by norm_num) b c)) (t : G),
        orderOf t = 2 → centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
        ¬ (((modelToG e (anisoPerp (K := K) (by norm_num) b c)).subgroupOf
            (centralizer (modelToG e (anisoTorus (K := K) (by norm_num) b c) : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer
            (modelToG e (anisoTorus (K := K) (by norm_num) b c) : Set G))))).Normal → False

@[expose] def OmegaMinusTwoRowInput (r : OmegaRow) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (n : ℕ) (hn : 6 ≤ n) (K : Type) [Field K] [Finite K] [CharP K 2] (b c : K),
      (∀ s : K, s ^ 2 + b * s + c ≠ 0) → Nat.card K = 2 →
      ∀ (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c)) (t : G),
        orderOf t = 2 → centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
        ¬ (((modelToG e (anisoPerp (K := K) (by omega) b c)).subgroupOf
            (centralizer (modelToG e (anisoTorus (K := K) (by omega) b c) : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer
            (modelToG e (anisoTorus (K := K) (by omega) b c) : Set G))))).Normal →
        (∀ htX : t ∈ centralizer (modelToG e (anisoTorus (K := K) (by omega) b c) : Set G),
          NeighbourOvergroupOmega (QuotientGroup.mk' (oddCore (centralizer
              (modelToG e (anisoTorus (K := K) (by omega) b c) : Set G))) ⟨t, htX⟩)
            (((modelToG e (anisoPerp (K := K) (by omega) b c)).subgroupOf
                (centralizer (modelToG e (anisoTorus (K := K) (by omega) b c) : Set G))).map
              (QuotientGroup.mk' (oddCore (centralizer
                (modelToG e (anisoTorus (K := K) (by omega) b c) : Set G))))) (n - 1) 1) →
        OmegaRowAt t (modelToG e (anisoTorus (K := K) (by omega) b c))
          (modelToG e (anisoPerp (K := K) (by omega) b c)) r → False

theorem omegaMinusTwoInput_of_inputs (hpos : OmegaMinusTwoPositionInput)
    (h10 : OmegaMinusTwoTenInput) (hcat : ∀ m : ℕ, 5 ≤ m → OmegaCatalogueClausesAt m)
    (hfield : OmegaMinusTwoRowInput .field) (hswap : OmegaMinusTwoRowInput .swap) :
    OmegaMinusTwoInput := by
  intro G _ _ L hset n hn K _ _ _ b c hirr hK2 e t ht hKt
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have hnn := hpos G L hset n hn K b c hirr hK2 e t htC ht
  rcases (show n = 5 ∨ 6 ≤ n by omega) with rfl | h6
  · exact h10 G L hset K b c hirr hK2 e t ht hKt hnn
  · have hN : ∀ htX : t ∈ centralizer (modelToG e (anisoTorus (K := K) (by omega) b c) : Set G),
        NeighbourOvergroupOmega (QuotientGroup.mk' (oddCore (centralizer
            (modelToG e (anisoTorus (K := K) (by omega) b c) : Set G))) ⟨t, htX⟩)
          (((modelToG e (anisoPerp (K := K) (by omega) b c)).subgroupOf
              (centralizer (modelToG e (anisoTorus (K := K) (by omega) b c) : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer
              (modelToG e (anisoTorus (K := K) (by omega) b c) : Set G))))) (n - 1) 1 :=
      fun htX => neighbour_overgroup_anisoTorus_two hset (hcat (n - 1) (by omega)) hK2 h6 hirr e
        htC ht rfl htX rfl hnn
    obtain ⟨-, htX, -⟩ := neighbour_data_anisoTorus (by omega) hirr e htC rfl rfl
    obtain ⟨r, hr⟩ := exists_omegaRowAt_anisoTorus_two hset (hcat (n - 1) (by omega)) hK2 h6
      hirr e htC ht rfl htX rfl hnn
    cases r with
    | field => exact hfield G L hset n h6 K b c hirr hK2 e t ht hKt hnn hN hr
    | swap => exact hswap G L hset n h6 K b c hirr hK2 e t ht hKt hnn hN hr

end Reduction

end CFSG.SeitzReduction.OmegaPilot
