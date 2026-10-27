module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotQ2PlusNbrPos
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMain
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotHR8Tori

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadPlus)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)

theorem sq_add_one_mul_add_one_ne_zero_of_card_two {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) (s : K) : s ^ 2 + 1 * s + 1 ≠ 0 := by
  have := Fintype.ofFinite K
  have h := FiniteField.pow_card s
  rw [Fintype.card_eq_nat_card, hK] at h
  rw [h, one_mul, CharTwo.add_self_eq_zero, zero_add]
  exact one_ne_zero

section HR8

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem neighbour_overgroup_plusAnisoTorus_two (hset : SeitzSetting G L) {m : ℕ}
    (hcat : OmegaCatalogueClausesAt (m + 1)) {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK2 : Nat.card K = 2) (hm : 4 ≤ m) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus (m + 2) K)) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {X : Subgroup G}
    (hX : X = ((plusAnisoTorus m hirr).map
      (e.trans (plusAnisoProjEquiv m hirr).symm).symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G}
    (hDe : D = ((plusAnisoPerp (K := K) m b c).map
      (e.trans (plusAnisoProjEquiv m hirr).symm).symm.toMonoidHom).map L.subtype)
    (hnn : ¬ ((D.subgroupOf (centralizer (X : Set G))).map
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))).Normal) :
    NeighbourOvergroupOmega (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
        ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) (m + 1) 1 := by
  set e' := e.trans (plusAnisoProjEquiv m hirr).symm with he'
  have hKc : Nat.card K = 2 ^ 1 := by rw [hK2, pow_one]
  have hKt := inf_centralizer_eq_zpowers_plus hset (by omega) hKc e htC ht
  obtain ⟨-, -, -, -, -, hDC, hDq, hZ⟩ := neighbour_data_plusAnisoTorus (by omega) hirr e' htC hX hDe
  obtain ⟨hLie, -⟩ := lieModel_map_plusAnisoPerp hKc (by omega) hirr e' hDe
  have hreg := regular_plusAnisoQuad (K := K) (b := b) (c := c)
    (coeff_ne_zero_of_irreducible' hirr) (by omega : 1 ≤ m)
  have hXne : X ≠ ⊥ := by
    rw [hX, Ne, map_eq_bot_iff_of_injective _ L.subtype_injective,
      map_eq_bot_iff_of_injective _ e'.symm.injective]
    exact (isAnisoCoord_plusAnisoQuad hirr).anisoTorusOf_ne_bot hreg.1 hreg.2
  obtain ⟨hcomp, hsyl, hstd⟩ := neighbour_standard_plusAnisoTorus hset.standardSetting.standard
    htC ht hKt (by omega) hirr e' hX htX hDe
  have hmf : (m + 1, 1) ≠ (4, 1) := by
    intro h
    have := congrArg Prod.fst h
    simp only at this
    omega
  exact (neighbour_overgroup_omega_of_seitzSetting hset hmf hcat hXne htX ht
    (hDC.trans inf_le_left) hDq hZ (Or.inr rfl) hLie hcomp hsyl hstd hnn).1

end HR8

section Reduction

theorem omegaPlusTwoPositionInput_holds :
    ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
      ∀ (m : ℕ), 3 ≤ m → ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (b c : K)
        (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0), Nat.card K = 2 →
        ∀ (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus (m + 2) K)) (t : G),
          t ∈ centralizer (L : Set G) → orderOf t = 2 →
          ¬ (((modelToG (e.trans (plusAnisoProjEquiv m hirr).symm)
              (plusAnisoPerp (K := K) m b c)).subgroupOf
              (centralizer (modelToG (e.trans (plusAnisoProjEquiv m hirr).symm)
                (plusAnisoTorus m hirr) : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer
              (modelToG (e.trans (plusAnisoProjEquiv m hirr).symm)
                (plusAnisoTorus m hirr) : Set G))))).Normal := by
  intro G _ _ L hset m hm K _ _ _ b c hirr hK2 e t htC ht
  exact not_normal_neighbour_plusAnisoTorus_two hset hK2 hm hirr e htC ht rfl rfl

@[expose] def OmegaPlusTwoTenInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (b c : K)
      (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0), Nat.card K = 2 →
      ∀ (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus (3 + 2) K)) (t : G),
        orderOf t = 2 → centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
        ¬ (((modelToG (e.trans (plusAnisoProjEquiv 3 hirr).symm)
            (plusAnisoPerp (K := K) 3 b c)).subgroupOf
            (centralizer (modelToG (e.trans (plusAnisoProjEquiv 3 hirr).symm)
              (plusAnisoTorus 3 hirr) : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer
            (modelToG (e.trans (plusAnisoProjEquiv 3 hirr).symm)
              (plusAnisoTorus 3 hirr) : Set G))))).Normal → False

@[expose] def OmegaPlusTwoRowInput (r : OmegaRow) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (m : ℕ), 4 ≤ m → ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (b c : K)
      (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0), Nat.card K = 2 →
      ∀ (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus (m + 2) K)) (t : G),
        orderOf t = 2 → centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
        ¬ (((modelToG (e.trans (plusAnisoProjEquiv m hirr).symm)
            (plusAnisoPerp (K := K) m b c)).subgroupOf
            (centralizer (modelToG (e.trans (plusAnisoProjEquiv m hirr).symm)
              (plusAnisoTorus m hirr) : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer
            (modelToG (e.trans (plusAnisoProjEquiv m hirr).symm)
              (plusAnisoTorus m hirr) : Set G))))).Normal →
        (∀ htX : t ∈ centralizer (modelToG (e.trans (plusAnisoProjEquiv m hirr).symm)
            (plusAnisoTorus m hirr) : Set G),
          NeighbourOvergroupOmega (QuotientGroup.mk' (oddCore (centralizer
              (modelToG (e.trans (plusAnisoProjEquiv m hirr).symm)
                (plusAnisoTorus m hirr) : Set G))) ⟨t, htX⟩)
            (((modelToG (e.trans (plusAnisoProjEquiv m hirr).symm)
                (plusAnisoPerp (K := K) m b c)).subgroupOf
                (centralizer (modelToG (e.trans (plusAnisoProjEquiv m hirr).symm)
                  (plusAnisoTorus m hirr) : Set G))).map
              (QuotientGroup.mk' (oddCore (centralizer
                (modelToG (e.trans (plusAnisoProjEquiv m hirr).symm)
                  (plusAnisoTorus m hirr) : Set G))))) (m + 1) 1) →
        OmegaRowAt t (modelToG (e.trans (plusAnisoProjEquiv m hirr).symm) (plusAnisoTorus m hirr))
          (modelToG (e.trans (plusAnisoProjEquiv m hirr).symm) (plusAnisoPerp (K := K) m b c)) r →
          False

theorem omegaPlusTwoInput_of_inputs (h10 : OmegaPlusTwoTenInput)
    (hcat : ∀ m : ℕ, 5 ≤ m → OmegaCatalogueClausesAt m)
    (hfield : OmegaPlusTwoRowInput .field) (hswap : OmegaPlusTwoRowInput .swap) :
    OmegaPlusTwoInput := by
  intro G _ _ L hset n K _ _ _ hK2 hn e t ht hKt
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hirr := sq_add_one_mul_add_one_ne_zero_of_card_two (K := K) hK2
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have hnn := omegaPlusTwoPositionInput_holds G L hset m (by omega) K 1 1 hirr hK2 e t htC ht
  rcases (show m = 3 ∨ 4 ≤ m by omega) with rfl | h4
  · exact h10 G L hset K 1 1 hirr hK2 e t ht hKt hnn
  · have hN : ∀ htX : t ∈ centralizer (modelToG (e.trans (plusAnisoProjEquiv m hirr).symm)
          (plusAnisoTorus m hirr) : Set G),
        NeighbourOvergroupOmega (QuotientGroup.mk' (oddCore (centralizer
            (modelToG (e.trans (plusAnisoProjEquiv m hirr).symm)
              (plusAnisoTorus m hirr) : Set G))) ⟨t, htX⟩)
          (((modelToG (e.trans (plusAnisoProjEquiv m hirr).symm)
              (plusAnisoPerp (K := K) m 1 1)).subgroupOf
              (centralizer (modelToG (e.trans (plusAnisoProjEquiv m hirr).symm)
                (plusAnisoTorus m hirr) : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer
              (modelToG (e.trans (plusAnisoProjEquiv m hirr).symm)
                (plusAnisoTorus m hirr) : Set G))))) (m + 1) 1 :=
      fun htX => neighbour_overgroup_plusAnisoTorus_two hset (hcat (m + 1) (by omega)) hK2 h4 hirr
        e htC ht rfl htX rfl hnn
    obtain ⟨-, htX, -⟩ := neighbour_data_plusAnisoTorus (by omega) hirr
      (e.trans (plusAnisoProjEquiv m hirr).symm) htC rfl rfl
    obtain ⟨r, hr⟩ := exists_omegaRowAt_of_neighbourOvergroupOmega htX (hN htX)
    cases r with
    | field => exact hfield G L hset m h4 K 1 1 hirr hK2 e t ht hKt hnn hN hr
    | swap => exact hswap G L hset m h4 K 1 1 hirr hK2 e t ht hKt hnn hN hr

end Reduction

end CFSG.SeitzReduction.OmegaPilot
