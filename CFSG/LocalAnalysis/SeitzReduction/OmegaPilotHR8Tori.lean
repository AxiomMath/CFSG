module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotHR8
import CFSG.LocalAnalysis.SeitzReduction.F4PilotHR8Instances
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotNeighbourStandard
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotNeighbourStandardAnisoTorus

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (coordinateQuadPlus coordinateQuadMinus regular_coordinateQuadMinus)

section Facts

theorem odd_card_center_of_center_eq_bot {D : Type*} [Group D] (hZ : center D = ⊥) :
    Odd (Nat.card (center D)) := by
  rw [hZ, Subgroup.card_bot]
  exact odd_one

theorem ne_four_one_of_four_le_card {K : Type*} {f : ℕ} (hKc : Nat.card K = 2 ^ f)
    (hq : 4 ≤ Nat.card K) (m : ℕ) : (m, f) ≠ (4, 1) := by
  intro h
  have hf : f = 1 := congrArg Prod.snd h
  rw [hKc, hf] at hq
  norm_num at hq

theorem ne_bot_of_one_lt_card {G : Type*} [Group G] {X : Subgroup G} (h : 1 < Nat.card X) :
    X ≠ ⊥ := by
  rintro rfl
  rw [Subgroup.card_bot] at h
  exact lt_irrefl 1 h

variable {K : Type*} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)} {a a' : Fin d} {b c : K}

theorem IsAnisoCoord.anisoTorusOf_ne_bot [Finite K] [CharP K 2] (h : IsAnisoCoord Q a a' b c)
    (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) :
    anisoTorusOf Q h.ne b c ≠ ⊥ := by
  intro hbot
  have hN₀ := h.norm_rot_one
  set x₀ : orthDerived Q := ⟨anisoRotEquiv h.ne b c hN₀,
    h.anisoRotSub_le_orthDerived hQ hT (anisoRotEquiv_mem_anisoRotSub h.ne hN₀)⟩ with hx₀def
  have hx₀ : projHom Q x₀ ∈ anisoTorusOf Q h.ne b c :=
    ⟨x₀, anisoRotEquiv_mem_anisoRotSub h.ne hN₀, rfl⟩
  rw [hbot, mem_bot] at hx₀
  have h1 : x₀ = 1 := projHom_injective h.exists_ne_zero (by rw [hx₀, map_one])
  have h2 := congrArg (fun g : orthDerived Q =>
    (g : (Fin d → K) ≃ₗ[K] (Fin d → K)) (Pi.single a 1) a') h1
  simp only [hx₀def, anisoRotEquiv_apply, anisoRotLin_single_left h.ne] at h2
  change (1 : K) • (Pi.single a (1 : K) : Fin d → K) a' + (b / c) • (Pi.single a' 1 : Fin d → K) a'
    = (Pi.single a (1 : K) : Fin d → K) a' at h2
  rw [Pi.single_eq_of_ne h.ne.symm, Pi.single_eq_same, smul_zero, zero_add, smul_eq_mul,
    mul_one] at h2
  exact div_ne_zero h.b_ne_zero h.c_ne_zero h2

end Facts

section Generic

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem neighbour_overgroup_omega_of_seitzSetting (hset : SeitzSetting G L) {m f : ℕ}
    (hmf : (m, f) ≠ (4, 1)) (hcat : OmegaCatalogueClausesAt m) {X : Subgroup G} (hX : X ≠ ⊥)
    {t : G} (htX : t ∈ centralizer (X : Set G)) (ht : orderOf t = 2) {D : Subgroup G}
    (hDX : D ≤ centralizer (X : Set G)) (hDq : CFSG.IsQuasisimple D) (hZD : center D = ⊥)
    {tag : StatedLieTag} (htag : tag = .POmegaPlus ∨ tag = .POmegaMinus)
    (hDm : LieModel D tag m 2 f)
    (hcomp : CFSG.Open.IsComponentOf
        ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))))
        (centralizer ({QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩} :
          Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))))))
    (hsyl : ∀ U : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
      IsPGroup 2 U →
      U ≤ centralizer ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) :
        Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) →
      Nat.card U ≤ 2)
    (hstd : CFSG.Open.standardComponentIsStandard ((D.subgroupOf (centralizer (X : Set G))).map
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))))
    (hnn : ¬ ((D.subgroupOf (centralizer (X : Set G))).map
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))).Normal) :
    NeighbourOvergroupOmega (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
        ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) m f ∧
      ∀ Lc : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
        IsComponent Lc →
        ⁅(D.subgroupOf (centralizer (X : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))), Lc⁆ ≠ ⊥ →
        OmegaNeighbourAlternative
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
          ((D.subgroupOf (centralizer (X : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) Lc m f :=
  neighbour_overgroup_omega hmf hcat hset.standardSetting.kProper
    (F4Pilot.centralizer_ne_top_of_ne_bot hset.standardSetting.simple hset.standardSetting.nonab
      hX) htX ht hDX hDq htag (LinearPilot.lieModel_quotient_center_of_center_eq_bot hZD hDm)
    (odd_card_center_of_center_eq_bot hZD) hcomp hsyl hstd hnn

end Generic

section Plus

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem neighbour_overgroup_pairTorus_of_not_normal (hset : SeitzSetting G L) {n f : ℕ}
    (hcat : OmegaCatalogueClausesAt (n - 1)) {K : Type} [Field K] (hKc : Nat.card K = 2 ^ f)
    (hq : 4 ≤ Nat.card K) (hn : 5 ≤ n) (k : Fin n)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus n K)) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    {X : Subgroup G} (hX : X = ((pairTorus (K := K) k).map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G))
    {D : Subgroup G} (hDe : D = ((pairPerp (K := K) k).map e.symm.toMonoidHom).map L.subtype)
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
  have := LinearPilot.finite_of_card_eq_two_pow hKc
  have := LinearPilot.charP_two_of_card_eq_two_pow hKc
  obtain ⟨-, -, -, hcard, -, -, hDC, hDq, hZ, hLie, -⟩ :=
    neighbour_data_pairTorus hKc hq hn k e htC hX hDe
  have hXne : X ≠ ⊥ := ne_bot_of_one_lt_card (by rw [hcard]; omega)
  obtain ⟨hcomp, hsyl, hstd⟩ :=
    neighbour_standard_pairTorus_of_seitzSetting hset hKc hq hn k e htC ht hX htX hDe
  exact neighbour_overgroup_omega_of_seitzSetting hset (ne_four_one_of_four_le_card hKc hq _) hcat
    hXne htX ht (hDC.trans inf_le_left) hDq hZ (Or.inl rfl) hLie hcomp hsyl hstd hnn

end Plus

section Minus

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem neighbour_overgroup_minusPairTorus (hset : SeitzSetting G L) {n f : ℕ}
    (hcat : OmegaCatalogueClausesAt (n - 1)) {K : Type} [Field K] (hKc : Nat.card K = 2 ^ f)
    (hq : 4 ≤ Nat.card K) (hn : 5 ≤ n) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (k : Fin (n - 1)) (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c))
    {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {X : Subgroup G}
    (hX : X = ((minusPairTorus (K := K) (by omega) b c k).map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G}
    (hDe : D = ((minusPairPerp (K := K) (by omega) b c k).map e.symm.toMonoidHom).map L.subtype)
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
  have := LinearPilot.finite_of_card_eq_two_pow hKc
  have := LinearPilot.charP_two_of_card_eq_two_pow hKc
  obtain ⟨-, -, -, hcard, -, -, hDC, hDq, hZ, hLie, -⟩ :=
    neighbour_data_minusPairTorus hKc hq hn hirr k e htC hX hDe
  have hXne : X ≠ ⊥ := ne_bot_of_one_lt_card (by rw [hcard]; omega)
  obtain ⟨hcomp, hsyl, hstd⟩ :=
    neighbour_standard_minusPairTorus_of_seitzSetting hset hKc hq hn hirr k e htC ht hX htX hDe
  exact neighbour_overgroup_omega_of_seitzSetting hset (ne_four_one_of_four_le_card hKc hq _) hcat
    hXne htX ht (hDC.trans inf_le_left) hDq hZ (Or.inr rfl) hLie hcomp hsyl hstd hnn

end Minus

end CFSG.SeitzReduction.OmegaPilot
