module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphTorusCover
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphTorusExact
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphTorusEmbed
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotFieldNeighbourFix
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotUniqueStep3Transfer
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainPieceTables

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.EvenSmallLie
  CFSG.Assembly.LowTwoRank
open Matrix
open CFSG.Quasithin (perfectCore)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

local instance f4PilotMainGraphTorusMainNeZeroRank : NeZero Tag.F4.rank := ⟨by decide⟩

theorem nodePermPow_one_one_two :
    nodePermPow 1 ({1, 2} : Finset (Fin (Tag.rank .F4))) = {1, 2} := by
  decide

theorem nodePermPow_one_one :
    nodePermPow 1 ({1} : Finset (Fin (Tag.rank .F4))) = {2} := by
  decide

theorem nodePermPow_one_two :
    nodePermPow 1 ({2} : Finset (Fin (Tag.rank .F4))) = {1} := by
  decide

section Graph

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K CFSG.LieType.Ree.ReeTag.F4.prime]

theorem leviTorusG_trans_graphAutF4_symm (e : L ≃* adjointGroup .F4 K)
    (J : Finset (Fin (Tag.rank .F4))) :
    leviTorusG (e.trans (graphAutF4 K).symm) J = leviTorusG e (nodePermPow 1 J) := by
  have h := map_graphAutF4_pow_leviTorus_subgroupOf (K := K) 1 J
  rw [pow_one] at h
  have e1 : (e.trans (graphAutF4 K).symm).symm.toMonoidHom =
      e.symm.toMonoidHom.comp (graphAutF4 K).toMonoidHom := by
    ext1 x
    rfl
  rw [leviTorusG, leviTorusG, modelToG, modelToG, e1, ← Subgroup.map_map, h]

end Graph

theorem graphTorus_nonempty_ringEquiv {K : Type} [Field K] [Finite K] {F : Type} [Field F]
    [Finite F] {f : ℕ}
    (hF : Nat.card F = 2 ^ f) (hK : Nat.card K = 2 ^ f) : Nonempty (F ≃+* K) := by
  have := Fintype.ofFinite F
  have := Fintype.ofFinite K
  have hc : Fintype.card F = Fintype.card K := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hF, hK]
  exact ⟨FiniteField.ringEquivOfCardEq hc⟩

section Main

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem exists_exact6_X {t : G} {f : ℕ} (hw : F4Work L K t f) (hf : 2 ≤ f)
    (e : L ≃* adjointGroup .F4 K) (hX : HR8Kind e t f .X .linear6) {F : Type} [Field F]
    [Finite F] (hF : Nat.card F = 2 ^ f) (Φ : SpecialLinearGroup (Fin 6) F →* G)
    (hE : Φ.range = neighbourCore e .X) (hker : Φ.ker ≤ center (SpecialLinearGroup (Fin 6) F)) :
    ∃ Φ' : SpecialLinearGroup (Fin 6) F →* G, Φ'.range = neighbourCore e .X ∧
      Φ'.ker ≤ center (SpecialLinearGroup (Fin 6) F) ∧
      (linTorusA (lin6Torus F) ⊤).map Φ' = leviTorusG e {1, 2} ⊓ neighbourLeviG e .X ∧
      (linTorusM2 (lin6Torus F) ⊤).map Φ' = leviTorusG e {1} ⊓ neighbourLeviG e .X ∧
      (linTorusM3 (lin6Torus F) ⊤).map Φ' = leviTorusG e {2} ⊓ neighbourLeviG e .X := by
  have : CharP F 2 := charP_two_of_natCard_eq_two_pow hF
  obtain ⟨ε⟩ := graphTorus_nonempty_ringEquiv hF hw.card_eq
  obtain ⟨Φ₁, hr₁, hk₁, hc₁⟩ := exists_graphCover6_X hw hf e hX hF Φ hE hker
  have hD : perfectCore (Φ₁.range ⊓ centralizer ({t} : Set G)) = neighbourLeviG e .X := by
    rw [hr₁, perfectCore_neighbourCore_inf_centralizer_X hw hf e, neighbourLeviG_eq_modelToG]
  obtain ⟨Φ', hr, hk, hA, h2, h3⟩ := exists_exact_of_cover e ε sp6ToSL6_injective
    sp6ToSL6_sp6Diag sp6ToSL6_statedSpMap fixedSubgroup_graphGram6 Φ₁ hk₁ hc₁ hD
  exact ⟨Φ', hr.trans hr₁, hk, hA, h2, h3⟩

theorem exists_exact7_X {t : G} {f : ℕ} (hw : F4Work L K t f) (hf : 2 ≤ f)
    (e : L ≃* adjointGroup .F4 K) (hX : HR8Kind e t f .X .linear7) {F : Type} [Field F]
    [Finite F] (hF : Nat.card F = 2 ^ f) (Φ : SpecialLinearGroup (Fin 7) F →* G)
    (hE : Φ.range = neighbourCore e .X) (hker : Φ.ker ≤ center (SpecialLinearGroup (Fin 7) F)) :
    ∃ Φ' : SpecialLinearGroup (Fin 7) F →* G, Φ'.range = neighbourCore e .X ∧
      Φ'.ker ≤ center (SpecialLinearGroup (Fin 7) F) ∧
      (linTorusA (lin7Torus F) ⊤).map Φ' = leviTorusG e {1, 2} ⊓ neighbourLeviG e .X ∧
      (linTorusM2 (lin7Torus F) ⊤).map Φ' = leviTorusG e {1} ⊓ neighbourLeviG e .X ∧
      (linTorusM3 (lin7Torus F) ⊤).map Φ' = leviTorusG e {2} ⊓ neighbourLeviG e .X := by
  have : CharP F 2 := charP_two_of_natCard_eq_two_pow hF
  obtain ⟨ε⟩ := graphTorus_nonempty_ringEquiv hF hw.card_eq
  obtain ⟨Φ₁, hr₁, hk₁, hc₁⟩ := exists_graphCover7_X hw hf e hX hF Φ hE hker
  have hD : perfectCore (Φ₁.range ⊓ centralizer ({t} : Set G)) = neighbourLeviG e .X := by
    rw [hr₁, perfectCore_neighbourCore_inf_centralizer_X hw hf e, neighbourLeviG_eq_modelToG]
  obtain ⟨Φ', hr, hk, hA, h2, h3⟩ := exists_exact_of_cover e ε sp6ToSL7_injective
    sp6ToSL7_sp6Diag sp6ToSL7_statedSpMap fixedSubgroup_graphGram7 Φ₁ hk₁ hc₁ hD
  exact ⟨Φ', hr.trans hr₁, hk, hA, h2, h3⟩

theorem linearGraphTorusExactInput_holds : LinearGraphTorusExactInput := by
  intro G _ _ L K _ _ _ e t f hw hf N hN
  have : CharP K CFSG.LieType.Ree.ReeTag.F4.prime := charP_two_of_natCard_eq_two_pow hw.card_eq
  cases N with
  | X =>
    exact ⟨fun hk F _ _ hF Φ hE hker => exists_exact6_X hw hf e hk hF Φ hE hker,
      fun hk F _ _ hF Φ hE hker => exists_exact7_X hw hf e hk hF Φ hE hker⟩
  | Y =>
    refine ⟨fun hk F _ _ hF Φ hE hker => ?_, fun hk F _ _ hF Φ hE hker => ?_⟩
    · rw [neighbourCore_Y_eq_X] at hE ⊢
      obtain ⟨Φ', hr, hk', hA, h2, h3⟩ :=
        exists_exact6_X hw hf _ ((hr8Kind_Y_iff_X e).1 hk) hF Φ hE hker
      refine ⟨Φ', hr, hk', ?_, ?_, ?_⟩
      · rw [hA, leviTorusG_trans_graphAutF4_symm, nodePermPow_one_one_two, ← neighbourLeviG_Y_eq_X]
      · rw [h2, leviTorusG_trans_graphAutF4_symm, nodePermPow_one_one, ← neighbourLeviG_Y_eq_X]
        rfl
      · rw [h3, leviTorusG_trans_graphAutF4_symm, nodePermPow_one_two, ← neighbourLeviG_Y_eq_X]
        rfl
    · rw [neighbourCore_Y_eq_X] at hE ⊢
      obtain ⟨Φ', hr, hk', hA, h2, h3⟩ :=
        exists_exact7_X hw hf _ ((hr8Kind_Y_iff_X e).1 hk) hF Φ hE hker
      refine ⟨Φ', hr, hk', ?_, ?_, ?_⟩
      · rw [hA, leviTorusG_trans_graphAutF4_symm, nodePermPow_one_one_two, ← neighbourLeviG_Y_eq_X]
      · rw [h2, leviTorusG_trans_graphAutF4_symm, nodePermPow_one_one, ← neighbourLeviG_Y_eq_X]
        rfl
      · rw [h3, leviTorusG_trans_graphAutF4_symm, nodePermPow_one_two, ← neighbourLeviG_Y_eq_X]
        rfl
  | X' => exact absurd rfl hN

theorem graphPieceTablesInput_of_unitaryOmega (hUO : UnitaryOmegaPieceTablesInput) :
    GraphPieceTablesInput :=
  graphPieceTablesInput_of_exactInput linearGraphTorusExactInput_holds hUO

end Main

end CFSG.SeitzReduction.F4Pilot
