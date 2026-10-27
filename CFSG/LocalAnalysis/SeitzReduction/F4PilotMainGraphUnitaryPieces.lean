module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphUnitaryInputs
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphUnitaryPiecesCore
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphUnitaryPiecesSL2

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (IsPrimeFormGram blockSwapJ)
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.SeitzReduction.LinearPilot (blockSpecialLinear blockSpecialLinear_mono)
open CFSG.ComponentClassification.UnbalancedCatalog.UnitaryFieldTransfer (fixedField_finite)
open CFSG.Quasithin (perfectCore)
open scoped commutatorElement

section PermGram

variable (F : Type) [Field F]

@[expose] def uPiecePerm6 : Fin 6 → Fin 6 := ![3, 4, 5, 0, 1, 2]

@[expose] def uPiecePerm7 : Fin 7 → Fin 7 := ![3, 4, 5, 0, 1, 2, 6]

theorem isPermGram_graphGram6 :
    IsPermGram ((graphGram6 F : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) uPiecePerm6 where
  invol := (by decide : ∀ i : Fin 6, uPiecePerm6 (uPiecePerm6 i) = i)
  apply i j := by
    have key : ∀ i j : Fin 6, ((j : ℕ) = i + 3 ∨ (i : ℕ) = j + 3) ↔ uPiecePerm6 i = j := by
      decide
    rw [coe_graphGram6]
    simp only [blockSwapJ, of_apply]
    exact if_congr (key i j) rfl rfl

theorem isPermGram_graphGram7 :
    IsPermGram ((graphGram7 F : GL (Fin 7) F) : Matrix (Fin 7) (Fin 7) F) uPiecePerm7 where
  invol := (by decide : ∀ i : Fin 7, uPiecePerm7 (uPiecePerm7 i) = i)
  apply i j := by
    have key : ∀ i j : Fin 7, (((i : ℕ) < 3 ∧ (j : ℕ) = i + 3) ∨ ((j : ℕ) < 3 ∧ (i : ℕ) = j + 3) ∨
        ((i : ℕ) = 6 ∧ (j : ℕ) = 6)) ↔ uPiecePerm7 i = j := by
      decide
    rw [coe_graphGram7]
    simp only [gram7, of_apply]
    exact if_congr (key i j) rfl rfl

end PermGram

section Tori

variable {f : ℕ} {F : Type} [Field F] (h : UnitaryFieldData 2 f F)

theorem uPiece_map_torus {X Y M : Type*} [Group X] [Group Y] [Group M] {n : ℕ}
    (uE : StatedSp 3 h.fixedField →* M) (j : M →* SpecialLinearGroup (Fin n) F)
    (τ : (Fin 3 → Fˣ) →* SpecialLinearGroup (Fin n) F)
    (hτ : ∀ t, j (uE (sp6Diag _ t)) =
      τ (fun i => Units.map (h.fixedField.subtype : h.fixedField →* F) (t i)))
    (P : Subgroup X) (πk : X →* (Fin 3 → h.fixedFieldˣ)) (πF : Y →* (Fin 3 → Fˣ)) (V : X →* Y)
    (hV : ∀ x i, Units.map (h.fixedField.subtype : h.fixedField →* F) (πk x i) = πF (V x) i) :
    ((P.map ((sp6Diag h.fixedField).comp πk)).map uE).map j = (P.map V).map (τ.comp πF) := by
  rw [Subgroup.map_map, Subgroup.map_map, Subgroup.map_map]
  congr 1
  refine MonoidHom.ext fun x => ?_
  simp only [MonoidHom.comp_apply, hτ]
  congr 1
  funext i
  exact hV x i

theorem uPiece_paramA (a : h.fixedFieldˣ) (i : Fin 3) :
    Units.map (h.fixedField.subtype : h.fixedField →* F) (sp6ParamA _ a i) =
      sp6ParamA F (Units.map (h.fixedField.subtype : h.fixedField →* F) a) i := by
  rw [sp6ParamA_apply, sp6ParamA_apply]
  fin_cases i <;> simp

theorem uPiece_paramM2 (p : h.fixedFieldˣ × h.fixedFieldˣ) (i : Fin 3) :
    Units.map (h.fixedField.subtype : h.fixedField →* F) (sp6ParamM2 _ p i) =
      sp6ParamM2 F (((Units.map (h.fixedField.subtype : h.fixedField →* F)).prodMap
        (Units.map (h.fixedField.subtype : h.fixedField →* F))) p) i := by
  rw [sp6ParamM2_apply, sp6ParamM2_apply]
  fin_cases i <;> simp

theorem uPiece_paramM3 (p : h.fixedFieldˣ × h.fixedFieldˣ) (i : Fin 3) :
    Units.map (h.fixedField.subtype : h.fixedField →* F) (sp6ParamM3 _ p i) =
      sp6ParamM3 F (((Units.map (h.fixedField.subtype : h.fixedField →* F)).prodMap
        (Units.map (h.fixedField.subtype : h.fixedField →* F))) p) i := by
  rw [sp6ParamM3_apply, sp6ParamM3_apply]
  fin_cases i <;> simp

@[expose] noncomputable def uPieceUnits : Subgroup Fˣ :=
  (Units.map (h.fixedField.subtype : h.fixedField →* F)).range

theorem uPiece_top_prod_map :
    ((⊤ : Subgroup h.fixedFieldˣ).prod ⊤).map
      ((Units.map (h.fixedField.subtype : h.fixedField →* F)).prodMap
        (Units.map (h.fixedField.subtype : h.fixedField →* F))) =
      (uPieceUnits h).prod (uPieceUnits h) := by
  rw [top_prod_top, ← MonoidHom.range_eq_map, MonoidHom.range_prodMap]
  rfl

theorem uPiece_map_torusA6 :
    ((sp6TorusA (⊤ : Subgroup h.fixedFieldˣ)).map (uEmbed6 h)).map (gramSUToSL h _) =
      linTorusA (lin6Torus F) (uPieceUnits h) := by
  rw [sp6TorusA, uPiece_map_torus h (uEmbed6 h) _ (lin6Torus F) (gramSUToSL_uEmbed6_sp6Diag h) ⊤
    (sp6ParamA _) (sp6ParamA F) _ (uPiece_paramA h), linTorusA, uPieceUnits,
    MonoidHom.range_eq_map]

theorem uPiece_map_torusM2_6 :
    ((sp6TorusM2 (⊤ : Subgroup h.fixedFieldˣ)).map (uEmbed6 h)).map (gramSUToSL h _) =
      linTorusM2 (lin6Torus F) (uPieceUnits h) := by
  rw [sp6TorusM2, uPiece_map_torus h (uEmbed6 h) _ (lin6Torus F) (gramSUToSL_uEmbed6_sp6Diag h)
    _ (sp6ParamM2 _) (sp6ParamM2 F) _ (uPiece_paramM2 h), linTorusM2, uPiece_top_prod_map]

theorem uPiece_map_torusM3_6 :
    ((sp6TorusM3 (⊤ : Subgroup h.fixedFieldˣ)).map (uEmbed6 h)).map (gramSUToSL h _) =
      linTorusM3 (lin6Torus F) (uPieceUnits h) := by
  rw [sp6TorusM3, uPiece_map_torus h (uEmbed6 h) _ (lin6Torus F) (gramSUToSL_uEmbed6_sp6Diag h)
    _ (sp6ParamM3 _) (sp6ParamM3 F) _ (uPiece_paramM3 h), linTorusM3, uPiece_top_prod_map]

theorem uPiece_map_torusA7 :
    ((sp6TorusA (⊤ : Subgroup h.fixedFieldˣ)).map (uEmbed7 h)).map (gramSUToSL h _) =
      linTorusA (lin7Torus F) (uPieceUnits h) := by
  rw [sp6TorusA, uPiece_map_torus h (uEmbed7 h) _ (lin7Torus F) (gramSUToSL_uEmbed7_sp6Diag h) ⊤
    (sp6ParamA _) (sp6ParamA F) _ (uPiece_paramA h), linTorusA, uPieceUnits,
    MonoidHom.range_eq_map]

theorem uPiece_map_torusM2_7 :
    ((sp6TorusM2 (⊤ : Subgroup h.fixedFieldˣ)).map (uEmbed7 h)).map (gramSUToSL h _) =
      linTorusM2 (lin7Torus F) (uPieceUnits h) := by
  rw [sp6TorusM2, uPiece_map_torus h (uEmbed7 h) _ (lin7Torus F) (gramSUToSL_uEmbed7_sp6Diag h)
    _ (sp6ParamM2 _) (sp6ParamM2 F) _ (uPiece_paramM2 h), linTorusM2, uPiece_top_prod_map]

theorem uPiece_map_torusM3_7 :
    ((sp6TorusM3 (⊤ : Subgroup h.fixedFieldˣ)).map (uEmbed7 h)).map (gramSUToSL h _) =
      linTorusM3 (lin7Torus F) (uPieceUnits h) := by
  rw [sp6TorusM3, uPiece_map_torus h (uEmbed7 h) _ (lin7Torus F) (gramSUToSL_uEmbed7_sp6Diag h)
    _ (sp6ParamM3 _) (sp6ParamM3 F) _ (uPiece_paramM3 h), linTorusM3, uPiece_top_prod_map]

theorem uPiece_exists_mem_units (hf : 2 ≤ f) :
    ∃ a₀ ∈ uPieceUnits h, a₀ ^ 2 ≠ 1 := by
  have := fixedField_finite h
  have hk : 4 ≤ Nat.card h.fixedField := by
    rw [h.card_fixedField]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨a, ha⟩ := exists_units_sq_ne_one_of_four_le hk
  refine ⟨Units.map (h.fixedField.subtype : h.fixedField →* F) a, ⟨a, rfl⟩, fun h2 => ha ?_⟩
  apply Units.map_injective (f := (h.fixedField.subtype : h.fixedField →* F))
    h.fixedField.subtype.injective
  rw [map_pow, h2, map_one]

end Tori

section Pieces

variable {f : ℕ} {F : Type} [Field F] (h : UnitaryFieldData 2 f F)

theorem uPiece_ordSU_two (q : ℕ) : ordSU 2 q = ordSL 2 q := by
  simp [ordSU, ordSL]

theorem uPiece_natCard_piece {n : ℕ} {C : GL (Fin n) F} (hC : IsPrimeFormGram C) (hn : 3 ≤ n)
    (hnq : ¬(n = 3 ∧ 2 ^ f = 2)) {G : Type} [Group G] [Finite G]
    (Φ : gramSU h (C : Matrix (Fin n) (Fin n) F) →* G)
    (hker : Φ.ker ≤ center (gramSU h (C : Matrix (Fin n) (Fin n) F)))
    (S : Subgroup (gramSU h (C : Matrix (Fin n) (Fin n) F)))
    {T B : Subgroup (SpecialLinearGroup (Fin n) F)} (hST : S.map (gramSUToSL h _) = T)
    (hB : perfectCore (centralizer (T : Set (SpecialLinearGroup (Fin n) F))) = B)
    (hrig : ∀ y : SpecialLinearGroup (Fin n) F,
      (∀ s ∈ T, ⁅y, s⁆ ∈ center (SpecialLinearGroup (Fin n) F)) →
        y ∈ centralizer (T : Set (SpecialLinearGroup (Fin n) F)))
    {I : Finset (Fin n)} {i₀ : Fin n} (hi₀ : i₀ ∉ I) (hBI : B ≤ blockSpecialLinear I)
    (hperf : ⁅(gramSUToSL h (C : Matrix (Fin n) (Fin n) F)).range ⊓ B,
      (gramSUToSL h (C : Matrix (Fin n) (Fin n) F)).range ⊓ B⁆ =
        (gramSUToSL h (C : Matrix (Fin n) (Fin n) F)).range ⊓ B) :
    Nat.card (perfectCore (Φ.range ⊓ centralizer ((S.map Φ : Subgroup G) : Set G))) =
      Nat.card ((gramSUToSL h (C : Matrix (Fin n) (Fin n) F)).range ⊓ B : Subgroup _) := by
  have := h.finite
  subst hST
  exact uPiece_natCard (gramSUToSL h _) (gramSUToSL_injective h _)
    (fun z hz => gramSUToSL_mem_center h hC hn hnq hz) S hB hrig
    (inf_center_eq_bot_of_le_blockSpecialLinear hi₀ hBI) hperf Φ hker

omit [Field F] in
theorem uPiece_four_le_pow (hf : 2 ≤ f) : 4 ≤ 2 ^ f :=
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf

include h in
theorem uPiece_four_le_card (hf : 2 ≤ f) : 4 ≤ Nat.card F := by
  rw [h.card_eq_sq]
  exact (uPiece_four_le_pow hf).trans (Nat.le_self_pow (by norm_num) _)

end Pieces

section Unitary6

variable {f : ℕ} {F : Type} [Field F] (h : UnitaryFieldData 2 f F) (hf : 2 ≤ f)
include hf

theorem pieceCards_unitary6 {G : Type} [Group G] [Finite G] (Φ : uGroup6 h →* G)
    (hker : Φ.ker ≤ center (uGroup6 h)) :
    pieceCards Φ.range (((sp6TorusA (⊤ : Subgroup h.fixedFieldˣ)).map (uEmbed6 h)).map Φ)
      (((sp6TorusM2 (⊤ : Subgroup h.fixedFieldˣ)).map (uEmbed6 h)).map Φ)
      (((sp6TorusM3 (⊤ : Subgroup h.fixedFieldˣ)).map (uEmbed6 h)).map Φ) =
        pieceOrders .unitary6 (2 ^ f) := by
  classical
  have := h.finite
  have hF := uPiece_four_le_card h hf
  have hq := uPiece_four_le_pow hf
  obtain ⟨a₀, ha₀, hsq⟩ := uPiece_exists_mem_units h hf
  have hC := isPermGram_graphGram6 F
  have hnq : ¬(6 = 3 ∧ 2 ^ f = 2) := by omega
  have hA := uPiece_natCard_piece h (isPrimeFormGram_graphGram6 F) (by norm_num) hnq Φ hker _
    (uPiece_map_torusA6 h) (perfectCore_centralizer_lin6TorusA hF ha₀ hsq)
    (rigid_lin6 (.inl rfl) ha₀ hsq) (i₀ := 0) (I := lin6BlockA) (by decide) le_rfl
    (hC.natCard_and_commutator_range_inf_blockSpecialLinear h (by decide) (by decide)
      ⟨fun _ => hq, fun _ => by omega⟩).2
  rw [(hC.natCard_and_commutator_range_inf_blockSpecialLinear h (I := lin6BlockA) (by decide)
    (by decide) ⟨fun _ => hq, fun _ => by omega⟩).1] at hA
  have hM2 := uPiece_natCard_piece h (isPrimeFormGram_graphGram6 F) (by norm_num) hnq Φ hker _
    (uPiece_map_torusM2_6 h) (perfectCore_centralizer_lin6TorusM2 hF ha₀ hsq)
    (rigid_lin6 (.inr (.inl rfl)) ha₀ hsq) (i₀ := 0) (I := lin6BlockM2) (by decide) le_rfl
    (hC.natCard_and_commutator_range_inf_blockSpecialLinear h (by decide) (by decide)
      ⟨fun _ => hq, fun _ => by omega⟩).2
  rw [(hC.natCard_and_commutator_range_inf_blockSpecialLinear h (I := lin6BlockM2) (by decide)
    (by decide) ⟨fun _ => hq, fun _ => by omega⟩).1] at hM2
  have hE : ∀ i, i ∈ linBlockF 6 ↔ uPiecePerm6 i ∈ linBlockE 6 := by decide
  have hE' : ∀ i, i ∈ linBlockE 6 ↔ uPiecePerm6 i ∈ linBlockF 6 := by decide
  have hd : Disjoint (linBlockE 6) (linBlockF 6) := by decide
  have hperfE := CFSG.SeitzReduction.LinearPilot.commutator_blockSpecialLinear_eq_of_two_le
    (I := linBlockE 6) (by decide) hF
  have hM3 := uPiece_natCard_piece h (isPrimeFormGram_graphGram6 F) (by norm_num) hnq Φ hker _
    (uPiece_map_torusM3_6 h) (perfectCore_centralizer_lin6TorusM3 hF ha₀ hsq)
    (rigid_lin6 (.inr (.inr rfl)) ha₀ hsq) (i₀ := 0) (I := {1, 2, 4, 5}) (by decide)
    (sup_le (blockSpecialLinear_mono (by decide)) (blockSpecialLinear_mono (by decide)))
    (commutator_range_inf_sup h hC hd hE hE' hperfE)
  rw [natCard_range_inf_sup h hC hd hE hE', natCard_blockSpecialLinear (by decide),
    h.card_eq_sq] at hM3
  have h4 : lin6BlockA.card = 4 := by decide
  have h2 : lin6BlockM2.card = 2 := by decide
  have hE2 : (linBlockE 6).card = 2 := by decide
  rw [pieceCards, hA, hM2, hM3, h4, h2, hE2, uPiece_ordSU_two]
  rfl

end Unitary6

section Unitary7

variable {f : ℕ} {F : Type} [Field F] (h : UnitaryFieldData 2 f F) (hf : 2 ≤ f)
include hf

theorem pieceCards_unitary7 {G : Type} [Group G] [Finite G] (Φ : uGroup7 h →* G)
    (hker : Φ.ker ≤ center (uGroup7 h)) :
    pieceCards Φ.range (((sp6TorusA (⊤ : Subgroup h.fixedFieldˣ)).map (uEmbed7 h)).map Φ)
      (((sp6TorusM2 (⊤ : Subgroup h.fixedFieldˣ)).map (uEmbed7 h)).map Φ)
      (((sp6TorusM3 (⊤ : Subgroup h.fixedFieldˣ)).map (uEmbed7 h)).map Φ) =
        pieceOrders .unitary7 (2 ^ f) := by
  classical
  have := h.finite
  have hF := uPiece_four_le_card h hf
  have hq := uPiece_four_le_pow hf
  obtain ⟨a₀, ha₀, hsq⟩ := uPiece_exists_mem_units h hf
  have hC := isPermGram_graphGram7 F
  have hnq : ¬(7 = 3 ∧ 2 ^ f = 2) := by omega
  have hA := uPiece_natCard_piece h (isPrimeFormGram_graphGram7 F) (by norm_num) hnq Φ hker _
    (uPiece_map_torusA7 h) (perfectCore_centralizer_lin7TorusA hF ha₀ hsq)
    (rigid_lin7 (.inl rfl) ha₀ hsq) (i₀ := 0) (I := lin7BlockA) (by decide) le_rfl
    (hC.natCard_and_commutator_range_inf_blockSpecialLinear h (by decide) (by decide)
      ⟨fun _ => hq, fun _ => by omega⟩).2
  rw [(hC.natCard_and_commutator_range_inf_blockSpecialLinear h (I := lin7BlockA) (by decide)
    (by decide) ⟨fun _ => hq, fun _ => by omega⟩).1] at hA
  have hM2 := uPiece_natCard_piece h (isPrimeFormGram_graphGram7 F) (by norm_num) hnq Φ hker _
    (uPiece_map_torusM2_7 h) (perfectCore_centralizer_lin7TorusM2 hF ha₀ hsq)
    (rigid_lin7 (.inr (.inl rfl)) ha₀ hsq) (i₀ := 0) (I := lin7BlockM2) (by decide) le_rfl
    (hC.natCard_and_commutator_range_inf_blockSpecialLinear h (by decide) (by decide)
      ⟨fun _ => hq, fun _ => by omega⟩).2
  rw [(hC.natCard_and_commutator_range_inf_blockSpecialLinear h (I := lin7BlockM2) (by decide)
    (by decide) ⟨fun _ => hq, fun _ => by omega⟩).1] at hM2
  have hE : ∀ i, i ∈ linBlockF 7 ↔ uPiecePerm7 i ∈ linBlockE 7 := by decide
  have hE' : ∀ i, i ∈ linBlockE 7 ↔ uPiecePerm7 i ∈ linBlockF 7 := by decide
  have hd : Disjoint (linBlockE 7) (linBlockF 7) := by decide
  have hperfE := CFSG.SeitzReduction.LinearPilot.commutator_blockSpecialLinear_eq_of_two_le
    (I := linBlockE 7) (by decide) hF
  have hM3 := uPiece_natCard_piece h (isPrimeFormGram_graphGram7 F) (by norm_num) hnq Φ hker _
    (uPiece_map_torusM3_7 h) (perfectCore_centralizer_lin7TorusM3 hF ha₀ hsq)
    (rigid_lin7 (.inr (.inr rfl)) ha₀ hsq) (i₀ := 0) (I := {1, 2, 4, 5}) (by decide)
    (sup_le (blockSpecialLinear_mono (by decide)) (blockSpecialLinear_mono (by decide)))
    (commutator_range_inf_sup h hC hd hE hE' hperfE)
  rw [natCard_range_inf_sup h hC hd hE hE', natCard_blockSpecialLinear (by decide),
    h.card_eq_sq] at hM3
  have h5 : lin7BlockA.card = 5 := by decide
  have h3 : lin7BlockM2.card = 3 := by decide
  have hE2 : (linBlockE 7).card = 2 := by decide
  rw [pieceCards, hA, hM2, hM3, h5, h3, hE2]
  rfl

end Unitary7

theorem unitaryModelPiecesInput_holds : UnitaryModelPiecesInput :=
  fun _ _ _ h hf _ _ _ => ⟨pieceCards_unitary6 h hf, pieceCards_unitary7 h hf⟩

end CFSG.SeitzReduction.F4Pilot
