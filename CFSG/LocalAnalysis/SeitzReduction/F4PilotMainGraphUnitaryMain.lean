module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphUnitaryInputs
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphUnitaryExact
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphUnitaryNormal
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphUnitaryCover
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphTorusMain
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphUnitaryLift

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.EvenSmallLie
  CFSG.Assembly.LowTwoRank
open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.Quasithin (perfectCore)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.UnbalancedCatalog.UnitaryFieldTransfer
  (fixedField_charP fixedField_finite)

local instance f4PilotMainGraphUnitaryMainNeZeroRank : NeZero Tag.F4.rank := ⟨by decide⟩

theorem unitaryFieldData_of_card {F : Type} [Field F] {f : ℕ} (hf : 1 ≤ f)
    (hF : Nat.card F = (2 ^ f) ^ 2) : UnitaryFieldData 2 f F :=
  ⟨Nat.prime_two, hf, by rw [hF, ← pow_mul, mul_comm]⟩

theorem finite_gramSU {p f n : ℕ} {F : Type} [Field F] (h : UnitaryFieldData p f F)
    (C : Matrix (Fin n) (Fin n) F) : Finite (gramSU h C) := by
  have : Finite F := h.finite
  have : Finite (Matrix (Fin n) (Fin n) F) := inferInstance
  have : Finite (GL (Fin n) F) :=
    Finite.of_injective (fun g : GL (Fin n) F => (g : Matrix (Fin n) (Fin n) F)) Units.val_injective
  infer_instance

theorem exists_mulAut_uEmbed6 {f : ℕ} {F : Type} [Field F] (h : UnitaryFieldData 2 f F)
    (ρ : h.fixedField ≃+* h.fixedField) :
    ∃ ρ' : MulAut (uGroup6 h), ∀ g,
      ρ' (uEmbed6 h g) = uEmbed6 h (statedSpMap (ρ : h.fixedField →+* h.fixedField) 3 g) := by
  obtain ⟨ρ'', hρ''⟩ := exists_ringEquiv_extend h ρ
  exact ⟨primeFormFieldSU h (isPrimeFormGram_graphGram6 F) ρ'',
    primeFormFieldSU_uEmbed6 h hρ''⟩

theorem exists_mulAut_uEmbed7 {f : ℕ} {F : Type} [Field F] (h : UnitaryFieldData 2 f F)
    (ρ : h.fixedField ≃+* h.fixedField) :
    ∃ ρ' : MulAut (uGroup7 h), ∀ g,
      ρ' (uEmbed7 h g) = uEmbed7 h (statedSpMap (ρ : h.fixedField →+* h.fixedField) 3 g) := by
  obtain ⟨ρ'', hρ''⟩ := exists_ringEquiv_extend h ρ
  exact ⟨primeFormFieldSU h (isPrimeFormGram_graphGram7 F) ρ'',
    primeFormFieldSU_uEmbed7 h hρ''⟩

theorem ker_comp_mulEquiv_le_center {G M M' : Type} [Group G] [Group M] [Group M'] (Φ : M' →* G)
    (hker : Φ.ker ≤ center M') (Ψ : M ≃* M') : (Φ.comp Ψ.toMonoidHom).ker ≤ center M := by
  intro g hg
  have h1 : Ψ g ∈ center M' := hker hg
  rw [← Subgroup.map_center_eq (Ψ.symm : M' ≃* M)]
  exact ⟨Ψ g, h1, Ψ.symm_apply_apply g⟩

section MainX


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem exists_unitaryExact6_X {t : G} {f : ℕ} (hw : F4Work L K t f) (hf : 2 ≤ f)
    (e : L ≃* adjointGroup .F4 K) (hX : HR8Kind e t f .X .unitary6) :
    ∃ (F : Type) (_ : Field F) (h : UnitaryFieldData 2 f F) (Φ : uGroup6 h →* G),
      Φ.range = neighbourCore e .X ∧ Φ.ker ≤ center (uGroup6 h) ∧
      ((sp6TorusA (⊤ : Subgroup h.fixedFieldˣ)).map (uEmbed6 h)).map Φ =
        leviTorusG e {1, 2} ⊓ neighbourLeviG e .X ∧
      ((sp6TorusM2 (⊤ : Subgroup h.fixedFieldˣ)).map (uEmbed6 h)).map Φ =
        leviTorusG e {1} ⊓ neighbourLeviG e .X ∧
      ((sp6TorusM3 (⊤ : Subgroup h.fixedFieldˣ)).map (uEmbed6 h)).map Φ =
        leviTorusG e {2} ⊓ neighbourLeviG e .X := by
  have hq4 : 4 ≤ 2 ^ f :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨F, _, _, hF, Φ₀, hE₀, hker₀⟩ := exists_su6_cover_neighbourCore hw hf e (by decide) hX
  have : CharP F 2 := charP_two_of_natCard_eq_two_pow (f := 2 * f) (by
    rw [hF, ← pow_mul, mul_comm])
  have h : UnitaryFieldData 2 f F := unitaryFieldData_of_card (by omega) hF
  have eS : StatedSU 6 (2 ^ f) F = gramSU h ((1 : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) := by
    rw [Units.val_one]
    exact unitarySU_eq_gramSU h 6
  set eM := MulEquiv.subgroupCongr eS
  set Φ₁ := Φ₀.comp eM.symm.toMonoidHom with hΦ₁
  have hE₁ : Φ₁.range = neighbourCore e .X := by
    rw [hΦ₁, MonoidHom.range_comp, MonoidHom.range_eq_top.2 eM.symm.surjective,
      ← MonoidHom.range_eq_map, hE₀]
  have hker₁ := ker_comp_mulEquiv_le_center Φ₀ hker₀ eM.symm
  have := finite_gramSU h ((1 : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F)
  have := CFSG.RankThree.Classical.isPerfect_gramSU_one h (n := 6) (by norm_num) (by omega)
  have hsplit := forall_exists_section_of_mulEquiv eM.symm
    (statedSU_even_split hF (by decide) (by norm_num) hq4)
  obtain ⟨β, hβ, -, hβ2, hβo, hβfix⟩ :=
    exists_graphLift_of_closed_X hw hf e (by decide) (by decide) hX hsplit Φ₁ hE₁ hker₁
  obtain ⟨Ψ, hΨ⟩ := exists_unitary6_normal_form h β hβ2 hβo hβfix
  set Φ₂ := Φ₁.comp Ψ.toMonoidHom with hΦ₂
  have hE₂ : Φ₂.range = neighbourCore e .X := by
    rw [hΦ₂, MonoidHom.range_comp, MonoidHom.range_eq_top.2 Ψ.surjective,
      ← MonoidHom.range_eq_map, hE₁]
  have hker₂ := ker_comp_mulEquiv_le_center Φ₁ hker₁ Ψ
  have hc : ∀ g, t * Φ₂ g * t⁻¹ =
      Φ₂ (primeFormFieldSU h (isPrimeFormGram_graphGram6 F) h.barEquiv g) := by
    intro g
    change t * Φ₁ (Ψ g) * t⁻¹ = Φ₁ (Ψ (primeFormFieldSU h _ h.barEquiv g))
    rw [← hΨ, hβ]
  have hD : perfectCore (Φ₂.range ⊓ centralizer ({t} : Set G)) = neighbourLeviG e .X := by
    rw [hE₂, perfectCore_neighbourCore_inf_centralizer_X hw hf e, neighbourLeviG_eq_modelToG]
  have := fixedField_charP h
  have := fixedField_finite h
  have := finite_gramSU h ((graphGram6 F : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F)
  obtain ⟨ε⟩ := graphTorus_nonempty_ringEquiv h.card_fixedField hw.card_eq
  obtain ⟨Φ', hr, hk, hA, h2, h3⟩ := exists_exact_of_cover_model e ε (uEmbed6_injective h)
    (exists_mulAut_uEmbed6 h) (fixedSubgroup_barSU6 h) Φ₂ hker₂ hc hD
  exact ⟨F, inferInstance, h, Φ', hr.trans hE₂, hk, hA, h2, h3⟩

theorem exists_unitaryExact7_X {t : G} {f : ℕ} (hw : F4Work L K t f) (hf : 2 ≤ f)
    (e : L ≃* adjointGroup .F4 K) (hX : HR8Kind e t f .X .unitary7) :
    ∃ (F : Type) (_ : Field F) (h : UnitaryFieldData 2 f F) (Φ : uGroup7 h →* G),
      Φ.range = neighbourCore e .X ∧ Φ.ker ≤ center (uGroup7 h) ∧
      ((sp6TorusA (⊤ : Subgroup h.fixedFieldˣ)).map (uEmbed7 h)).map Φ =
        leviTorusG e {1, 2} ⊓ neighbourLeviG e .X ∧
      ((sp6TorusM2 (⊤ : Subgroup h.fixedFieldˣ)).map (uEmbed7 h)).map Φ =
        leviTorusG e {1} ⊓ neighbourLeviG e .X ∧
      ((sp6TorusM3 (⊤ : Subgroup h.fixedFieldˣ)).map (uEmbed7 h)).map Φ =
        leviTorusG e {2} ⊓ neighbourLeviG e .X := by
  have hq4 : 4 ≤ 2 ^ f :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨F, _, _, hF, Φ₀, hE₀, hker₀⟩ := exists_su7_cover_neighbourCore hw hf e (by decide) hX
  have : CharP F 2 := charP_two_of_natCard_eq_two_pow (f := 2 * f) (by
    rw [hF, ← pow_mul, mul_comm])
  have h : UnitaryFieldData 2 f F := unitaryFieldData_of_card (by omega) hF
  have eS : StatedSU 7 (2 ^ f) F = gramSU h ((1 : GL (Fin 7) F) : Matrix (Fin 7) (Fin 7) F) := by
    rw [Units.val_one]
    exact unitarySU_eq_gramSU h 7
  set eM := MulEquiv.subgroupCongr eS
  set Φ₁ := Φ₀.comp eM.symm.toMonoidHom with hΦ₁
  have hE₁ : Φ₁.range = neighbourCore e .X := by
    rw [hΦ₁, MonoidHom.range_comp, MonoidHom.range_eq_top.2 eM.symm.surjective,
      ← MonoidHom.range_eq_map, hE₀]
  have hker₁ := ker_comp_mulEquiv_le_center Φ₀ hker₀ eM.symm
  have := finite_gramSU h ((1 : GL (Fin 7) F) : Matrix (Fin 7) (Fin 7) F)
  have := CFSG.RankThree.Classical.isPerfect_gramSU_one h (n := 7) (by norm_num) (by omega)
  have hsplit := forall_exists_section_of_mulEquiv eM.symm
    (statedSU_odd_split hF (by omega) (by norm_num) (by decide) hq4)
  obtain ⟨β, hβ, -, hβ2, hβo, hβfix⟩ :=
    exists_graphLift_of_closed_X hw hf e (by decide) (by decide) hX hsplit Φ₁ hE₁ hker₁
  obtain ⟨Ψ, hΨ⟩ := exists_unitary7_normal_form h β hβ2 hβo hβfix
  set Φ₂ := Φ₁.comp Ψ.toMonoidHom with hΦ₂
  have hE₂ : Φ₂.range = neighbourCore e .X := by
    rw [hΦ₂, MonoidHom.range_comp, MonoidHom.range_eq_top.2 Ψ.surjective,
      ← MonoidHom.range_eq_map, hE₁]
  have hker₂ := ker_comp_mulEquiv_le_center Φ₁ hker₁ Ψ
  have hc : ∀ g, t * Φ₂ g * t⁻¹ =
      Φ₂ (primeFormFieldSU h (isPrimeFormGram_graphGram7 F) h.barEquiv g) := by
    intro g
    change t * Φ₁ (Ψ g) * t⁻¹ = Φ₁ (Ψ (primeFormFieldSU h _ h.barEquiv g))
    rw [← hΨ, hβ]
  have hD : perfectCore (Φ₂.range ⊓ centralizer ({t} : Set G)) = neighbourLeviG e .X := by
    rw [hE₂, perfectCore_neighbourCore_inf_centralizer_X hw hf e, neighbourLeviG_eq_modelToG]
  have := fixedField_charP h
  have := fixedField_finite h
  have := finite_gramSU h ((graphGram7 F : GL (Fin 7) F) : Matrix (Fin 7) (Fin 7) F)
  obtain ⟨ε⟩ := graphTorus_nonempty_ringEquiv h.card_fixedField hw.card_eq
  obtain ⟨Φ', hr, hk, hA, h2, h3⟩ := exists_exact_of_cover_model e ε (uEmbed7_injective h)
    (exists_mulAut_uEmbed7 h) (fixedSubgroup_barSU7 h) Φ₂ hker₂ hc hD
  exact ⟨F, inferInstance, h, Φ', hr.trans hE₂, hk, hA, h2, h3⟩

end MainX

section Main


theorem exact_Y_of_exact_X {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
    [CharP K CFSG.LieType.Ree.ReeTag.F4.prime] (e : L ≃* adjointGroup .F4 K) {M : Type} [Group M]
    {Φ : M →* G} {S₁₂ S₁ S₂ : Subgroup M}
    (hA : S₁₂.map Φ = leviTorusG (e.trans (graphAutF4 K).symm) {1, 2} ⊓
      neighbourLeviG (e.trans (graphAutF4 K).symm) .X)
    (h₂ : S₁.map Φ = leviTorusG (e.trans (graphAutF4 K).symm) {1} ⊓
      neighbourLeviG (e.trans (graphAutF4 K).symm) .X)
    (h₃ : S₂.map Φ = leviTorusG (e.trans (graphAutF4 K).symm) {2} ⊓
      neighbourLeviG (e.trans (graphAutF4 K).symm) .X) :
    S₁₂.map Φ = leviTorusG e {1, 2} ⊓ neighbourLeviG e .Y ∧
      S₁.map Φ = leviTorusG e (rankOneTori .Y).1 ⊓ neighbourLeviG e .Y ∧
      S₂.map Φ = leviTorusG e (rankOneTori .Y).2 ⊓ neighbourLeviG e .Y := by
  refine ⟨?_, ?_, ?_⟩
  · rw [hA, leviTorusG_trans_graphAutF4_symm, nodePermPow_one_one_two, ← neighbourLeviG_Y_eq_X]
  · rw [h₂, leviTorusG_trans_graphAutF4_symm, nodePermPow_one_one, ← neighbourLeviG_Y_eq_X]
    rfl
  · rw [h₃, leviTorusG_trans_graphAutF4_symm, nodePermPow_one_two, ← neighbourLeviG_Y_eq_X]
    rfl

theorem unitaryGraphTorusExactInput_holds : UnitaryGraphTorusExactInput := by
  intro G _ _ L K _ _ _ e t f hw hf N hN
  have : CharP K CFSG.LieType.Ree.ReeTag.F4.prime := charP_two_of_natCard_eq_two_pow hw.card_eq
  cases N with
  | X =>
    exact ⟨fun hk => exists_unitaryExact6_X hw hf e hk,
      fun hk => exists_unitaryExact7_X hw hf e hk⟩
  | Y =>
    refine ⟨fun hk => ?_, fun hk => ?_⟩
    · obtain ⟨F, _, h, Φ, hE, hker, hA, h₂, h₃⟩ :=
        exists_unitaryExact6_X hw hf _ ((hr8Kind_Y_iff_X e).1 hk)
      exact ⟨F, inferInstance, h, Φ, by rw [hE, neighbourCore_Y_eq_X], hker,
        exact_Y_of_exact_X e hA h₂ h₃⟩
    · obtain ⟨F, _, h, Φ, hE, hker, hA, h₂, h₃⟩ :=
        exists_unitaryExact7_X hw hf _ ((hr8Kind_Y_iff_X e).1 hk)
      exact ⟨F, inferInstance, h, Φ, by rw [hE, neighbourCore_Y_eq_X], hker,
        exact_Y_of_exact_X e hA h₂ h₃⟩
  | X' => exact absurd rfl hN

theorem unitaryOmegaPieceTablesInput_of_pieces (hP : UnitaryModelPiecesInput)
    (hO : OmegaPieceTablesInput) : UnitaryOmegaPieceTablesInput :=
  unitaryOmegaPieceTablesInput_of_inputs unitaryGraphTorusExactInput_holds hP hO

theorem graphPieceTablesInput_of_pieces_omega (hP : UnitaryModelPiecesInput)
    (hO : OmegaPieceTablesInput) : GraphPieceTablesInput :=
  graphPieceTablesInput_of_unitaryOmega (unitaryOmegaPieceTablesInput_of_pieces hP hO)

end Main

end CFSG.SeitzReduction.F4Pilot
