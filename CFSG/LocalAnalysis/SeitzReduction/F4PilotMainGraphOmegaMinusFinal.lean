module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaMinusField
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaPlusFinal

public section

namespace CFSG.SeitzReduction.F4Pilot

open CFSG Subgroup Matrix
open CFSG.Assembly.LowTwoRank
open CFSG.Blueprint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.Quasithin (perfectCore)

@[expose] def OmegaMinusPieceComputation : Prop :=
  ∀ (k : Type) [Field k] [Finite k] [CharP k 2], 4 ≤ Nat.card k → ∀ b c : k,
    (∀ s : k, s ^ 2 + b * s + c ≠ 0) →
    Nat.card (perfectCore (StatedOmega (StatedQuadMinus 4 k b c) ⊓
        centralizer (diagOmegaMinus k '' {t | t 1 = 1 ∧ t 2 = 1}))) = ordSU 4 (Nat.card k) ∧
      Nat.card (perfectCore (StatedOmega (StatedQuadMinus 4 k b c) ⊓
        centralizer (diagOmegaMinus k '' {t | t 2 = 1}))) = ordSL 2 (Nat.card k ^ 2) ∧
      Nat.card (perfectCore (StatedOmega (StatedQuadMinus 4 k b c) ⊓
        centralizer (diagOmegaMinus k '' {t | t 2 = t 1}))) = ordSL 2 (Nat.card k)

variable {k : Type} [Field k] [CharP k 2] [Finite k]

theorem coe_map_omegaMinusIota_torus {b c : k} {f : ℕ} (hK : Nat.card k = 2 ^ f) (hf : 2 ≤ f)
    (hirr : ∀ s : k, s ^ 2 + b * s + c ≠ 0) {A : Type*} [Group A] (p : A →* (Fin 3 → kˣ)) :
    (((((⊤ : Subgroup A).map ((sp6Diag k).comp p)).map (omegaMinusIota hK hf hirr)).map
        (StatedOmega (StatedQuadMinus 4 k b c)).subtype :
          Subgroup (GL (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) k)) :
            Set (GL (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) k)) =
      diagOmegaMinus k '' Set.range p := by
  ext X
  constructor
  · rintro ⟨_, ⟨_, ⟨a, -, rfl⟩, rfl⟩, rfl⟩
    exact ⟨_, ⟨a, rfl⟩, (coe_omegaMinusIota_sp6Diag hK hf hirr (p a)).symm⟩
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    exact ⟨_, ⟨_, ⟨a, Subgroup.mem_top a, rfl⟩, rfl⟩,
      coe_omegaMinusIota_sp6Diag hK hf hirr (p a)⟩

omit [CharP k 2] [Finite k] in
theorem range_sp6ParamA : Set.range (sp6ParamA k) = {t | t 1 = 1 ∧ t 2 = 1} := by
  ext t
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨by simp [sp6ParamA], by simp [sp6ParamA]⟩
  · rintro ⟨h1, h2⟩
    refine ⟨t 0, funext fun i => ?_⟩
    fin_cases i
    · simp [sp6ParamA]
    · simp [sp6ParamA, h1]
    · simp [sp6ParamA, h2]

omit [CharP k 2] [Finite k] in
theorem range_sp6ParamM2 : Set.range (sp6ParamM2 k) = {t | t 2 = 1} := by
  ext t
  constructor
  · rintro ⟨a, rfl⟩
    simp [sp6ParamM2]
  · intro h2
    refine ⟨(t 0, t 1), funext fun i => ?_⟩
    fin_cases i
    · simp [sp6ParamM2]
    · simp [sp6ParamM2]
    · simp [sp6ParamM2, show t 2 = 1 from h2]

omit [CharP k 2] [Finite k] in
theorem range_sp6ParamM3 : Set.range (sp6ParamM3 k) = {t | t 2 = t 1} := by
  ext t
  constructor
  · rintro ⟨a, rfl⟩
    simp [sp6ParamM3]
  · intro h2
    refine ⟨(t 0, t 1), funext fun i => ?_⟩
    fin_cases i
    · simp [sp6ParamM3]
    · simp [sp6ParamM3]
    · simp [sp6ParamM3, show t 2 = t 1 from h2]

theorem pieceCards_omegaMinus8_model (hP : OmegaMinusPieceComputation) {b c : k} {f : ℕ}
    (hK : Nat.card k = 2 ^ f) (hf : 2 ≤ f) (hirr : ∀ s : k, s ^ 2 + b * s + c ≠ 0)
    (G : Type) [Group G] [Finite G] (Φ : StatedOmega (StatedQuadMinus 4 k b c) →* G)
    (hΦ : Φ.ker ≤ center (StatedOmega (StatedQuadMinus 4 k b c))) :
    pieceCards Φ.range (((sp6TorusA (⊤ : Subgroup kˣ)).map (omegaMinusIota hK hf hirr)).map Φ)
      (((sp6TorusM2 (⊤ : Subgroup kˣ)).map (omegaMinusIota hK hf hirr)).map Φ)
      (((sp6TorusM3 (⊤ : Subgroup kˣ)).map (omegaMinusIota hK hf hirr)).map Φ) =
        pieceOrders .omegaMinus8 (2 ^ f) := by
  have hk4 : 4 ≤ Nat.card k := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hinj : Function.Injective Φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hΦ.trans (center_omegaMinus8 k hirr).le
  set Φ' : StatedOmega (StatedQuadMinus 4 k b c) ≃* Φ.range := MonoidHom.ofInjective hinj
  have hΦ' : Φ.range.subtype.comp Φ'.toMonoidHom = Φ := by
    ext x
    rfl
  rw [pieceCards_eq_of_mulEquiv Φ' (by rw [hΦ']) (by rw [hΦ']) (by rw [hΦ']), pieceCards_top]
  obtain ⟨hA', h2', h3'⟩ := hP k hk4 b c hirr
  have hA := card_perfectCore_centralizer_eq_of_coe
    (coe_map_omegaMinusIota_torus hK hf hirr (sp6ParamA k))
  have h2 := card_perfectCore_centralizer_eq_of_coe
    (coe_map_omegaMinusIota_torus hK hf hirr (sp6ParamM2 k))
  have h3 := card_perfectCore_centralizer_eq_of_coe
    (coe_map_omegaMinusIota_torus hK hf hirr (sp6ParamM3 k))
  rw [range_sp6ParamA, hA'] at hA
  rw [range_sp6ParamM2, h2'] at h2
  rw [range_sp6ParamM3, h3'] at h3
  rw [sp6TorusA, sp6TorusM2, sp6TorusM3, Subgroup.top_prod_top, hA, h2, h3, hK]
  rfl

omit [CharP k 2] [Finite k] in
theorem graphKindModelInput_omegaMinus8_of_pieces
    (hP : OmegaMinusPieceComputation) : GraphKindModelInput .omegaMinus8 := by
  intro f hf k _ _ hK
  have : CharP k 2 := charP_two_of_natCard_eq_two_pow hK
  have hk4 : 4 ≤ Nat.card k := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨c, hc⟩ := exists_minus_coefficient (k := k)
  refine ⟨StatedOmega (StatedQuadMinus 4 k 1 c), inferInstance, inferInstance,
    isPerfect_omegaMinus8 k hc, omegaMinusIota hK hf hc, omegaMinusBetaC k 1 c, ?_, ?_,
    omegaMinusIota_injective hK hf hc, (range_omegaMinusIota hK hf hc).symm, ?_, ?_, ?_⟩
  · intro E' _ _ π' hπ' hcen
    exact omegaMinus8_exists_section k hk4 hc E' π' hπ' hcen
  · intro S _ hS
    exact omegaMinus8_covers k hK hc S hS
  · intro ρ
    obtain ⟨s, hs⟩ := exists_sq_add_eq_ringEquiv hc ρ
    exact ⟨omegaMinusFieldAut k c ρ s hs, omegaMinusFieldAut_iota hc hK hf ρ s hs⟩
  · intro β hβ2 hβo f' hfix
    exact exists_conj_omegaMinusBetaC k (by omega) hK hc β hβ2 hβo hfix
  · intro G _ _ Φ hΦ
    exact pieceCards_omegaMinus8_model hP hK hf hc G Φ hΦ

end CFSG.SeitzReduction.F4Pilot
