module

public import CFSG.LocalAnalysis.ComponentInitial.BinarySymmetricThreeLinear
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBXSp6TensorModel

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.ComponentInitial.ChevTwoFactor

open Matrix Subgroup CFSG.ProperTwoGeneratedCore.PairedTensor
open CFSG.ProperTwoGeneratedCore.BinaryThreeSpace (Mat3 unitri unitriGL)
open CFSG.LocalAnalysis.ComponentInitial.SteinbergBX.TensorModel

abbrev Sym3 : Type := ↥(binarySymMatrices 3)

theorem sym_symm (B : Sym3) (i j : Fin 3) : (B : Mat3) j i = (B : Mat3) i j := by
  have h : (B : Mat3)ᵀ = B := B.2
  rw [← h, transpose_apply, h]

theorem coe_sym_eta (B : Sym3) :
    (B : Mat3) = !![(B : Mat3) 0 0, (B : Mat3) 0 1, (B : Mat3) 0 2;
      (B : Mat3) 0 1, (B : Mat3) 1 1, (B : Mat3) 1 2;
      (B : Mat3) 0 2, (B : Mat3) 1 2, (B : Mat3) 2 2] := by
  conv_lhs => rw [Matrix.eta_fin_three (B : Mat3)]
  rw [sym_symm B 0 1, sym_symm B 0 2, sym_symm B 1 2]

theorem sym_ext {B B' : Sym3} (h00 : (B : Mat3) 0 0 = (B' : Mat3) 0 0)
    (h01 : (B : Mat3) 0 1 = (B' : Mat3) 0 1) (h02 : (B : Mat3) 0 2 = (B' : Mat3) 0 2)
    (h11 : (B : Mat3) 1 1 = (B' : Mat3) 1 1) (h12 : (B : Mat3) 1 2 = (B' : Mat3) 1 2)
    (h22 : (B : Mat3) 2 2 = (B' : Mat3) 2 2) : B = B' := by
  apply Subtype.ext
  rw [coe_sym_eta B, coe_sym_eta B', h00, h01, h02, h11, h12, h22]

@[expose] def tLow : S := invS !![1, 0, 0; 0, 1, 0; 0, 1, 1] (by decide)

theorem coe_tLow : ((tLow : S) : Mat3) = !![1, 0, 0; 0, 1, 0; 0, 1, 1] := rfl

set_option maxRecDepth 100000 in
theorem fixed_stab_check : ∀ a b c d e f : ZMod 2,
    unitri 1 0 0 * !![a, d, e; d, b, f; e, f, c] * (unitri 1 0 0)ᵀ = !![a, d, e; d, b, f; e, f, c] →
    unitri 0 1 0 * !![a, d, e; d, b, f; e, f, c] * (unitri 0 1 0)ᵀ = !![a, d, e; d, b, f; e, f, c] →
    unitri 0 0 1 * !![a, d, e; d, b, f; e, f, c] * (unitri 0 0 1)ᵀ = !![a, d, e; d, b, f; e, f, c] →
    !![(1 : ZMod 2), 0, 0; 0, 1, 0; 0, 1, 1] * !![a, d, e; d, b, f; e, f, c] *
        (!![(1 : ZMod 2), 0, 0; 0, 1, 0; 0, 1, 1])ᵀ = !![a, d, e; d, b, f; e, f, c] →
    b = 0 ∧ c = 0 ∧ d = 0 ∧ e = 0 ∧ f = 0 := by
  decide +kernel

abbrev E11 : Sym3 := symThreeRankOne ![1, 0, 0]

theorem coe_E11 : (E11 : Mat3) = !![1, 0, 0; 0, 0, 0; 0, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem eq_zero_or_eq_E11 {B : Sym3} (h1 : symThreeCongr (unitriGL 1 0 0) B = B)
    (h2 : symThreeCongr (unitriGL 0 1 0) B = B) (h3 : symThreeCongr (unitriGL 0 0 1) B = B)
    (h4 : symThreeCongr tLow B = B) : B = 0 ∨ B = E11 := by
  have e1 := congrArg Subtype.val h1
  have e2 := congrArg Subtype.val h2
  have e3 := congrArg Subtype.val h3
  have e4 := congrArg Subtype.val h4
  rw [coe_symThreeCongr] at e1 e2 e3 e4
  rw [coe_sym_eta B] at e1 e2 e3 e4
  obtain ⟨hb, hc, hd, he, hf⟩ := fixed_stab_check _ _ _ _ _ _ e1 e2 e3 e4
  rcases (show ∀ x : ZMod 2, x = 0 ∨ x = 1 by decide) ((B : Mat3) 0 0) with ha | ha
  · left
    apply sym_ext <;> simp [ha, hb, hc, hd, he, hf]
  · right
    apply sym_ext <;> simp [coe_E11, ha, hb, hc, hd, he, hf]

theorem unitriGL_mulVec_e1 (a b c : ZMod 2) :
    ((unitriGL a b c : S) : Mat3) *ᵥ ![1, 0, 0] = ![1, 0, 0] := by
  revert a b c
  decide

theorem eq_refl_of_commute (F : Sym3 ≃ₗ[ZMod 2] Sym3)
    (hF : ∀ (g : S) (B : Sym3), F (symThreeCongr g B) = symThreeCongr g (F B)) :
    F = LinearEquiv.refl (ZMod 2) Sym3 := by
  have hfix : ∀ g : S, ((g : S) : Mat3) *ᵥ ![1, 0, 0] = ![1, 0, 0] →
      symThreeCongr g (F E11) = F E11 := fun g hg => by
    rw [← hF, symThreeCongr_rankOne, hg]
  have hE : F E11 = E11 := by
    rcases eq_zero_or_eq_E11 (hfix _ (unitriGL_mulVec_e1 1 0 0))
        (hfix _ (unitriGL_mulVec_e1 0 1 0)) (hfix _ (unitriGL_mulVec_e1 0 0 1))
        (hfix _ (by rw [coe_tLow]; decide)) with h | h
    · exfalso
      have h0 : E11 = 0 := F.injective (by rw [h, map_zero])
      have := congrArg (fun B : Sym3 => (B : Mat3) 0 0) h0
      exact absurd this (by decide)
    · exact h
  refine eq_of_eq_on_symThreeType_one fun B hB => ?_
  obtain ⟨D, rfl⟩ := exists_symThreeCongr_of_type_eq
    (symThreeType_diag_units.1.trans hB.symm)
  rw [hF, hE]
  rfl

abbrev FixS (g : S) : Type := {B : Sym3 // symThreeCongr g B = B}

theorem card_le_of_recon' {P : Sym3 → Prop} {n : ℕ} (f : Sym3 → Fin n → ZMod 2)
    (Φ : (Fin n → ZMod 2) → Mat3) (h : ∀ B : Sym3, P B → (B : Mat3) = Φ (f B)) :
    Nat.card {B // P B} ≤ 2 ^ n := by
  calc Nat.card {B // P B} ≤ Nat.card (Fin n → ZMod 2) :=
        Nat.card_le_card_of_injective (fun B => f B.1) fun B B' hBB' =>
          Subtype.ext (Subtype.ext ((h B.1 B.2).trans ((congrArg Φ hBB').trans
            (h B'.1 B'.2).symm)))
    _ = 2 ^ n := by simp [Nat.card_eq_fintype_card, ZMod.card]

set_option maxRecDepth 100000 in
theorem fix_tS_check : ∀ a b c d e f : ZMod 2,
    unitri 0 1 0 * !![a, d, e; d, b, f; e, f, c] * (unitri 0 1 0)ᵀ = !![a, d, e; d, b, f; e, f, c] →
    c = 0 ∧ f = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem fix_tS_check' : ∀ a b d e : ZMod 2,
    unitri 0 1 0 * !![a, d, e; d, b, 0; e, 0, 0] * (unitri 0 1 0)ᵀ =
      !![a, d, e; d, b, 0; e, 0, 0] := by
  decide +kernel

theorem card_fixS_tS : Nat.card (FixS tS) = 16 := by
  have e : FixS tS ≃ (Fin 4 → ZMod 2) :=
    { toFun := fun B => ![(B.1 : Mat3) 0 0, (B.1 : Mat3) 0 1, (B.1 : Mat3) 0 2, (B.1 : Mat3) 1 1]
      invFun := fun v => ⟨⟨!![v 0, v 1, v 2; v 1, v 3, 0; v 2, 0, 0], by
          rw [mem_binarySymMatrices]
          ext i j
          fin_cases i <;> fin_cases j <;> rfl⟩, Subtype.ext (by
          rw [coe_symThreeCongr, coe_tS]
          exact fix_tS_check' _ _ _ _)⟩
      left_inv := fun B => by
        have hB := congrArg Subtype.val B.2
        rw [coe_symThreeCongr, coe_tS, coe_sym_eta B.1] at hB
        obtain ⟨hc, hf⟩ := fix_tS_check _ _ _ _ _ _ hB
        apply Subtype.ext
        apply sym_ext <;> simp [hc, hf]
      right_inv := fun v => by
        funext i
        fin_cases i <;> rfl }
  rw [Nat.card_congr e]
  simp [Nat.card_eq_fintype_card, ZMod.card]

theorem card_fixS_conj (h g : S) : Nat.card (FixS (h * g * h⁻¹)) = Nat.card (FixS g) := by
  refine Nat.card_congr
    { toFun := fun B => ⟨symThreeCongr h⁻¹ B.1, ?_⟩
      invFun := fun B => ⟨symThreeCongr h B.1, ?_⟩
      left_inv := fun B => Subtype.ext (by
        change symThreeCongr h (symThreeCongr h⁻¹ B.1) = B.1
        rw [← symThreeCongr_mul, mul_inv_cancel, symThreeCongr_one])
      right_inv := fun B => Subtype.ext (by
        change symThreeCongr h⁻¹ (symThreeCongr h B.1) = B.1
        rw [← symThreeCongr_mul, inv_mul_cancel, symThreeCongr_one]) }
  · have hB := B.2
    rw [symThreeCongr_mul, symThreeCongr_mul] at hB
    calc symThreeCongr g (symThreeCongr h⁻¹ B.1) =
        symThreeCongr h⁻¹ (symThreeCongr h (symThreeCongr g (symThreeCongr h⁻¹ B.1))) := by
          rw [← symThreeCongr_mul h⁻¹ h, inv_mul_cancel, symThreeCongr_one]
      _ = symThreeCongr h⁻¹ B.1 := by rw [hB]
  · have hB := B.2
    rw [symThreeCongr_mul, symThreeCongr_mul, ← symThreeCongr_mul h⁻¹, inv_mul_cancel,
      symThreeCongr_one, hB]

theorem card_fixS_one : Nat.card (FixS 1) = 64 := by
  rw [Nat.card_congr (Equiv.subtypeUnivEquiv fun B : Sym3 => symThreeCongr_one B)]
  exact card_symThree

theorem card_fixS_of_involution {g : S} (hg : g * g = 1) (hg1 : g ≠ 1) :
    Nat.card (FixS g) = 16 := by
  obtain ⟨h, hh⟩ := exists_conj_eq_tS hg hg1
  rw [← card_fixS_conj h g, hh, card_fixS_tS]

theorem sixteen_le_card_fixS {g : S} (hg : g * g = 1) : 16 ≤ Nat.card (FixS g) := by
  by_cases hg1 : g = 1
  · subst hg1
    rw [card_fixS_one]
    norm_num
  · rw [card_fixS_of_involution hg hg1]

theorem card_fixS_le_of_ne_one {g : S} (hg : g * g = 1) (hg1 : g ≠ 1) :
    Nat.card (FixS g) ≤ 16 :=
  (card_fixS_of_involution hg hg1).le

set_option maxRecDepth 100000 in
theorem fix_pair_check₁ : ∀ x : ZMod 2, ∀ a b c d e f : ZMod 2,
    unitri 0 1 0 * !![a, d, e; d, b, f; e, f, c] * (unitri 0 1 0)ᵀ = !![a, d, e; d, b, f; e, f, c] →
    unitri 1 x 0 * !![a, d, e; d, b, f; e, f, c] * (unitri 1 x 0)ᵀ = !![a, d, e; d, b, f; e, f, c] →
    b = 0 ∧ c = 0 ∧ f = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem fix_pair_check₂ : ∀ x : ZMod 2, ∀ a b c d e f : ZMod 2,
    unitri 0 1 0 * !![a, d, e; d, b, f; e, f, c] * (unitri 0 1 0)ᵀ = !![a, d, e; d, b, f; e, f, c] →
    unitri 0 x 1 * !![a, d, e; d, b, f; e, f, c] * (unitri 0 x 1)ᵀ = !![a, d, e; d, b, f; e, f, c] →
    c = 0 ∧ e = 0 ∧ f = 0 := by
  decide +kernel

theorem card_fixS₂_conj (h x y : S) :
    Nat.card {B : Sym3 // symThreeCongr (h * x * h⁻¹) B = B ∧ symThreeCongr (h * y * h⁻¹) B = B} =
      Nat.card {B : Sym3 // symThreeCongr x B = B ∧ symThreeCongr y B = B} := by
  have key : ∀ (g : S) (B : Sym3), symThreeCongr (h * g * h⁻¹) B = B ↔
      symThreeCongr g (symThreeCongr h⁻¹ B) = symThreeCongr h⁻¹ B := fun g B => by
    rw [symThreeCongr_mul, symThreeCongr_mul]
    constructor
    · intro hB
      calc symThreeCongr g (symThreeCongr h⁻¹ B) =
          symThreeCongr h⁻¹ (symThreeCongr h (symThreeCongr g (symThreeCongr h⁻¹ B))) := by
            rw [← symThreeCongr_mul h⁻¹ h, inv_mul_cancel, symThreeCongr_one]
        _ = symThreeCongr h⁻¹ B := by rw [hB]
    · intro hB
      rw [hB, ← symThreeCongr_mul, mul_inv_cancel, symThreeCongr_one]
  refine Nat.card_congr
    { toFun := fun B => ⟨symThreeCongr h⁻¹ B.1, (key x B.1).1 B.2.1, (key y B.1).1 B.2.2⟩
      invFun := fun B => ⟨symThreeCongr h B.1, ?_, ?_⟩
      left_inv := fun B => Subtype.ext (by
        change symThreeCongr h (symThreeCongr h⁻¹ B.1) = B.1
        rw [← symThreeCongr_mul, mul_inv_cancel, symThreeCongr_one])
      right_inv := fun B => Subtype.ext (by
        change symThreeCongr h⁻¹ (symThreeCongr h B.1) = B.1
        rw [← symThreeCongr_mul, inv_mul_cancel, symThreeCongr_one]) }
  · rw [key, ← symThreeCongr_mul h⁻¹ h, inv_mul_cancel, symThreeCongr_one]
    exact B.2.1
  · rw [key, ← symThreeCongr_mul h⁻¹ h, inv_mul_cancel, symThreeCongr_one]
    exact B.2.2

theorem card_fixS_pair_le {x y : S} (hx : x * x = 1) (hy : y * y = 1) (hx1 : x ≠ 1)
    (hy1 : y ≠ 1) (hxy : x ≠ y) (hc : x * y = y * x) :
    Nat.card {B : Sym3 // symThreeCongr x B = B ∧ symThreeCongr y B = B} ≤ 8 := by
  obtain ⟨h, hh⟩ := exists_conj_eq_tS hx hx1
  rw [← card_fixS₂_conj h x y, hh]
  set y' := h * y * h⁻¹ with hy'
  have hcomm : y' * tS = tS * y' := by
    rw [← hh, hy']
    calc h * y * h⁻¹ * (h * x * h⁻¹) = h * (y * x) * h⁻¹ := by group
      _ = h * (x * y) * h⁻¹ := by rw [hc]
      _ = h * x * h⁻¹ * (h * y * h⁻¹) := by group
  obtain ⟨a, b, c, habc⟩ := (commute_tS_iff y').1 hcomm
  have hy'2 : y' * y' = 1 := by
    rw [hy', show h * y * h⁻¹ * (h * y * h⁻¹) = h * (y * y) * h⁻¹ by group, hy]
    group
  have hy'1 : y' ≠ 1 := fun h1 => hy1 (by
    rw [show y = h⁻¹ * y' * h by rw [hy']; group, h1]; group)
  have hy't : y' ≠ tS := fun h1 => hxy (by
    rw [show x = h⁻¹ * tS * h by rw [← hh]; group, show y = h⁻¹ * y' * h by rw [hy']; group,
      h1])
  rw [habc] at hy'2 hy'1 hy't ⊢
  have hu2 : unitri a b c * unitri a b c = 1 := congrArg Units.val hy'2
  have hu1 : unitri a b c ≠ 1 := fun h1 => hy'1 (Units.ext h1)
  have hut : unitri a b c ≠ unitri 0 1 0 := fun h1 => hy't (Units.ext h1)
  have hfix : ∀ B : Sym3, symThreeCongr tS B = B → symThreeCongr (unitriGL a b c) B = B →
      unitri 0 1 0 * !![(B : Mat3) 0 0, (B : Mat3) 0 1, (B : Mat3) 0 2;
          (B : Mat3) 0 1, (B : Mat3) 1 1, (B : Mat3) 1 2;
          (B : Mat3) 0 2, (B : Mat3) 1 2, (B : Mat3) 2 2] * (unitri 0 1 0)ᵀ =
        !![(B : Mat3) 0 0, (B : Mat3) 0 1, (B : Mat3) 0 2;
          (B : Mat3) 0 1, (B : Mat3) 1 1, (B : Mat3) 1 2;
          (B : Mat3) 0 2, (B : Mat3) 1 2, (B : Mat3) 2 2] ∧
      unitri a b c * !![(B : Mat3) 0 0, (B : Mat3) 0 1, (B : Mat3) 0 2;
          (B : Mat3) 0 1, (B : Mat3) 1 1, (B : Mat3) 1 2;
          (B : Mat3) 0 2, (B : Mat3) 1 2, (B : Mat3) 2 2] * (unitri a b c)ᵀ =
        !![(B : Mat3) 0 0, (B : Mat3) 0 1, (B : Mat3) 0 2;
          (B : Mat3) 0 1, (B : Mat3) 1 1, (B : Mat3) 1 2;
          (B : Mat3) 0 2, (B : Mat3) 1 2, (B : Mat3) 2 2] := fun B h1 h2 => by
    have e1 := congrArg Subtype.val h1
    have e2 := congrArg Subtype.val h2
    rw [coe_symThreeCongr, coe_tS] at e1
    rw [coe_symThreeCongr] at e2
    rw [← coe_sym_eta B]
    exact ⟨e1, e2⟩
  fin_cases a <;> fin_cases c
  ·
    fin_cases b
    · exact absurd (by decide) hu1
    · exact absurd (by decide) hut
  ·
    refine le_of_le_of_eq (card_le_of_recon' (n := 3) (fun B => ![(B : Mat3) 0 0, (B : Mat3) 0 1,
      (B : Mat3) 1 1]) (fun v => !![v 0, v 1, 0; v 1, v 2, 0; 0, 0, 0]) fun B hB => ?_)
      (by norm_num)
    obtain ⟨e1, e2⟩ := hfix B hB.1 hB.2
    obtain ⟨hc', he, hf⟩ := fix_pair_check₂ _ _ _ _ _ _ _ e1 e2
    rw [coe_sym_eta B, hc', he, hf]
    rfl
  ·
    refine le_of_le_of_eq (card_le_of_recon' (n := 3) (fun B => ![(B : Mat3) 0 0, (B : Mat3) 0 1,
      (B : Mat3) 0 2]) (fun v => !![v 0, v 1, v 2; v 1, 0, 0; v 2, 0, 0]) fun B hB => ?_)
      (by norm_num)
    obtain ⟨e1, e2⟩ := hfix B hB.1 hB.2
    obtain ⟨hb, hc', hf⟩ := fix_pair_check₁ _ _ _ _ _ _ _ e1 e2
    rw [coe_sym_eta B, hb, hc', hf]
    rfl
  ·
    exfalso
    revert hu2
    fin_cases b <;> decide

@[expose] def tLow₁ : S := invS !![1, 0, 0; 1, 1, 0; 0, 0, 1] (by decide)

theorem coe_tLow₁ : ((tLow₁ : S) : Mat3) = !![1, 0, 0; 1, 1, 0; 0, 0, 1] := rfl

theorem congr_tLow₁_E11 :
    ((symThreeCongr tLow₁ E11 : Sym3) : Mat3) = !![1, 1, 0; 1, 1, 0; 0, 0, 0] := by
  rw [coe_symThreeCongr, coe_tLow₁, coe_E11]
  decide

theorem eq_zero_of_forall_fixed {B : Sym3} (h : ∀ g : S, symThreeCongr g B = B) : B = 0 := by
  rcases eq_zero_or_eq_E11 (h _) (h _) (h _) (h _) with h0 | hE
  · exact h0
  · exfalso
    have h1 := congrArg (fun B : Sym3 => (B : Mat3) 0 1) (h tLow₁)
    simp only [hE, congr_tLow₁_E11, coe_E11] at h1
    exact absurd h1 (by decide)

theorem symThreeDiag_congr_sub_ne_zero :
    symThreeDiag ((symThreeCongr tLow₁ E11 - E11 : Sym3) : Mat3) ≠ 0 := by
  intro h
  have h1 := congrFun h 1
  rw [AddSubgroup.coe_sub, congr_tLow₁_E11, coe_E11] at h1
  exact absurd h1 (by decide)

theorem eq_top_of_invariant_of_comm (U : AddSubgroup Sym3)
    (hU : ∀ (g : S), ∀ B ∈ U, symThreeCongr g B ∈ U)
    (hcomm : ∀ (g : S) (B : Sym3), symThreeCongr g B - B ∈ U) : U = ⊤ := by
  rcases invariant_addSubgroup U hU with h | h | h
  · exfalso
    have h1 := hcomm tLow₁ E11
    rw [h, AddSubgroup.mem_bot] at h1
    apply symThreeDiag_congr_sub_ne_zero
    rw [h1]
    rfl
  · exfalso
    exact symThreeDiag_congr_sub_ne_zero ((h _).1 (hcomm tLow₁ E11))
  · exact h

theorem card_of_invariant (U : AddSubgroup Sym3) (hU : ∀ (g : S), ∀ B ∈ U, symThreeCongr g B ∈ U) :
    Nat.card U = 1 ∨ Nat.card U = 8 ∨ Nat.card U = 64 := by
  rcases invariant_addSubgroup U hU with h | h | h
  · left
    rw [h, AddSubgroup.card_bot]
  · right; left
    have e : U ≃ (Fin 3 → ZMod 2) :=
      { toFun := fun B => ![(B.1 : Mat3) 0 1, (B.1 : Mat3) 0 2, (B.1 : Mat3) 1 2]
        invFun := fun v => ⟨⟨!![0, v 0, v 1; v 0, 0, v 2; v 1, v 2, 0], by
            rw [mem_binarySymMatrices]
            ext i j
            fin_cases i <;> fin_cases j <;> rfl⟩, (h _).2 (by
            funext i
            fin_cases i <;> rfl)⟩
        left_inv := fun B => by
          have hB := (h B.1).1 B.2
          have h0 := congrFun hB 0
          have h1 := congrFun hB 1
          have h2 := congrFun hB 2
          simp only [symThreeDiag, Pi.zero_apply] at h0 h1 h2
          apply Subtype.ext
          apply sym_ext <;> simp [h0, h1, h2]
        right_inv := fun v => by
          funext i
          fin_cases i <;> rfl }
    rw [Nat.card_congr e]
    simp [Nat.card_eq_fintype_card, ZMod.card]
  · right; right
    rw [h, AddSubgroup.card_top]
    exact card_symThree

end CFSG.LocalAnalysis.ComponentInitial.ChevTwoFactor
