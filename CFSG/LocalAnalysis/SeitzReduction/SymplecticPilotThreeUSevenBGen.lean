module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindCTUnitaryModel
public import CFSG.LieType.Steinberg.CentralExt.UnitaryRankOneLast
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotOrthSL2
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_involutive)
open CFSG.LieType.Steinberg (sl2Upper sl2Lower)
open CFSG.SeitzReduction.LinearPilot (diagUnit)
open scoped MatrixGroups

section Heis

variable {F : Type} [Field F] {σ : F ≃+* F}

theorem ug3_heis_mul_inv (a b : F) :
    heisenbergMatrix σ (0 : Fin 3) 1 a b * heisenbergMatrix σ 0 1 (-a) (-b - a * σ a) = 1 := by
  rw [heisenbergMatrix_mul σ (by decide) (by decide) (by decide), map_neg]
  rw [show a + -a = 0 by ring, show b + (-b - a * σ a) - a * -σ a = 0 by ring,
    heisenbergMatrix_zero]

theorem ug3_heis_inv_mul (a b : F) :
    heisenbergMatrix σ (0 : Fin 3) 1 (-a) (-b - a * σ a) * heisenbergMatrix σ 0 1 a b = 1 := by
  rw [heisenbergMatrix_mul σ (by decide) (by decide) (by decide)]
  rw [show -a + a = 0 by ring, show -b - a * σ a + b - -a * σ a = 0 by ring,
    heisenbergMatrix_zero]

variable (hσ : ∀ c, σ (σ c) = c)

@[expose] noncomputable def ug3Heis {a b : F} (h : b + σ b + σ a * a = 0) : SU σ 3 :=
  ⟨⟨heisenbergMatrix σ (0 : Fin 3) 1 a b, heisenbergMatrix σ 0 1 (-a) (-b - a * σ a),
      ug3_heis_mul_inv a b, ug3_heis_inv_mul a b⟩,
    det_heisenbergMatrix σ (by decide) (by decide) (by decide) a b,
    heisenbergMatrix_isometry σ hσ (by decide) (by decide) (by decide) h⟩

theorem coe_ug3Heis {a b : F} (h : b + σ b + σ a * a = 0) :
    ((ug3Heis hσ h : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      heisenbergMatrix σ (0 : Fin 3) 1 a b := rfl

theorem coe_ug3Heis_three {a b : F} (h : b + σ b + σ a * a = 0) :
    ((ug3Heis hσ h : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = !![1, a, b; 0, 1, -σ a; 0, 0, 1] :=
  CFSG.LieType.Steinberg.heisenbergMatrix_three a b

theorem ug3Heis_congr {a b a' b' : F} (h : b + σ b + σ a * a = 0)
    (h' : b' + σ b' + σ a' * a' = 0) (ha : a = a') (hb : b = b') : ug3Heis hσ h = ug3Heis hσ h' := by
  subst ha hb
  rfl

include hσ in
theorem ug3_valid_mul {a b a' b' : F} (h : b + σ b + σ a * a = 0)
    (h' : b' + σ b' + σ a' * a' = 0) :
    (b + b' - a * σ a') + σ (b + b' - a * σ a') + σ (a + a') * (a + a') = 0 := by
  rw [map_sub, map_add, map_add, map_mul, hσ]
  calc b + b' - a * σ a' + (σ b + σ b' - σ a * a') + (σ a + σ a') * (a + a')
      = (b + σ b + σ a * a) + (b' + σ b' + σ a' * a') := by ring
    _ = 0 := by rw [h, h', add_zero]

theorem ug3Heis_mul {a b a' b' : F} (h : b + σ b + σ a * a = 0)
    (h' : b' + σ b' + σ a' * a' = 0) :
    ug3Heis hσ h * ug3Heis hσ h' = ug3Heis hσ (ug3_valid_mul hσ h h') :=
  Subtype.ext (Units.ext (heisenbergMatrix_mul σ (by decide) (by decide) (by decide) a b a' b'))

include hσ in
theorem ug3_valid_inv {a b : F} (h : b + σ b + σ a * a = 0) :
    (-b - a * σ a) + σ (-b - a * σ a) + σ (-a) * (-a) = 0 := by
  rw [map_sub, map_neg, map_neg, map_mul, hσ]
  calc -b - a * σ a + (-σ b - σ a * a) + -σ a * -a = -(b + σ b + σ a * a) := by ring
    _ = 0 := by rw [h, neg_zero]

theorem ug3Heis_inv {a b : F} (h : b + σ b + σ a * a = 0) :
    (ug3Heis hσ h)⁻¹ = ug3Heis hσ (ug3_valid_inv hσ h) :=
  Subtype.ext (Units.ext rfl)

theorem ug3Heis_zero (h : (0 : F) + σ 0 + σ 0 * 0 = 0) : ug3Heis hσ h = 1 :=
  Subtype.ext (Units.ext (heisenbergMatrix_zero σ _ _))

theorem ug3Heis_mem_rootGroup {a b : F} (h : b + σ b + σ a * a = 0) :
    ug3Heis hσ h ∈ rootGroup σ hσ 3 (Pi.single 0 1) := by
  rw [CFSG.LieType.Steinberg.rootGroup_three_eq_heisenbergSubgroup hσ]
  exact ⟨a, b, h, rfl⟩

theorem exists_ug3Heis_of_mem_rootGroup {x : SU σ 3} (hx : x ∈ rootGroup σ hσ 3 (Pi.single 0 1)) :
    ∃ (a b : F) (h : b + σ b + σ a * a = 0), x = ug3Heis hσ h := by
  rw [CFSG.LieType.Steinberg.rootGroup_three_eq_heisenbergSubgroup hσ] at hx
  obtain ⟨a, b, h, hx⟩ := hx
  exact ⟨a, b, h, Subtype.ext (Units.ext hx)⟩

end Heis

section Sl

variable {K F : Type} [Field K] [Field F] [CharP K 2] {σ : F ≃+* F}

theorem ug3_coord0 : (ctuCoord 1 1 (Sum.inl (Sum.inl 0)) : Fin (2 * 1 + 1)) = 0 := Fin.ext rfl

theorem ug3_coord1 : (ctuCoord 1 1 (Sum.inr 0) : Fin (2 * 1 + 1)) = 1 := Fin.ext rfl

theorem ug3_coord2 : (ctuCoord 1 1 (Sum.inl (Sum.inr 0)) : Fin (2 * 1 + 1)) = 2 := Fin.ext rfl

variable (σ) (ι : K →+* F) (hι : ∀ c, σ (ι c) = ι c)

@[expose] noncomputable def ug3Sl : SL(2, K) →* SU σ 3 :=
  (ctuEmbed 1 le_rfl σ ι hι).comp (longBlock K 1 0)

theorem ug3Sl_apply (A : SL(2, K)) : ug3Sl σ ι hι A = ctuEmbed 1 le_rfl σ ι hι (longBlock K 1 0 A) :=
  rfl

theorem coe_ug3Sl (A : SL(2, K)) :
    ((ug3Sl σ ι hι A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      !![ι (A 0 0), 0, ι (A 0 1); 0, 1, 0; ι (A 1 0), 0, ι (A 1 1)] := by
  change (((ctuEmbed 1 le_rfl σ ι hι (longBlock K 1 0 A) : SU σ (2 * 1 + 1)) :
    GL (Fin (2 * 1 + 1)) F) : Matrix (Fin (2 * 1 + 1)) (Fin (2 * 1 + 1)) F) = _
  ext a b
  obtain ⟨w, rfl⟩ := (ctuCoord 1 1).surjective a
  obtain ⟨w', rfl⟩ := (ctuCoord 1 1).surjective b
  rw [ctuEmbed_apply_ctuCoord, mat_longBlock]
  rcases w with (p | p) | i <;> rcases w' with (p' | p') | i' <;>
    simp only [Fin.fin_one_eq_zero, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
      fromBlocks_apply₂₂, map_apply, ug3_coord0, ug3_coord1, ug3_coord2,
      CFSG.LieType.Steinberg.Sp.blockMat, of_apply] <;> simp

theorem coe_ug3Sl_upper (c : K) :
    ((ug3Sl σ ι hι (sl2Upper c) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      !![1, 0, ι c; 0, 1, 0; 0, 0, 1] := by
  rw [coe_ug3Sl, CFSG.LieType.Steinberg.coe_sl2Upper]
  simp

theorem coe_ug3Sl_lower (c : K) :
    ((ug3Sl σ ι hι (sl2Lower c) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      !![1, 0, 0; 0, 1, 0; ι c, 0, 1] := by
  rw [coe_ug3Sl, CFSG.LieType.Steinberg.coe_sl2Lower]
  simp

theorem coe_ug3Sl_diag (r : Kˣ) :
    ((ug3Sl σ ι hι (diagUnit r) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      !![ι r, 0, 0; 0, 1, 0; 0, 0, ι ((r⁻¹ : Kˣ) : K)] := by
  rw [coe_ug3Sl, LinearPilot.coe_diagUnit]
  simp

omit [CharP K 2] in
theorem ug3_diagUnit_inv (r : Kˣ) : (diagUnit r)⁻¹ = diagUnit r⁻¹ := by
  refine inv_eq_of_mul_eq_one_right ?_
  ext i j
  simp only [Matrix.SpecialLinearGroup.coe_mul, LinearPilot.coe_diagUnit, inv_inv,
    Matrix.SpecialLinearGroup.coe_one]
  fin_cases i <;> fin_cases j <;> simp

variable (K) in
@[expose] noncomputable def ug3W : SL(2, K) := sl2Upper 1 * sl2Lower 1 * sl2Upper 1

theorem coe_ug3Sl_W :
    ((ug3Sl σ ι hι (ug3W K) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      !![0, 0, 1; 0, 1, 0; 1, 0, 0] := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hW : ((ug3W K : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = !![0, 1; 1, 0] := by
    simp only [ug3W, Matrix.SpecialLinearGroup.coe_mul, CFSG.LieType.Steinberg.coe_sl2Upper,
      CFSG.LieType.Steinberg.coe_sl2Lower, Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> linear_combination h2
  rw [coe_ug3Sl, hW]
  simp

theorem ug3Sl_W_mul_self : ug3Sl σ ι hι (ug3W K) * ug3Sl σ ι hι (ug3W K) = 1 := by
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_mul, Units.val_mul, coe_ug3Sl_W]
  simp only [Matrix.mul_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

end Sl

section Act

variable {K F : Type} [Field K] [Field F] [CharP K 2] [CharP F 2] {σ : F ≃+* F}
  (hσ : ∀ c, σ (σ c) = c) {ι : K →+* F} (hι : ∀ c, σ (ι c) = ι c)

omit [CharP K 2] in
include hι in
theorem ug3_valid_zero (c : K) : ι c + σ (ι c) + σ 0 * 0 = 0 := by
  rw [hι, mul_zero, add_zero, CharTwo.add_self_eq_zero]

theorem ug3Sl_upper_eq (c : K) : ug3Sl σ ι hι (sl2Upper c) = ug3Heis hσ (ug3_valid_zero hι c) := by
  apply Subtype.ext
  apply Units.ext
  rw [coe_ug3Sl_upper, coe_ug3Heis_three]
  simp

omit [CharP K 2] [CharP F 2] in
include hι in
theorem ug3_valid_conj (r : Kˣ) {a b : F} (h : b + σ b + σ a * a = 0) :
    ι r * ι r * b + σ (ι r * ι r * b) + σ (ι r * a) * (ι r * a) = 0 := by
  rw [map_mul, map_mul, map_mul, hι]
  linear_combination (ι r * ι r) * h

omit [CharP F 2] in
theorem ug3_conj_diag (r : Kˣ) {a b : F} (h : b + σ b + σ a * a = 0) :
    ug3Sl σ ι hι (diagUnit r) * ug3Heis hσ h * (ug3Sl σ ι hι (diagUnit r))⁻¹ =
      ug3Heis hσ (ug3_valid_conj hι r h) := by
  rw [← map_inv, ug3_diagUnit_inv]
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul]
  rw [coe_ug3Sl_diag, coe_ug3Sl_diag, coe_ug3Heis_three, coe_ug3Heis_three, inv_inv]
  simp only [Matrix.mul_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [map_mul, hι] <;> ring

omit [CharP F 2] in
theorem ug3Heis_commute_zero {a b d : F} (h : b + σ b + σ a * a = 0)
    (hd : d + σ d + σ 0 * 0 = 0) : ug3Heis hσ h * ug3Heis hσ hd = ug3Heis hσ hd * ug3Heis hσ h := by
  rw [ug3Heis_mul, ug3Heis_mul]
  exact ug3Heis_congr hσ _ _ (by ring) (by rw [map_zero]; ring)

omit [CharP F 2] in
theorem coe_ug3W_conj {a b : F} (h : b + σ b + σ a * a = 0) :
    (((ug3Sl σ ι hι (ug3W K) * ug3Heis hσ h * ug3Sl σ ι hι (ug3W K) : SU σ 3) :
      GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = heisenbergMatrix σ (2 : Fin 3) 1 a b := by
  simp only [Subgroup.coe_mul, Units.val_mul]
  rw [coe_ug3Sl_W, coe_ug3Heis_three]
  simp only [Matrix.mul_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [heisenbergMatrix, Fin.rev]

omit [CharP F 2] in
theorem exists_eq_ug3W_conj {x : SU σ 3} (hx : x ∈ rootGroup σ hσ 3 (-Pi.single 0 1)) :
    ∃ (a b : F) (h : b + σ b + σ a * a = 0),
      x = ug3Sl σ ι hι (ug3W K) * ug3Heis hσ h * ug3Sl σ ι hι (ug3W K) := by
  rw [CFSG.LieType.Steinberg.rootGroup_three_neg_eq_heisenbergSubgroup hσ] at hx
  obtain ⟨a, b, h, hx⟩ := hx
  exact ⟨a, b, h, Subtype.ext (Units.ext (hx.trans (coe_ug3W_conj hσ hι h).symm))⟩

end Act

section Key

variable {K F : Type} [Field K] [Field F] [CharP K 2] [CharP F 2] {σ : F ≃+* F}
  (hσ : ∀ c, σ (σ c) = c) {ω : F} (hω : σ ω = ω + 1)

include hω in
theorem ug3_valid_y : ω + σ ω + σ 1 * 1 = 0 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  rw [hω, map_one]
  linear_combination (ω + 1) * h2

omit [CharP F 2] in
include hω in
theorem ug3_omega_ne_zero : ω ≠ 0 := by
  rintro rfl
  rw [map_zero, zero_add] at hω
  exact zero_ne_one hω

include hω in
theorem ug3_omega_add_one_ne_zero : ω + 1 ≠ 0 := by
  intro h
  have h1 : ω = 1 := by
    have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
    linear_combination h - h2
  rw [h1, map_one] at hω
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  exact one_ne_zero (by linear_combination hω + h2)

include hω in
theorem ug3_sigma_inv_add_one : σ (ω + 1)⁻¹ = ω⁻¹ := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  rw [map_inv₀, map_add, map_one, hω, show ω + 1 + 1 = ω by linear_combination h2]

omit [CharP F 2] in
include hω in
theorem ug3_sigma_inv : σ ω⁻¹ = (ω + 1)⁻¹ := by
  rw [map_inv₀, hω]

include hω in
theorem ug3_valid_xp : ω⁻¹ + σ ω⁻¹ + σ (ω + 1)⁻¹ * (ω + 1)⁻¹ = 0 := by
  rw [ug3_sigma_inv hω, ug3_sigma_inv_add_one hω]
  have h0 := ug3_omega_ne_zero hω
  have h1 := ug3_omega_add_one_ne_zero hω
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  field_simp
  linear_combination (ω + 1) * h2

theorem coe_ug3Heis_y :
    ((ug3Heis hσ (ug3_valid_y hω) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      !![1, 1, ω; 0, 1, 1; 0, 0, 1] := by
  rw [coe_ug3Heis_three, map_one, CharTwo.neg_eq]

theorem coe_ug3Heis_y_inv :
    ((((ug3Heis hσ (ug3_valid_y hω))⁻¹ : SU σ 3) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      !![1, 1, ω + 1; 0, 1, 1; 0, 0, 1] := by
  rw [ug3Heis_inv, coe_ug3Heis_three, map_neg, map_one]
  simp only [CharTwo.neg_eq, mul_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sub_eq_add_neg, CharTwo.neg_eq]

theorem coe_ug3Heis_xp :
    ((ug3Heis hσ (ug3_valid_xp hω) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      !![1, (ω + 1)⁻¹, ω⁻¹; 0, 1, ω⁻¹; 0, 0, 1] := by
  rw [coe_ug3Heis_three, ug3_sigma_inv_add_one hω, CharTwo.neg_eq]

theorem coe_ug3Heis_xp_inv :
    ((((ug3Heis hσ (ug3_valid_xp hω))⁻¹ : SU σ 3) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      !![1, (ω + 1)⁻¹, (ω + 1)⁻¹; 0, 1, ω⁻¹; 0, 0, 1] := by
  rw [ug3Heis_inv, coe_ug3Heis_three, map_neg, ug3_sigma_inv_add_one hω]
  have h0 := ug3_omega_ne_zero hω
  have h1 := ug3_omega_add_one_ne_zero hω
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  ext i j
  fin_cases i <;> fin_cases j <;> simp [CharTwo.neg_eq]
  field_simp
  ring

end Key

section Point

variable {K F : Type} [Field K] [Field F] [CharP K 2] [CharP F 2] {σ : F ≃+* F}
  (hσ : ∀ c, σ (σ c) = c) (ι : K →+* F) (hι : ∀ c, σ (ι c) = ι c) {ω : F} (hω : σ ω = ω + 1)

theorem coe_ug3_h0 :
    (((ug3Sl σ ι hι (ug3W K) * (ug3Heis hσ (ug3_valid_y hω) * ug3Sl σ ι hι (ug3W K) *
      (ug3Heis hσ (ug3_valid_y hω))⁻¹) : SU σ 3) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        !![1, 1, ω + 1; 1, 0, ω; ω, ω + 1, ω * (ω + 1)] := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  simp only [Subgroup.coe_mul, Units.val_mul]
  rw [coe_ug3Sl_W, coe_ug3Heis_y hσ hω, coe_ug3Heis_y_inv hσ hω]
  simp only [Matrix.mul_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> grind

theorem coe_ug3_h0_inv :
    ((((ug3Sl σ ι hι (ug3W K) * (ug3Heis hσ (ug3_valid_y hω) * ug3Sl σ ι hι (ug3W K) *
      (ug3Heis hσ (ug3_valid_y hω))⁻¹))⁻¹ : SU σ 3) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        !![ω * (ω + 1), ω + 1, ω; ω, 0, 1; ω + 1, 1, 1] := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hw : (ug3Sl σ ι hι (ug3W K))⁻¹ = ug3Sl σ ι hι (ug3W K) :=
    inv_eq_of_mul_eq_one_right (ug3Sl_W_mul_self σ ι hι)
  rw [_root_.mul_inv_rev, _root_.mul_inv_rev, _root_.mul_inv_rev, inv_inv, hw]
  simp only [Subgroup.coe_mul, Units.val_mul]
  rw [coe_ug3Sl_W, coe_ug3Heis_y hσ hω, coe_ug3Heis_y_inv hσ hω]
  simp only [Matrix.mul_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> grind

theorem ug3_key {c d : K} (hcd : ι d * (ω * (ω + 1)) = ι c) :
    ug3Heis hσ (ug3_valid_xp hω) * ug3Sl σ ι hι (sl2Lower c) * (ug3Heis hσ (ug3_valid_xp hω))⁻¹ =
      (ug3Sl σ ι hι (ug3W K) * (ug3Heis hσ (ug3_valid_y hω) * ug3Sl σ ι hι (ug3W K) *
        (ug3Heis hσ (ug3_valid_y hω))⁻¹)) * ug3Sl σ ι hι (sl2Upper d) *
        (ug3Sl σ ι hι (ug3W K) * (ug3Heis hσ (ug3_valid_y hω) * ug3Sl σ ι hι (ug3W K) *
          (ug3Heis hσ (ug3_valid_y hω))⁻¹))⁻¹ := by
  have h0 := ug3_omega_ne_zero hω
  have h1 := ug3_omega_add_one_ne_zero hω
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_mul, Units.val_mul, Subgroup.coe_mul, Units.val_mul, Subgroup.coe_mul,
    Units.val_mul, Subgroup.coe_mul, Units.val_mul, coe_ug3_h0 hσ ι hι hω,
    coe_ug3_h0_inv hσ ι hι hω, coe_ug3Heis_xp hσ hω, coe_ug3Heis_xp_inv hσ hω, coe_ug3Sl_lower,
    coe_ug3Sl_upper, ← hcd]
  simp only [Matrix.mul_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> field_simp <;> grind

end Point

section Gen

variable {F : Type} [Field F] [CharP F 2] {K : Type} [Field K] [CharP K 2] {σ : F ≃+* F}

theorem ug3_eq_top_of (hσ : ∀ c, σ (σ c) = c) (ι : K →+* F) (hι : ∀ c, σ (ι c) = ι c)
    (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι) (hK : ∃ r : K, r ≠ 0 ∧ r ≠ 1) {ω : F}
    (hω : σ ω = ω + 1) (htop : CFSG.LieType.CurtisTits.rankOne (rootGroup σ hσ 3) 0 = ⊤)
    {H : Subgroup (SU σ 3)} (hA : ∀ s : SL(2, K), ug3Sl σ ι hι s ∈ H)
    (hAy : ∀ s : SL(2, K), ug3Heis hσ (ug3_valid_y hω) * ug3Sl σ ι hι s *
      (ug3Heis hσ (ug3_valid_y hω))⁻¹ ∈ H) :
    H = ⊤ := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  set P : F → Prop := fun a => ∃ (b : F) (h : b + σ b + σ a * a = 0), ug3Heis hσ h ∈ H with hP
  have hPcongr : ∀ {a a'}, P a → a = a' → P a' := fun ha e => e ▸ ha
  have hZ : ∀ c : K, ug3Heis hσ (ug3_valid_zero hι c) ∈ H := fun c => by
    rw [← ug3Sl_upper_eq hσ hι c]
    exact hA _
  have hP0 : ∀ a, a = 0 → P a := by
    rintro a rfl
    refine ⟨0, by simp, ?_⟩
    rw [ug3Heis_zero]
    exact H.one_mem
  have hscale : ∀ (r : K) {a}, P a → P (ι r * a) := by
    intro r a ⟨b, h, hb⟩
    by_cases hr : r = 0
    · exact hP0 _ (by rw [hr, map_zero, zero_mul])
    · obtain ⟨u, rfl⟩ : ∃ u : Kˣ, (u : K) = r := ⟨Units.mk0 r hr, rfl⟩
      refine ⟨_, ug3_valid_conj hι u h, ?_⟩
      rw [← ug3_conj_diag hσ hι u h]
      exact mul_mem (mul_mem (hA _) hb) (inv_mem (hA _))
  have hadd : ∀ {a a'}, P a → P a' → P (a + a') := by
    rintro a a' ⟨b, h, hb⟩ ⟨b', h', hb'⟩
    exact ⟨_, ug3_valid_mul hσ h h', by rw [← ug3Heis_mul hσ h h']; exact mul_mem hb hb'⟩
  obtain ⟨r, hr0, hr1⟩ := hK
  obtain ⟨u, rfl⟩ : ∃ u : Kˣ, (u : K) = r := ⟨Units.mk0 r hr0, rfl⟩
  have hu1 : (1 : F) - ι u ≠ 0 := by
    rw [← map_one ι, ← map_sub]
    exact (map_ne_zero ι).2 (sub_ne_zero.2 (Ne.symm hr1))
  have hdiv : ∀ {a : F}, P ((1 + ι u * -1) * a) → P a := by
    intro a ha
    refine hPcongr (hscale ((1 - u)⁻¹) ha) ?_
    rw [map_inv₀, map_sub, map_one]
    field_simp
    ring
  have hP1 : P 1 := by
    refine hdiv (hPcongr ⟨_, ug3_valid_mul hσ (ug3_valid_y hω)
      (ug3_valid_conj hι u (ug3_valid_inv hσ (ug3_valid_y hω))), ?_⟩ (by ring))
    rw [← ug3Heis_mul hσ (ug3_valid_y hω)
      (ug3_valid_conj hι u (ug3_valid_inv hσ (ug3_valid_y hω))),
      ← ug3_conj_diag hσ hι u (ug3_valid_inv hσ (ug3_valid_y hω)),
      ← ug3Heis_inv hσ (ug3_valid_y hω)]
    have e : ug3Heis hσ (ug3_valid_y hω) * (ug3Sl σ ι hι (diagUnit u) *
        (ug3Heis hσ (ug3_valid_y hω))⁻¹ * (ug3Sl σ ι hι (diagUnit u))⁻¹) =
        ug3Heis hσ (ug3_valid_y hω) * ug3Sl σ ι hι (diagUnit u) *
          (ug3Heis hσ (ug3_valid_y hω))⁻¹ * (ug3Sl σ ι hι (diagUnit u))⁻¹ := by group
    rw [e]
    exact mul_mem (hAy _) (inv_mem (hA _))
  have hω0 := ug3_omega_ne_zero hω
  have hω1 := ug3_omega_add_one_ne_zero hω
  obtain ⟨n₀, hn₀⟩ : ω * (ω + 1) ∈ Set.range ι := (hfix _).1 (by
    rw [map_mul, map_add, map_one, hω]
    linear_combination (ω + 1) * h2)
  have hh₀ : ug3Sl σ ι hι (ug3W K) * (ug3Heis hσ (ug3_valid_y hω) * ug3Sl σ ι hι (ug3W K) *
      (ug3Heis hσ (ug3_valid_y hω))⁻¹) ∈ H := mul_mem (hA _) (hAy _)
  have hxA : ∀ s : SL(2, K), ug3Heis hσ (ug3_valid_xp hω) * ug3Sl σ ι hι s *
      (ug3Heis hσ (ug3_valid_xp hω))⁻¹ ∈ H := by
    intro s
    have hle : Subgroup.closure (Set.range (sl2Upper (k := K)) ∪ Set.range sl2Lower) ≤
        H.comap ((MulAut.conj (ug3Heis hσ (ug3_valid_xp hω))).toMonoidHom.comp
          (ug3Sl σ ι hι)) := by
      rw [Subgroup.closure_le]
      rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
      · change ug3Heis hσ (ug3_valid_xp hω) * ug3Sl σ ι hι (sl2Upper c) *
          (ug3Heis hσ (ug3_valid_xp hω))⁻¹ ∈ H
        rw [ug3Sl_upper_eq hσ hι c, ug3Heis_commute_zero hσ, mul_inv_cancel_right]
        exact hZ c
      · change ug3Heis hσ (ug3_valid_xp hω) * ug3Sl σ ι hι (sl2Lower c) *
          (ug3Heis hσ (ug3_valid_xp hω))⁻¹ ∈ H
        have hn0 : ι n₀ ≠ 0 := by rw [hn₀]; exact mul_ne_zero hω0 hω1
        rw [ug3_key hσ ι hι hω (d := c * n₀⁻¹) (by rw [map_mul, map_inv₀, ← hn₀]; field_simp)]
        exact mul_mem (mul_mem hh₀ (hA _)) (inv_mem hh₀)
    exact hle (CFSG.LieType.Steinberg.Sp.mem_closure_sl2 s)
  have hPp : P (ω + 1)⁻¹ := by
    refine hdiv (hPcongr ⟨_, ug3_valid_mul hσ (ug3_valid_xp hω)
      (ug3_valid_conj hι u (ug3_valid_inv hσ (ug3_valid_xp hω))), ?_⟩ (by ring))
    rw [← ug3Heis_mul hσ (ug3_valid_xp hω)
      (ug3_valid_conj hι u (ug3_valid_inv hσ (ug3_valid_xp hω))),
      ← ug3_conj_diag hσ hι u (ug3_valid_inv hσ (ug3_valid_xp hω)),
      ← ug3Heis_inv hσ (ug3_valid_xp hω)]
    have e : ug3Heis hσ (ug3_valid_xp hω) * (ug3Sl σ ι hι (diagUnit u) *
        (ug3Heis hσ (ug3_valid_xp hω))⁻¹ * (ug3Sl σ ι hι (diagUnit u))⁻¹) =
        ug3Heis hσ (ug3_valid_xp hω) * ug3Sl σ ι hι (diagUnit u) *
          (ug3Heis hσ (ug3_valid_xp hω))⁻¹ * (ug3Sl σ ι hι (diagUnit u))⁻¹ := by group
    rw [e]
    exact mul_mem (hxA _) (inv_mem (hA _))
  have hPω : P ω := hPcongr (hscale n₀ hPp) (by rw [hn₀]; field_simp)
  have hPall : ∀ a, P a := by
    intro a
    obtain ⟨k₂, hk₂⟩ : a + σ a ∈ Set.range ι := (hfix _).1 (by rw [map_add, hσ, add_comm])
    obtain ⟨k₁, hk₁⟩ : a + (a + σ a) * ω ∈ Set.range ι := (hfix _).1 (by
      rw [map_add, map_mul, map_add, hσ, hω]
      linear_combination (σ a) * h2)
    refine hPcongr (hadd (hscale k₁ hP1) (hscale k₂ hPω)) ?_
    rw [hk₁, hk₂]
    linear_combination (a + σ a) * ω * h2
  have hX : rootGroup σ hσ 3 (Pi.single 0 1) ≤ H := by
    intro x hx
    obtain ⟨a, b, h, rfl⟩ := exists_ug3Heis_of_mem_rootGroup hσ hx
    obtain ⟨b', h', hb'⟩ := hPall a
    have hd : (b - b') + σ (b - b') = 0 := by
      rw [map_sub]
      linear_combination h - h'
    obtain ⟨c, hc⟩ : b - b' ∈ Set.range ι := (hfix _).1 (by linear_combination hd - (b - b') * h2)
    have e : ug3Heis hσ h = ug3Heis hσ h' * ug3Heis hσ (ug3_valid_zero hι c) := by
      rw [ug3Heis_mul]
      exact ug3Heis_congr hσ _ _ (by ring) (by rw [hc, map_zero, mul_zero]; ring)
    rw [e]
    exact mul_mem hb' (hZ c)
  have hXn : rootGroup σ hσ 3 (-Pi.single 0 1) ≤ H := by
    intro x hx
    obtain ⟨a, b, h, rfl⟩ := exists_eq_ug3W_conj hσ hι hx
    exact mul_mem (mul_mem (hA _) (hX (ug3Heis_mem_rootGroup hσ h))) (hA _)
  rw [eq_top_iff, ← htop]
  exact sup_le hX hXn

theorem ug3_eq_top [Finite F] {f : ℕ} (hF : Nat.card F = (2 ^ f) ^ 2) (ι : K →+* F)
    (hι : ∀ c, unitaryInvolution F 2 f (ι c) = ι c)
    (hfix : ∀ x : F, unitaryInvolution F 2 f x = x ↔ x ∈ Set.range ι)
    (hK : ∃ r : K, r ≠ 0 ∧ r ≠ 1) {ω : F} (hω : unitaryInvolution F 2 f ω = ω + 1)
    {H : Subgroup (SU (unitaryInvolution F 2 f) 3)}
    (hA : ∀ s : SL(2, K), ug3Sl _ ι hι s ∈ H)
    (hAy : ∀ s : SL(2, K), ug3Heis (unitaryInvolution_involutive hF) (ug3_valid_y hω) *
      ug3Sl _ ι hι s * (ug3Heis (unitaryInvolution_involutive hF) (ug3_valid_y hω))⁻¹ ∈ H) :
    H = ⊤ :=
  ug3_eq_top_of (unitaryInvolution_involutive hF) ι hι hfix hK hω
    (CFSG.LieType.Steinberg.rankOne_three_eq_top hF) hA hAy

end Gen

end CFSG.SeitzReduction.SymplecticPilot
