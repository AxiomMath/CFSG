module

public import CFSG.GH74.GLS.Stage4.Q9.ModelBase
public import CFSG.CharacterTheory.PSL2Table
public meta import CFSG.GH74.GLS.Stage4.Q9.ModelBase
public meta import CFSG.CharacterTheory.PSL2Table.Basic
public meta import Mathlib
public import CFSG.GH74.GLS.Stage4.Q9.TablesInputs
public meta import CFSG.GH74.GLS.Stage4.Q9.TablesInputs
public import Certificates.Certificate5100
public import Certificates.Certificate5102

public section

namespace CFSG.GH74.GLS.Stage4.Q9

open CFSG CFSG.PSL2Table
open scoped MatrixGroups

local notation "𝕄" => Matrix (Fin 2) (Fin 2) F9

theorem two_ne_zero_F9 : (2 : F9) ≠ 0 := by decide

theorem ringChar_F9_ne_two : ringChar F9 ≠ 2 := by
  intro h
  have h2 : ((2 : ℕ) : F9) = 0 := (ringChar.spec F9 2).mpr (by rw [h])
  revert h2
  decide

theorem five_le_card_F9 : 5 ≤ Fintype.card F9 := by
  rw [card_F9]; norm_num

theorem isSquare_neg_one_F9 : IsSquare (-1 : F9) := ⟨⟨0, 1⟩, by decide⟩

@[expose] noncomputable def psi9 : AddChar F9 ℂ := AddChar.FiniteField.primitiveChar_to_Complex F9

theorem psi9_isPrimitive : psi9.IsPrimitive :=
  AddChar.FiniteField.primitiveChar_to_Complex_isPrimitive F9

theorem card_nonsplitTorus_F9 : Nat.card (nonsplitTorus nu) = 5 := by
  have h := card_nonsplitTorus ringChar_F9_ne_two nu_not_isSquare
  rw [card_F9] at h
  omega

theorem card_splitTorus_F9 : Nat.card (splitTorus F9) = 4 := by
  have h := card_splitTorus (F := F9) two_ne_zero_F9
  rw [card_F9] at h
  omega

theorem exists_beta9 : ∃ β : nonsplitTorus nu →* ℂˣ, β ^ 2 ≠ 1 := by
  by_contra h
  have h : ∀ β : nonsplitTorus nu →* ℂˣ, β ^ 2 = 1 := fun β => by_contra fun hb => h ⟨β, hb⟩
  have h1 := card_units_hom_of_comm (A := nonsplitTorus nu) nonsplitTorus_comm
  have h2 := card_sq_eq_one_nonsplitTorus ringChar_F9_ne_two nu_not_isSquare
  rw [ite_eq_left isSquare_neg_one_F9] at h2
  have h3 : Nat.card {α : nonsplitTorus nu →* ℂˣ // α ^ 2 = 1} =
      Nat.card (nonsplitTorus nu →* ℂˣ) := Nat.card_congr (Equiv.subtypeUnivEquiv h)
  have h4 := h1.1
  have h5 := h1.2
  rw [card_nonsplitTorus_F9] at h4
  omega

@[expose] noncomputable def beta9 : nonsplitTorus nu →* ℂˣ := Classical.choose exists_beta9

theorem beta9_sq_ne_one : beta9 ^ 2 ≠ 1 := Classical.choose_spec exists_beta9

abbrev mkL : SL2 →* PSL(2, F9) := CFSG.PSL2Table.mk

@[expose] noncomputable def rhoC : PSL(2, F9) → ℂ := discrete beta9

@[expose] noncomputable def lamC : PSL(2, F9) → ℂ := halfPlus ringChar_F9_ne_two psi9 nu

@[expose] noncomputable def gaussG : ℂ := quadGauss psi9

theorem epsSign_F9 : epsSign F9 = 1 := by
  rw [epsSign, ite_eq_left isSquare_neg_one_F9]

theorem rhoC_mem_irr : rhoC ∈ BlocksIrr PSL(2, F9) :=
  discrete_mem_blocksIrr ringChar_F9_ne_two five_le_card_F9 nu_not_isSquare beta9_sq_ne_one

theorem lamC_mem_irr : lamC ∈ BlocksIrr PSL(2, F9) :=
  (psl2_character_table ringChar_F9_ne_two five_le_card_F9 nu_not_isSquare psi9_isPrimitive).2.2.2.2.1

theorem rhoC_mem : rhoC ∈ BlocksVChar PSL(2, F9) := AddSubgroup.subset_closure rhoC_mem_irr

theorem lamC_mem : lamC ∈ BlocksVChar PSL(2, F9) := AddSubgroup.subset_closure lamC_mem_irr

open Tables

namespace Tables

instance (R X : SL2) : Decidable (IsRepOf R X) := inferInstanceAs (Decidable (_ ∨ _))

end Tables

open Tables

namespace Tables

theorem conjSL_eq (c M : SL2) : conjSL c M = c * M * c⁻¹ := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_inv_SL]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [conjSL, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

end Tables

theorem mem_allSL2 : ∀ M : SL2, M ∈ allSL2 :=
  Certificates.certificate5102.1

namespace Tables

theorem repIdx_repList_aux :
    ∀ j : Fin 7, repIdx (repList j) = j :=
  Certificates.certificate5102.2.1

theorem repIdx_spec_aux :
    ∀ M ∈ allSL2, ∃ c ∈ allSL2, IsRepOf (repList (repIdx M)) (conjSL c M) :=
  Certificates.certificate5102.2.2.1

theorem repIdx_neg_aux :
    ∀ M ∈ allSL2, repIdx (M * minusOne) = repIdx M :=
  Certificates.certificate5102.2.2.2.2.1

theorem repIdx_sigma_aux :
    ∀ M ∈ allSL2, repIdx (sigmaAut M) = classSwap (repIdx M) :=
  Certificates.certificate5102.2.2.2.2.2.1

end Tables

theorem repIdx_repList
    (j : Fin 7) : repIdx (repList j) = j := repIdx_repList_aux j

theorem repIdx_spec (M : SL2) :
    ∃ c : SL2, c * M * c⁻¹ = repList (repIdx M) ∨ c * M * c⁻¹ = repList (repIdx M) * minusOne := by
  obtain ⟨c, -, hc⟩ := repIdx_spec_aux M (mem_allSL2 M)
  exact ⟨c, by rwa [conjSL_eq] at hc⟩

theorem repIdx_neg_mul
    (M : SL2) : repIdx (M * minusOne) = repIdx M :=
  repIdx_neg_aux M (mem_allSL2 M)

theorem repIdx_sigma
    (M : SL2) : repIdx (sigmaAut M) = classSwap (repIdx M) :=
  repIdx_sigma_aux M (mem_allSL2 M)

theorem mkL_minusOne : mkL minusOne = 1 := by
  have h : minusOne = -1 := Subtype.ext (by
    rw [minusOne_val, Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one])
  rw [h]
  exact (mk_eq_one_iff (-1)).mpr (Or.inr rfl)

namespace Tables

theorem mkL_mul_minusOne (A : SL2) : mkL (A * minusOne) = mkL A := by
  rw [map_mul, mkL_minusOne, mul_one]

end Tables

open Tables

theorem classFn_mkL
    {f : PSL(2, F9) → ℂ} (hf : f ∈ BlocksVChar PSL(2, F9)) (M : SL2) :
    f (mkL M) = f (mkL (repList (repIdx M))) := by
  have hcf := blocksVChar_isClassFunction hf
  obtain ⟨c, hc | hc⟩ := repIdx_spec M
  · have e : f (mkL (c * M * c⁻¹)) = f (mkL M) := by
      simp only [map_mul, map_inv]; exact hcf (mkL M) (mkL c)
    rw [← e, hc]
  · have e : f (mkL (c * M * c⁻¹)) = f (mkL M) := by
      simp only [map_mul, map_inv]; exact hcf (mkL M) (mkL c)
    rw [← e, hc, mkL_mul_minusOne]

namespace Tables

theorem Y_mem : Y ∈ nonsplitSL nu := nsElem_mem_nonsplitSL nu _ _ _

theorem Y2_mem : Y2 ∈ nonsplitSL nu := (nonsplitSL nu).mul_mem Y_mem Y_mem

theorem Y_ne_one : Y ≠ 1 := by
  intro h
  have := congrArg (fun x : SL2 => (x : 𝕄) 0 1) h
  revert this
  decide

theorem Y_ne_neg_one : Y ≠ -1 := by
  intro h
  have := congrArg (fun x : SL2 => (x : 𝕄) 0 1) h
  revert this
  decide

theorem Y_pow_five : Y ^ 5 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
  decide

theorem Y2_ne_one : Y2 ≠ 1 := by
  intro h
  have := congrArg (fun x : SL2 => (x : 𝕄) 0 1) h
  revert this
  decide

theorem Y2_ne_neg_one : Y2 ≠ -1 := by
  intro h
  have := congrArg (fun x : SL2 => (x : 𝕄) 0 1) h
  revert this
  decide

theorem mkL_Y_mem : mkL Y ∈ nonsplitTorus nu := (mk_mem_nonsplitTorus_iff nu Y).mpr Y_mem

theorem mkL_Y2_mem : mkL Y2 ∈ nonsplitTorus nu := (mk_mem_nonsplitTorus_iff nu Y2).mpr Y2_mem

theorem mkL_Y_ne_one : mkL Y ≠ 1 := fun h => by
  rcases (mk_eq_one_iff Y).mp h with h | h
  exacts [Y_ne_one h, Y_ne_neg_one h]

theorem mkL_Y2_ne_one : mkL Y2 ≠ 1 := fun h => by
  rcases (mk_eq_one_iff Y2).mp h with h | h
  exacts [Y2_ne_one h, Y2_ne_neg_one h]

theorem orderOf_mkL_Y : orderOf (mkL Y) = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact orderOf_eq_prime (by rw [← map_pow, Y_pow_five, map_one]) mkL_Y_ne_one

@[expose] def yS : nonsplitTorus nu := ⟨mkL Y, mkL_Y_mem⟩

theorem orderOf_yS : orderOf yS = 5 := by
  rw [yS, Subgroup.orderOf_mk, orderOf_mkL_Y]

theorem zpowers_eq_top_of_orderOf {A : Type*} [Group A] [Finite A] {a : A}
    (h : orderOf a = Nat.card A) : Subgroup.zpowers a = ⊤ := by
  rw [← Subgroup.card_eq_iff_eq_top, Nat.card_zpowers, h]

theorem hom_eq_one_of_gen {A : Type*} [Group A] [Finite A] {a : A} (h : orderOf a = Nat.card A)
    {χ : A →* ℂˣ} (hχ : χ a = 1) : χ = 1 := by
  ext g
  have hg : g ∈ Subgroup.zpowers a := by
    rw [zpowers_eq_top_of_orderOf h]; exact Subgroup.mem_top g
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  rw [map_zpow, hχ, one_zpow, MonoidHom.one_apply]

@[expose] noncomputable def zeta9 : ℂ := (beta9 yS : ℂ)

theorem zeta9_pow_five : zeta9 ^ 5 = 1 := by
  have h : yS ^ 5 = 1 := by rw [← orderOf_yS]; exact pow_orderOf_eq_one yS
  have h1 : beta9 yS ^ 5 = 1 := by rw [← map_pow, h, map_one]
  have h2 := congrArg Units.val h1
  rwa [Units.val_pow_eq_pow_val, Units.val_one] at h2

theorem zeta9_ne_one : zeta9 ≠ 1 := by
  intro h
  have h1 : beta9 yS = 1 := Units.ext h
  have h2 : orderOf yS = Nat.card (nonsplitTorus nu) := by rw [orderOf_yS, card_nonsplitTorus_F9]
  have h3 : beta9 = 1 := hom_eq_one_of_gen h2 h1
  apply beta9_sq_ne_one
  ext g
  simp [h3]

theorem zeta9_sum : zeta9 ^ 4 + zeta9 ^ 3 + zeta9 ^ 2 + zeta9 + 1 = 0 := by
  have h : (zeta9 - 1) * (zeta9 ^ 4 + zeta9 ^ 3 + zeta9 ^ 2 + zeta9 + 1) = 0 := by
    linear_combination zeta9_pow_five
  exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr zeta9_ne_one)

theorem zeta9_inv : zeta9⁻¹ = zeta9 ^ 4 := by
  apply inv_eq_of_mul_eq_one_right
  linear_combination zeta9_pow_five

end Tables

open Tables

@[expose] noncomputable def r : ℂ := -((beta9 yS : ℂ) + (beta9 yS⁻¹ : ℂ))

namespace Tables

theorem r_eq : r = -(zeta9 + zeta9 ^ 4) := by
  rw [r, map_inv, Units.val_inv_eq_inv_val, ← zeta9, zeta9_inv]

end Tables

open Tables

theorem rho_r_sq : r ^ 2 = r + 1 := by
  rw [r_eq]
  linear_combination zeta9_sum + (2 + zeta9 ^ 3) * zeta9_pow_five

@[expose] noncomputable def rhoTab : Fin 7 → ℂ := ![8, -1, -1, 0, 0, r, 1 - r]

@[expose] noncomputable def lamTab : Fin 7 → ℂ :=
  ![5, (1 + gaussG) / 2, (1 - gaussG) / 2, 1, -1, 0, 0]

@[expose] def muTab : Fin 7 → ℤ := ![10, 1, 1, 2, -2, 0, 0]

namespace Tables

theorem mkL_diag_sq (a : F9ˣ) : (mkL (diag a)) ^ 2 = mkL (diag (a * a)) := by
  rw [pow_two, ← map_mul, ← diag_mul]

theorem mkL_R4_mem : mkL R4 ∈ splitTorus F9 := mk_diag_mem_splitTorus aEight

theorem mkL_R3_mem : mkL R3 ∈ splitTorus F9 := mk_diag_mem_splitTorus aFour

theorem mkL_R3_ne_one : mkL R3 ≠ 1 := by
  rw [R3, aFour]
  intro h
  have := (mk_diag_eq_one_iff (aEight * aEight)).mp h
  revert this
  decide

theorem mkL_R4_ne_one : mkL R4 ≠ 1 := by
  rw [R4]
  intro h
  have := (mk_diag_eq_one_iff aEight).mp h
  revert this
  decide

theorem orderOf_mkL_R4 : orderOf (mkL R4) = 4 := by
  have h2 : ¬ (mkL R4) ^ 2 ^ 1 = 1 := by
    rw [pow_one, R4, mkL_diag_sq, mk_diag_eq_one_iff]
    decide
  have h4 : (mkL R4) ^ 2 ^ (1 + 1) = 1 := by
    have e : (mkL R4) ^ 2 ^ (1 + 1) = ((mkL R4) ^ 2) ^ 2 := by
      rw [← pow_mul]; norm_num
    rw [e, R4, mkL_diag_sq, mkL_diag_sq, mk_diag_eq_one_iff]
    decide
  simpa using orderOf_eq_prime_pow h2 h4

@[expose] def x4 : splitTorus F9 := ⟨mkL R4, mkL_R4_mem⟩

theorem orderOf_x4 : orderOf x4 = Nat.card (splitTorus F9) := by
  rw [x4, Subgroup.orderOf_mk, orderOf_mkL_R4, card_splitTorus_F9]

theorem splitQuadChar_x4 : (splitQuadChar F9 x4 : ℂ) = -1 := by
  obtain ⟨hne, hsq⟩ := splitQuadChar_spec ringChar_F9_ne_two isSquare_neg_one_F9
  have h1 : splitQuadChar F9 x4 ^ 2 = 1 := by
    have := DFunLike.congr_fun hsq x4
    rwa [MonoidHom.pow_apply, MonoidHom.one_apply] at this
  have h2 : (splitQuadChar F9 x4 : ℂ) * (splitQuadChar F9 x4 : ℂ) = 1 := by
    have := congrArg Units.val h1
    rwa [Units.val_pow_eq_pow_val, Units.val_one, pow_two] at this
  rcases mul_self_eq_one_iff.mp h2 with h | h
  · exact absurd (hom_eq_one_of_gen orderOf_x4 (Units.ext h)) hne
  · exact h

theorem splitQuadChar_R3 :
    (splitQuadChar F9 ⟨mkL R3, mkL_R3_mem⟩ : ℂ) = 1 := by
  have e : (⟨mkL R3, mkL_R3_mem⟩ : splitTorus F9) = x4 * x4 := by
    apply Subtype.ext
    show mkL R3 = mkL R4 * mkL R4
    rw [R3, R4, aFour, diag_mul, map_mul]
  rw [e, map_mul, Units.val_mul, splitQuadChar_x4]
  norm_num

end Tables

namespace Tables

theorem rhoC_one : rhoC 1 = 8 := by
  rw [rhoC, discrete_one ringChar_F9_ne_two nu_not_isSquare, card_F9]
  norm_num

theorem mkL_unip_ne_one {t : F9} (ht : t ≠ 0) : mkL (unip t) ≠ 1 :=
  fun h => ht ((mk_unip_eq_one_iff two_ne_zero_F9 t).mp h)

theorem rhoC_unip {t : F9} (ht : t ≠ 0) : rhoC (mkL (unip t)) = -1 :=
  discrete_of_mem_unipotent ringChar_F9_ne_two nu_not_isSquare beta9 (mk_unip_mem_unipotent t)
    (mkL_unip_ne_one ht)

theorem rhoC_split {x : PSL(2, F9)} (hx : x ∈ splitTorus F9) (hx1 : x ≠ 1) : rhoC x = 0 :=
  discrete_of_mem_splitTorus ringChar_F9_ne_two nu_not_isSquare beta9 hx hx1

theorem rhoC_Y : rhoC (mkL Y) = r :=
  discrete_of_mem_nonsplitTorus ringChar_F9_ne_two nu_not_isSquare beta9 mkL_Y_mem mkL_Y_ne_one

theorem rhoC_Y2 : rhoC (mkL Y2) = 1 - r := by
  rw [rhoC, discrete_of_mem_nonsplitTorus ringChar_F9_ne_two nu_not_isSquare beta9 mkL_Y2_mem
    mkL_Y2_ne_one]
  have e : (⟨mkL Y2, mkL_Y2_mem⟩ : nonsplitTorus nu) = yS * yS := by
    apply Subtype.ext
    show mkL Y2 = mkL Y * mkL Y
    rw [Y2, map_mul]
  have h1 : (beta9 (yS * yS) : ℂ) = zeta9 * zeta9 := by
    rw [map_mul, Units.val_mul]; rfl
  have h2 : (beta9 (yS * yS)⁻¹ : ℂ) = (zeta9 * zeta9)⁻¹ := by
    rw [map_inv, Units.val_inv_eq_inv_val, h1]
  rw [e, h1, h2, r_eq, mul_inv, zeta9_inv]
  linear_combination (-1) * zeta9_sum - zeta9 ^ 3 * zeta9_pow_five

end Tables

open Tables

theorem rhoC_repList (j : Fin 7) : rhoC (mkL (repList j)) = rhoTab j := by
  fin_cases j
  · show rhoC (mkL 1) = 8
    rw [map_one, rhoC_one]
  · show rhoC (mkL (unip 1)) = -1
    exact rhoC_unip one_ne_zero
  · show rhoC (mkL (unip nu)) = -1
    exact rhoC_unip nu_ne_zero
  · show rhoC (mkL R3) = 0
    exact rhoC_split mkL_R3_mem mkL_R3_ne_one
  · show rhoC (mkL R4) = 0
    exact rhoC_split mkL_R4_mem mkL_R4_ne_one
  · exact rhoC_Y
  · exact rhoC_Y2

namespace Tables

theorem quadChar_one_F9 : quadChar F9 1 = 1 := map_one _

theorem quadChar_nu_F9 : quadChar F9 nu = -1 := by
  rw [quadChar_apply, quadraticChar_neg_one_iff_not_isSquare.mpr nu_not_isSquare]
  norm_num

theorem normTwoDegree_F9 : normTwoDegree F9 = 10 := by
  rw [normTwoDegree, ite_eq_left isSquare_neg_one_F9, card_F9]

theorem lamC_one : lamC 1 = 5 := by
  rw [lamC, halfPlus_one ringChar_F9_ne_two psi9 nu_not_isSquare, normTwoDegree_F9]
  norm_num

theorem lamC_unip {t : F9} (ht : t ≠ 0) :
    lamC (mkL (unip t)) = (1 + quadChar F9 t * gaussG) / 2 := by
  rw [lamC, halfPlus_unip ringChar_F9_ne_two psi9_isPrimitive nu_not_isSquare ht, epsSign_F9]
  rfl

theorem lamC_split {x : PSL(2, F9)} (hx : x ∈ splitTorus F9) (hx1 : x ≠ 1) :
    lamC x = (splitQuadChar F9 ⟨x, hx⟩ : ℂ) := by
  rw [lamC, halfPlus_of_mem_splitTorus ringChar_F9_ne_two psi9 nu_not_isSquare hx hx1,
    ite_eq_left isSquare_neg_one_F9]

theorem lamC_nonsplit {x : PSL(2, F9)} (hx : x ∈ nonsplitTorus nu) (hx1 : x ≠ 1) : lamC x = 0 := by
  rw [lamC, halfPlus_of_mem_nonsplitTorus ringChar_F9_ne_two psi9 nu_not_isSquare hx hx1,
    ite_eq_left isSquare_neg_one_F9]

end Tables

open Tables

theorem lamC_repList (j : Fin 7) : lamC (mkL (repList j)) = lamTab j := by
  fin_cases j
  · show lamC (mkL 1) = 5
    rw [map_one, lamC_one]
  · show lamC (mkL (unip 1)) = (1 + gaussG) / 2
    rw [lamC_unip one_ne_zero, quadChar_one_F9, one_mul]
  · show lamC (mkL (unip nu)) = (1 - gaussG) / 2
    rw [lamC_unip nu_ne_zero, quadChar_nu_F9]
    ring
  · show lamC (mkL R3) = 1
    rw [lamC_split mkL_R3_mem mkL_R3_ne_one, splitQuadChar_R3]
  · show lamC (mkL R4) = -1
    rw [lamC_split mkL_R4_mem mkL_R4_ne_one]
    exact splitQuadChar_x4
  · show lamC (mkL Y) = 0
    exact lamC_nonsplit mkL_Y_mem mkL_Y_ne_one
  · show lamC (mkL Y2) = 0
    exact lamC_nonsplit mkL_Y2_mem mkL_Y2_ne_one

theorem rhoTab_classSwap (j : Fin 7) : rhoTab (classSwap j) = rhoTab j := by
  fin_cases j <;> rfl

theorem lamTab_add_classSwap (j : Fin 7) : lamTab j + lamTab (classSwap j) = (muTab j : ℂ) := by
  fin_cases j
  · show (5 : ℂ) + 5 = ((10 : ℤ) : ℂ)
    norm_num
  · show (1 + gaussG) / 2 + (1 - gaussG) / 2 = ((1 : ℤ) : ℂ)
    push_cast; ring
  · show (1 - gaussG) / 2 + (1 + gaussG) / 2 = ((1 : ℤ) : ℂ)
    push_cast; ring
  · show (1 : ℂ) + 1 = ((2 : ℤ) : ℂ)
    norm_num
  · show (-1 : ℂ) + -1 = ((-2 : ℤ) : ℂ)
    norm_num
  · show (0 : ℂ) + 0 = ((0 : ℤ) : ℂ)
    norm_num
  · show (0 : ℂ) + 0 = ((0 : ℤ) : ℂ)
    norm_num

theorem rhoC_eq_rhoTab
    (M : SL2) : rhoC (mkL M) = rhoTab (repIdx M) := by
  rw [classFn_mkL rhoC_mem M]
  exact rhoC_repList _

theorem lamC_eq_lamTab
    (M : SL2) : lamC (mkL M) = lamTab (repIdx M) := by
  rw [classFn_mkL lamC_mem M]
  exact lamC_repList _

theorem rhoC_sigma
    (M : SL2) : rhoC (mkL (sigmaAut M)) = rhoC (mkL M) := by
  rw [rhoC_eq_rhoTab, rhoC_eq_rhoTab, repIdx_sigma, rhoTab_classSwap]

theorem lam_sum_sigma (M : SL2) :
    lamC (mkL M) + lamC (mkL (sigmaAut M)) = (muTab (repIdx M) : ℂ) := by
  rw [lamC_eq_lamTab, lamC_eq_lamTab, repIdx_sigma, lamTab_add_classSwap]

namespace Tables

theorem conj_zeta9 : starRingEnd ℂ zeta9 = zeta9⁻¹ := by
  have h : ‖zeta9‖ = 1 := Complex.norm_eq_one_of_pow_eq_one zeta9_pow_five (by norm_num)
  have h2 : zeta9 * starRingEnd ℂ zeta9 = 1 := by
    rw [Complex.mul_conj', h]; norm_num
  exact eq_inv_of_mul_eq_one_right h2

end Tables

open Tables

theorem conj_r : starRingEnd ℂ r = r := by
  rw [r_eq, map_neg, map_add, map_pow, conj_zeta9, zeta9_inv]
  linear_combination (-zeta9 * (zeta9 ^ 10 + zeta9 ^ 5 + 1)) * zeta9_pow_five

open Tables

theorem rhoTab_conj (j : Fin 7) : starRingEnd ℂ (rhoTab j) = rhoTab j := by
  fin_cases j
  · show starRingEnd ℂ (8 : ℂ) = 8
    exact map_ofNat _ 8
  · show starRingEnd ℂ (-1 : ℂ) = -1
    rw [map_neg, map_one]
  · show starRingEnd ℂ (-1 : ℂ) = -1
    rw [map_neg, map_one]
  · show starRingEnd ℂ (0 : ℂ) = 0
    exact map_zero _
  · show starRingEnd ℂ (0 : ℂ) = 0
    exact map_zero _
  · exact conj_r
  · show starRingEnd ℂ (1 - r) = 1 - r
    rw [map_sub, map_one, conj_r]

namespace Tables

theorem repIdx_eq_zero_iff_aux :
    ∀ M ∈ allSL2, (repIdx M = 0 ↔ M = 1 ∨ M = minusOne) :=
  Certificates.certificate5102.2.2.2.2.2.2.2.2.1

end Tables

open Tables

theorem repIdx_eq_zero_iff
    (M : SL2) : repIdx M = 0 ↔ M = 1 ∨ M = minusOne :=
  repIdx_eq_zero_iff_aux M (mem_allSL2 M)

end CFSG.GH74.GLS.Stage4.Q9
