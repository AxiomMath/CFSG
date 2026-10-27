module

public import CFSG.ClassicalInvolution.Q3.Q3PPFundPSL3
public import CFSG.ClassicalInvolution.AschTight.S19KOutU
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryModelOuterTwoPart
public import CFSG.ClassicalInvolution.AschTight.S19KUniStd

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3PP

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Q3.Q3NM CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Disconnected.AschTight.S19K CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits
open scoped MatrixGroups

abbrev F9 : Type := GaloisField 3 (2 * 1)

abbrev SU3 : Type := Su F9 3 1 3

theorem card_F9 : Nat.card F9 = (3 ^ 1) ^ 2 :=
  CFSG.LieType.Universal.card_galoisField_two_mul 3 1 le_rfl

theorem two_ne_zero_F9 : (2 : F9) ≠ 0 :=
  Models.two_ne_zero_of_charP_ne_two (K := F9) (p := 3) (by norm_num)

noncomputable abbrev rootSU2₃ : Subgroup SU3 := rootSU2 F9 3 1 (n := 3) (by norm_num)

noncomputable abbrev rootInvSU₃ : SU3 := rootInvSU F9 3 1 (n := 3) (by norm_num)

theorem isBlockScalar_of_commutesSU {g : SU3} (hg : ∀ r ∈ rootSU2₃, g * r = r * g) :
    IsBlockScalar (suMat g) :=
  isBlockScalar_of_mem_centralizerU card_F9 (by norm_num) (by norm_num)
    (Subgroup.mem_centralizer_iff.mpr fun r hr => (hg r hr).symm)

theorem rootInvSU₃_mul_self : rootInvSU₃ * rootInvSU₃ = 1 :=
  suMat_injective (by rw [suMat_mul, suMat_one, suMat_rootInvSU]; exact negBlock_mul_self 3 0)

theorem suMat_rootInvSU₃ : suMat rootInvSU₃ = !![-1, 0, 0; 0, -1, 0; 0, 0, 1] :=
  coe_rootInvSU_three

theorem rootInvSU₃_ne_one : rootInvSU₃ ≠ 1 := by
  intro h
  have h1 := congrFun (congrFun (congrArg suMat h) 0) 0
  rw [suMat_rootInvSU₃, suMat_one] at h1
  have h3 : (-1 : F9) = 1 := by simpa using h1
  apply two_ne_zero_F9
  linear_combination -h3

theorem eq_one_or_rootInvSU₃_of_commutes {g : SU3} (hg : ∀ r ∈ rootSU2₃, g * r = r * g)
    (hg2 : g * g = 1) : g = 1 ∨ g = rootInvSU₃ := by
  have hsq : suMat g * suMat g = 1 := by rw [← suMat_mul, hg2, suMat_one]
  rcases isBlockScalar_sq_eq_one (isBlockScalar_of_commutesSU hg) (det_suMat g) hsq with h | h
  · left
    exact suMat_injective (by rw [h, suMat_one])
  · right
    exact suMat_injective (by rw [h, suMat_rootInvSU₃])

theorem center_su3_eq_bot : Subgroup.center SU3 = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 3 1 F9 :=
    ⟨Fact.out, le_rfl, by rw [card_F9, ← pow_mul, mul_comm]⟩
  obtain ⟨a, ha⟩ := ModelFacts.UnitaryAut.eq_smul_one_of_commute h (by norm_num) (le_refl 3)
    (((z : SU3) : GL (Fin 3) F9) : Matrix (Fin 3) (Fin 3) F9) fun y hy => by
      have hy' : y ∈ SUid (unitaryInvolution F9 3 1) 3 := by
        rw [SUid_eq_statedSU card_F9]; exact hy
      have h1 := Subgroup.mem_center_iff.mp hz ⟨y, hy'⟩
      have h2 := congrArg (fun w : SU3 => ((w : GL (Fin 3) F9) : Matrix (Fin 3) (Fin 3) F9)) h1
      simp only [Subgroup.coe_mul, Units.val_mul] at h2
      exact h2.symm
  have hdet : (a • (1 : Matrix (Fin 3) (Fin 3) F9)).det = 1 := by
    rw [← ha]; exact det_suMat z
  have ha3 : a ^ 3 = 1 := by simpa using hdet
  have : Fintype F9 := Fintype.ofFinite F9
  have hcard : Fintype.card F9 = 9 := by
    rw [← Nat.card_eq_fintype_card, card_F9]; norm_num
  have ha9 : a ^ 9 = a := by simpa [hcard] using FiniteField.pow_card a
  have ha1 : a = 1 := by
    rw [← ha9, show (9 : ℕ) = 3 * 3 from rfl, pow_mul, ha3, one_pow]
  rw [Subgroup.mem_bot]
  exact suMat_injective (by rw [suMat_one]; rw [show suMat z = a • 1 from ha, ha1, one_smul])

noncomputable abbrev J3GL : GL (Fin 3) F9 :=
  Matrix.SpecialLinearGroup.toGL (J3 F9)

theorem J3GL_mem_isomU : J3GL ∈ isomU F9 3 1 := by
  show conjTr (unitaryInvolution F9 3 1) ((J3GL : GL (Fin 3) F9) : Matrix (Fin 3) (Fin 3) F9) *
    ((J3GL : GL (Fin 3) F9) : Matrix (Fin 3) (Fin 3) F9) = 1
  rw [show ((J3GL : GL (Fin 3) F9) : Matrix (Fin 3) (Fin 3) F9) =
    ((J3 F9 : SL(3, F9)) : Matrix (Fin 3) (Fin 3) F9) from rfl, coe_J3]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [conjTr, Matrix.mul_apply, Fin.sum_univ_three]

theorem toGL_gam (x : SL(3, F9)) :
    Matrix.SpecialLinearGroup.toGL (gam F9 x) = invTr (Matrix.SpecialLinearGroup.toGL x) := by
  apply Units.ext
  rw [coe_invTr, ← map_inv Matrix.SpecialLinearGroup.toGL x]
  rfl

theorem toGL_gam' (x : SL(3, F9)) :
    Matrix.SpecialLinearGroup.toGL (gam' F9 x) =
      J3GL * invTr (Matrix.SpecialLinearGroup.toGL x) * J3GL⁻¹ := by
  rw [← toGL_gam, ← map_inv Matrix.SpecialLinearGroup.toGL (J3 F9),
    ← map_mul, ← map_mul]
  rfl

theorem toGL_suToSL (a : SU3) :
    Matrix.SpecialLinearGroup.toGL (suToSL (unitaryInvolution F9 3 1) 3 a) =
      ((a : SUid (unitaryInvolution F9 3 1) 3) : GL (Fin 3) F9) :=
  Units.ext rfl

theorem toGL_gam'_suToSL_mem (a : SU3) :
    Matrix.SpecialLinearGroup.toGL (gam' F9 (suToSL (unitaryInvolution F9 3 1) 3 a)) ∈
      SUid (unitaryInvolution F9 3 1) 3 := by
  have haI : ((a : SUid (unitaryInvolution F9 3 1) 3) : GL (Fin 3) F9) ∈ isomU F9 3 1 :=
    (mem_SUid.mp a.2).2
  have hI : Matrix.SpecialLinearGroup.toGL (gam' F9 (suToSL (unitaryInvolution F9 3 1) 3 a)) ∈
      isomU F9 3 1 := by
    rw [toGL_gam', toGL_suToSL]
    exact (isomU F9 3 1).mul_mem ((isomU F9 3 1).mul_mem J3GL_mem_isomU
      (invTr_mem_isomU card_F9 haI)) ((isomU F9 3 1).inv_mem J3GL_mem_isomU)
  exact mem_SUid.mpr ⟨(gam' F9 (suToSL (unitaryInvolution F9 3 1) 3 a)).2, hI⟩

@[expose] noncomputable def suGamHom : SU3 →* SU3 :=
  (Matrix.SpecialLinearGroup.toGL.comp ((gam' F9 : MulAut SL(3, F9)).toMonoidHom.comp
    (suToSL (unitaryInvolution F9 3 1) 3))).codRestrict (SUid (unitaryInvolution F9 3 1) 3)
    toGL_gam'_suToSL_mem

theorem suGamHom_injective : Function.Injective suGamHom := by
  intro a b hab
  have h1 : Matrix.SpecialLinearGroup.toGL (gam' F9 (suToSL (unitaryInvolution F9 3 1) 3 a)) =
      Matrix.SpecialLinearGroup.toGL (gam' F9 (suToSL (unitaryInvolution F9 3 1) 3 b)) :=
    congrArg Subtype.val hab
  exact suToSL_injective ((gam' F9).injective (Matrix.SpecialLinearGroup.toGL_injective h1))

@[expose] noncomputable def suGam : MulAut SU3 :=
  MulEquiv.ofBijective suGamHom (Finite.injective_iff_bijective.mp suGamHom_injective)

theorem suToSL_suGam (a : SU3) :
    suToSL (unitaryInvolution F9 3 1) 3 (suGam a) =
      gam' F9 (suToSL (unitaryInvolution F9 3 1) 3 a) :=
  Matrix.SpecialLinearGroup.toGL_injective (Units.ext rfl)

theorem suToSL_rootInvSU₃ :
    suToSL (unitaryInvolution F9 3 1) 3 rootInvSU₃ = rootInv₃ F9 := by
  apply Subtype.ext
  rw [coe_suToSL, suMat_rootInvSU, coe_rootInv]

theorem suGam_apply_of_mem {r : SU3} (hr : r ∈ rootSU2₃) : suGam r = r := by
  obtain ⟨B, rfl⟩ := hr
  apply suToSL_injective
  rw [suToSL_suGam, suToSL_blockEmb]
  exact gam'_blockSL _

theorem suGam_sq : suGam * suGam = MulAut.conj rootInvSU₃ := by
  refine MulEquiv.ext fun a => suToSL_injective ?_
  show suToSL (unitaryInvolution F9 3 1) 3 (suGam (suGam a)) =
    suToSL (unitaryInvolution F9 3 1) 3 (rootInvSU₃ * a * rootInvSU₃⁻¹)
  rw [suToSL_suGam, suToSL_suGam, map_mul, map_mul, map_inv, suToSL_rootInvSU₃]
  exact congrArg (fun φ : MulAut SL(3, F9) => φ (suToSL (unitaryInvolution F9 3 1) 3 a)) gam'_sq

theorem suGam_eq_inv_of_commutes {g : SU3} (hg : ∀ r ∈ rootSU2₃, g * r = r * g) :
    suGam g = g⁻¹ := by
  apply suToSL_injective
  rw [suToSL_suGam, map_inv]
  refine gam'_eq_inv_of_isBlockScalar ?_
  rw [← map_inv, coe_suToSL]
  refine isBlockScalar_of_commutesSU fun r hr => ?_
  have := hg r hr
  calc g⁻¹ * r = g⁻¹ * (r * g) * g⁻¹ := by group
    _ = g⁻¹ * (g * r) * g⁻¹ := by rw [this]
    _ = r * g⁻¹ := by group

theorem eq_one_or_conj_of_fixes_su3 (hout : OutOne SU3) {ρ : MulAut SU3} (hρ2 : ρ * ρ = 1)
    {g₀ : SU3} (hρR : ∀ r ∈ conjSub g₀ rootSU2₃, ρ r = r) :
    ρ = 1 ∨ ∃ s : SU3, s * s = 1 ∧ s ≠ 1 ∧ ρ = MulAut.conj s := by
  obtain ⟨c, hc⟩ : ∃ c : MulAut SU3, c = MulAut.conj g₀ := ⟨_, rfl⟩
  have hcr : ∀ x, c x = g₀ * x * g₀⁻¹ := fun x => by rw [hc]; rfl
  obtain ⟨ρ', hρ'⟩ : ∃ ρ' : MulAut SU3, ρ' = c⁻¹ * ρ * c := ⟨_, rfl⟩
  have hρ'R : ∀ r ∈ rootSU2₃, ρ' r = r := by
    intro r hr
    have h1 : ρ (c r) = c r := by rw [hcr]; exact hρR _ (conj_mem_conjSub hr)
    rw [hρ']
    show c⁻¹ (ρ (c r)) = r
    rw [h1]
    exact MulAut.inv_apply_self _ c r
  have hρ'2 : ρ' * ρ' = 1 := by
    calc ρ' * ρ' = c⁻¹ * (ρ * ρ) * c := by rw [hρ']; group
      _ = 1 := by rw [hρ2]; group
  have hk := eq_one_or_conj_of_invol center_su3_eq_bot hout (R := rootSU2₃) (t := rootInvSU₃)
    rootInvSU₃_mul_self rootInvSU₃_ne_one
    (fun g hg hg2 => eq_one_or_rootInvSU₃_of_commutes hg hg2) suGam
    (fun r hr => suGam_apply_of_mem hr) suGam_sq
    (fun g hg => suGam_eq_inv_of_commutes hg) ρ' hρ'2 hρ'R
  have hρ : ρ = c * ρ' * c⁻¹ := by rw [hρ']; group
  rcases hk with h | h
  · left
    rw [hρ, h, mul_one c, mul_inv_cancel]
  · right
    refine ⟨g₀ * rootInvSU₃ * g₀⁻¹, ?_, ?_, ?_⟩
    · calc g₀ * rootInvSU₃ * g₀⁻¹ * (g₀ * rootInvSU₃ * g₀⁻¹)
          = g₀ * (rootInvSU₃ * rootInvSU₃) * g₀⁻¹ := by group
        _ = 1 := by rw [rootInvSU₃_mul_self]; group
    · intro h1
      apply rootInvSU₃_ne_one
      calc rootInvSU₃ = g₀⁻¹ * (g₀ * rootInvSU₃ * g₀⁻¹) * g₀ := by group
        _ = 1 := by rw [h1]; group
    · rw [hρ, h, hc, map_mul, map_mul, map_inv]

theorem statedLieAdmissible_psu3 : StatedLieAdmissible .PSU 3 3 1 :=
  ⟨Nat.prime_three, le_rfl, le_rfl, by decide⟩

theorem fixedOddFreeFund_psu3 : FixedOddFreeFund (CompData.model .PSU 3) := by
  have hadm := statedLieAdmissible_psu3
  obtain ⟨e, he⟩ := RouteD.psu_model_equiv (p := 3) (f := 1) (by norm_num) hadm
  have hZ : Subgroup.center (CompData.model .PSU 3).G = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have h1 : e x ∈ Subgroup.center SU3 := by
      rw [← Subgroup.map_center_eq e]
      exact ⟨x, hx, rfl⟩
    rw [center_su3_eq_bot, Subgroup.mem_bot] at h1
    exact Subgroup.mem_bot.mpr (e.injective (by rw [h1, map_one]))
  refine fixedOddFreeFund_of_center_eq_bot hZ ?_
  have hT : StatedClassicalModel ((CompData.model .PSU 3).G ⧸
      Subgroup.center (CompData.model .PSU 3).G) .PSU 3 3 1 :=
    statedClassicalModel_center_quotient hadm card_F9
  have hcard := (CFSG.LocalAnalysis.ComponentInitial.unitary_model_outer_two_part_bound _ 3 3 1
    hT).2.2.1
  have hOT : OutOne ((CompData.model .PSU 3).G ⧸ Subgroup.center (CompData.model .PSU 3).G) :=
    OutOne.of_card_dvd_two (by rw [hcard]; norm_num)
  have hOutS : OutOne SU3 := OutOne.of_mulEquiv e (OutOne.of_center_eq_bot hZ hOT)
  have hsu : ∀ ρ : MulAut SU3, ρ * ρ = 1 →
      (∃ R ∈ longRootSetU (K := F9) (p := 3) (f := 1) (by norm_num : 2 ≤ 3),
        ∀ r ∈ R, ρ r = r) →
      ρ = 1 ∨ ∃ s : SU3, s * s = 1 ∧ s ≠ 1 ∧ ρ = MulAut.conj s := by
    intro ρ hρ2 ⟨R, hR, hρR⟩
    obtain ⟨g₀, rfl⟩ := (mem_longRootSetU_iff (by norm_num)).mp hR
    exact eq_one_or_conj_of_fixes_su3 hOutS hρ2 (g₀ := g₀) hρR
  have hcl := inv_classification_transport e (fun R hR => (he R).mp hR) hsu
  have hinv : ∃ x : (CompData.model .PSU 3).G, orderOf x = 2 :=
    ⟨e.symm rootInvSU₃, by
      rw [MulEquiv.orderOf_eq]
      exact orderOf_eq_prime (by rw [pow_two]; exact rootInvSU₃_mul_self) rootInvSU₃_ne_one⟩
  intro ρ hρ2 hfix
  rcases hcl ρ hρ2 hfix with h | ⟨s, hs2, hs1, hs⟩
  · exact oddCoreIn_fixed_eq_bot_of_model (t := .PSU) (n := 3) trivial hadm (Or.inl h) hinv
  · have hs' : orderOf s = 2 := orderOf_eq_prime (by rw [pow_two]; exact hs2) hs1
    exact oddCoreIn_fixed_eq_bot_of_model (t := .PSU) (n := 3) trivial hadm
      (Or.inr ⟨s, hs', hs⟩) hinv

end CFSG.ClassicalInvolution.Q3.Q3PP
