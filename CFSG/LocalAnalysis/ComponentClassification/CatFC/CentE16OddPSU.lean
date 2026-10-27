module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentE16Core
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentE16ArithLU
public import CFSG.RankThree.Classical.SteinbergBJUnitaryThreeInvolutions

public section

namespace CFSG.ComponentClassification.CatFC

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.Classical
open Matrix


@[expose] noncomputable def e16DiagGL {F : Type} [Field F] (ω : Fˣ) : GL (Fin 3) F :=
  ⟨diagonal ![(ω : F), ((ω⁻¹ : Fˣ) : F), 1], diagonal ![((ω⁻¹ : Fˣ) : F), (ω : F), 1], by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp, by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp⟩

theorem coe_e16DiagGL {F : Type} [Field F] (ω : Fˣ) :
    ((e16DiagGL ω : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      diagonal ![(ω : F), ((ω⁻¹ : Fˣ) : F), 1] := rfl

theorem e16DiagGL_mem {p f : ℕ} {F : Type} [Field F] (hU : UnitaryFieldData p f F) (ω : Fˣ)
    (hω : hU.bar (ω : F) = ((ω⁻¹ : Fˣ) : F)) : e16DiagGL ω ∈ unitarySU p f F 3 := by
  rw [mem_unitarySU_iff hU, coe_e16DiagGL]
  refine ⟨?_, ?_⟩
  · rw [det_diagonal, Fin.prod_univ_three]
    simp
  · rw [diagonal_map (map_zero hU.bar), diagonal_transpose, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    fin_cases i
    · simp [hω]
    · simp [hω]
    · simp

theorem e16DiagGL_commute {p f : ℕ} {F : Type} [Field F] (hU : UnitaryFieldData p f F) (ω : Fˣ)
    (hω : hU.bar (ω : F) = ((ω⁻¹ : Fˣ) : F)) :
    (⟨e16DiagGL ω, e16DiagGL_mem hU ω hω⟩ : unitarySU p f F 3) * unitaryInvT hU =
      unitaryInvT hU * ⟨e16DiagGL ω, e16DiagGL_mem hU ω hω⟩ := by
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, coe_unitaryInvT]
  change diagonal ![(ω : F), ((ω⁻¹ : Fˣ) : F), 1] * negNegOneDiag F =
    negNegOneDiag F * diagonal ![(ω : F), ((ω⁻¹ : Fˣ) : F), 1]
  rw [negNegOneDiag, diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

theorem e16DiagGL_pow {p f : ℕ} {F : Type} [Field F] (hU : UnitaryFieldData p f F) (ω : Fˣ)
    (hω : hU.bar (ω : F) = ((ω⁻¹ : Fˣ) : F)) {r : ℕ} (hr : ω ^ r = 1) :
    (⟨e16DiagGL ω, e16DiagGL_mem hU ω hω⟩ : unitarySU p f F 3) ^ r = 1 := by
  apply Subtype.ext
  apply Units.ext
  rw [SubmonoidClass.coe_pow, Units.val_pow_eq_pow_val, OneMemClass.coe_one, Units.val_one]
  change (diagonal ![(ω : F), ((ω⁻¹ : Fˣ) : F), 1]) ^ r = 1
  rw [diagonal_pow, ← diagonal_one]
  congr 1
  funext i
  have h1 : (ω : F) ^ r = 1 := by
    have := congrArg (fun u : Fˣ => (u : F)) hr
    simpa using this
  fin_cases i
  · simpa using h1
  · simp [inv_pow, h1]
  · simp

theorem e16DiagGL_proj_ne_one {p f : ℕ} {F : Type} [Field F] (hU : UnitaryFieldData p f F)
    (ω : Fˣ) (hω : hU.bar (ω : F) = ((ω⁻¹ : Fˣ) : F)) (hne : ω ≠ ω⁻¹) :
    unitaryProj hU 3 ⟨e16DiagGL ω, e16DiagGL_mem hU ω hω⟩ ≠ 1 := by
  intro h
  rw [← MonoidHom.mem_ker, ker_unitaryProj, mem_unitaryScalars] at h
  obtain ⟨c, -, -, hc⟩ := h
  have e0 := congrArg (fun M : GL (Fin 3) F => (M : Matrix (Fin 3) (Fin 3) F) 0 0) hc
  have e1 := congrArg (fun M : GL (Fin 3) F => (M : Matrix (Fin 3) (Fin 3) F) 1 1) hc
  simp only [coe_e16DiagGL, GeneralLinearGroup.coe_scalar, scalar_apply,
    diagonal_apply_eq] at e0 e1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at e0 e1
  apply hne
  apply Units.ext
  rw [e0, e1]

theorem e16_psu3_odd_commuting {p f : ℕ} {F : Type} [Field F] (hU : UnitaryFieldData p f F)
    (hq4 : (p ^ f) % 4 = 1) (hq3 : 3 ≤ p ^ f) :
    ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ ∃ y : unitaryPSU hU 3, orderOf y = r ∧
      y * unitaryProj hU 3 (unitaryInvT hU) = unitaryProj hU 3 (unitaryInvT hU) * y := by
  classical
  haveI : Finite F := hU.finite
  haveI : Fintype F := Fintype.ofFinite F
  obtain ⟨q, hq⟩ : ∃ q, q = p ^ f := ⟨_, rfl⟩
  rw [← hq] at hq4 hq3
  have hmod : (q + 1) % 4 = 2 := by omega
  have hodd : ((q + 1) / 2) % 2 = 1 := by omega
  have hne1 : (q + 1) / 2 ≠ 1 := by omega
  obtain ⟨r, hr, hrq⟩ := Nat.exists_prime_and_dvd hne1
  have hr2 : r ≠ 2 := by
    rintro rfl
    obtain ⟨m, hm⟩ := hrq
    omega
  have hrq1 : r ∣ q + 1 :=
    hrq.trans (Nat.div_dvd_of_dvd (by omega : 2 ∣ q + 1))
  haveI : Fact r.Prime := ⟨hr⟩
  have hcardF : Fintype.card F = q ^ 2 := by
    rw [← Nat.card_eq_fintype_card, hU.card, hq, ← pow_mul, mul_comm]
  have hdvd : r ∣ Fintype.card Fˣ := by
    rw [Fintype.card_units, hcardF]
    obtain ⟨k, rfl⟩ : ∃ k, q = k + 1 := ⟨q - 1, by omega⟩
    have h1 : (k + 1) ^ 2 - 1 = (k + 1 + 1) * k := by
      rw [Nat.sub_eq_iff_eq_add (Nat.one_le_pow 2 (k + 1) (by omega))]
      ring
    rw [h1]
    exact Dvd.dvd.mul_right hrq1 _
  obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card r hdvd
  have hωr : ω ^ r = 1 := by rw [← hω]; exact pow_orderOf_eq_one ω
  have hωq1 : ω ^ (q + 1) = 1 := orderOf_dvd_iff_pow_eq_one.1 (hω ▸ hrq1)
  have hωq : ω ^ q = ω⁻¹ := by
    rw [pow_succ] at hωq1
    exact eq_inv_of_mul_eq_one_left hωq1
  have hbar : hU.bar (ω : F) = ((ω⁻¹ : Fˣ) : F) := by
    rw [hU.bar_apply, ← hq, ← Units.val_pow_eq_pow_val, hωq]
  have hne : ω ≠ ω⁻¹ := by
    intro h
    have h2 : ω ^ 2 = 1 := by
      rw [sq]
      exact mul_eq_one_iff_eq_inv.2 h
    have : r ∣ 2 := hω ▸ orderOf_dvd_of_pow_eq_one h2
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 this)
  refine ⟨r, hr, hr2, unitaryProj hU 3 ⟨e16DiagGL ω, e16DiagGL_mem hU ω hbar⟩, ?_, ?_⟩
  · refine orderOf_eq_prime ?_ (e16DiagGL_proj_ne_one hU ω hbar hne)
    rw [← map_pow, e16DiagGL_pow hU ω hbar hωr, map_one]
  · rw [← map_mul, ← map_mul, e16DiagGL_commute hU ω hbar]

theorem e16_orderOf_conj {G : Type*} [Group G] (c y : G) : orderOf (c⁻¹ * y * c) = orderOf y := by
  have := orderOf_injective (MulAut.conj c⁻¹).toMonoidHom (MulAut.conj c⁻¹).injective y
  simpa [MulAut.conj_apply] using this

theorem e16_false_psu_three (hO : LieOrderFormulasInput) {K : Type} [Group K] [Finite K]
    (D : CatE16Data K) {f : ℕ} (hadm : StatedLieAdmissible .PSU 3 5 f)
    (hmod : LieModel K .PSU 3 5 f) : False := by
  have hq4 : (5 ^ f) % 4 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  have hq3 : 3 ≤ 5 ^ f := by
    calc 3 ≤ 5 ^ 1 := by norm_num
      _ ≤ 5 ^ f := Nat.pow_le_pow_right (by norm_num) hadm.2.1
  obtain ⟨-, hord, -⟩ := hO K .PSU 3 5 f hadm hmod
  have hdivpos : 0 < lieOrderDivisor .PSU 3 (5 ^ f) := by
    simp only [lieOrderDivisor]
    exact Nat.gcd_pos_of_pos_left _ (by norm_num)
  have h16 : 2 ^ 4 ∣ Nat.card K := by
    have h := e16_arith_psu_three hq4
    rw [← hord] at h
    exact Nat.dvd_of_mul_dvd_mul_right hdivpos h
  have h16Q := (D.two_pow_dvd_card_iff 4).1 h16
  have hpos : 0 < Nat.card (Subgroup.centralizer ({D.κ} : Set K)) := Nat.card_pos
  have hQ16 : Nat.card (Subgroup.centralizer ({D.κ} : Set K)) = 16 := by
    have h1 := Nat.le_of_dvd hpos h16Q
    have h2 := D.hQ
    omega
  obtain ⟨⟨hp, hf, -, -⟩, F, _, _, hF, ⟨e⟩⟩ := LieModel.statedClassicalModel hmod (by decide)
  have hU : UnitaryFieldData 5 f F := ⟨hp, hf, by rw [hF]; ring⟩
  let φ : K ≃* unitaryPSU hU 3 := e.trans (unitaryPSUEquiv hU (by norm_num)).symm
  have hκ'2 : orderOf (φ D.κ) = 2 := by rw [MulEquiv.orderOf_eq]; exact D.hκ2
  obtain ⟨r, hr, hr2, y, hy, hcomm⟩ := e16_psu3_odd_commuting hU hq4 hq3
  obtain ⟨c, hc⟩ := isConj_iff.1 (isConj_unitaryProj_unitaryInvT hU (by norm_num) hκ'2)
  have hκ'eq : φ D.κ = c⁻¹ * unitaryProj hU 3 (unitaryInvT hU) * c := by
    rw [← hc]
    group
  have hy'comm : (c⁻¹ * y * c) * φ D.κ = φ D.κ * (c⁻¹ * y * c) := by
    rw [hκ'eq]
    calc c⁻¹ * y * c * (c⁻¹ * unitaryProj hU 3 (unitaryInvT hU) * c)
        = c⁻¹ * (y * unitaryProj hU 3 (unitaryInvT hU)) * c := by group
      _ = c⁻¹ * (unitaryProj hU 3 (unitaryInvT hU) * y) * c := by rw [hcomm]
      _ = c⁻¹ * unitaryProj hU 3 (unitaryInvT hU) * c * (c⁻¹ * y * c) := by group
  have hzmem : φ.symm (c⁻¹ * y * c) ∈ Subgroup.centralizer ({D.κ} : Set K) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply φ.injective
    have h1 : φ (D.κ * φ.symm (c⁻¹ * y * c)) = φ D.κ * (c⁻¹ * y * c) := by
      rw [map_mul, MulEquiv.apply_symm_apply]
    have h2 : φ (φ.symm (c⁻¹ * y * c) * D.κ) = (c⁻¹ * y * c) * φ D.κ := by
      rw [map_mul, MulEquiv.apply_symm_apply]
    rw [h1, h2]
    exact hy'comm
  have hzord : orderOf (φ.symm (c⁻¹ * y * c)) = r := by
    rw [MulEquiv.orderOf_eq, e16_orderOf_conj, hy]
  have hdvd : orderOf (⟨φ.symm (c⁻¹ * y * c), hzmem⟩ :
      Subgroup.centralizer ({D.κ} : Set K)) ∣ Nat.card (Subgroup.centralizer ({D.κ} : Set K)) :=
    orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk, hzord, hQ16] at hdvd
  have : r ∣ 2 ^ 4 := by simpa using hdvd
  have hr2' : r ∣ 2 := hr.dvd_of_dvd_pow this
  exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 hr2')

end CFSG.ComponentClassification.CatFC
