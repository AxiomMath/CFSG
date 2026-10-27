module

public import CFSG.RankThree.SubgroupLists.UnitaryThreeFamily
public import CFSG.GH74.KGroups.L3EpsBlockLin

public section

namespace CFSG.GH74.KGroups.L3Eps.Uni

open Matrix Subgroup CFSG CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.SubgroupLists CFSG.Assembly.LowTwoRank
open scoped MatrixGroups commutatorElement

variable {p f : ℕ} {F : Type} [Field F]

@[expose] noncomputable def levU (hq1 : 1 ≤ p ^ f) : ↥(unitarySU p f F 2) →* ↥(unitarySU p f F 3) :=
  (blockGL3.comp (unitarySU p f F 2).subtype).codRestrict (unitarySU p f F 3)
    (fun A => map_blockGL3_statedSU_le hq1 ⟨A, A.2, rfl⟩)

theorem coe_levU (hq1 : 1 ≤ p ^ f) (A : ↥(unitarySU p f F 2)) :
    (((levU hq1 A : ↥(unitarySU p f F 3)) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      leviMat (((A : GL (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F) := rfl

@[expose] noncomputable def dU (hq : Odd (p ^ f)) : ↥(unitarySU p f F 3) := negDiagSU3 hq

theorem coe_dU (hq : Odd (p ^ f)) :
    (((dU (p := p) (f := f) (F := F) hq : ↥(unitarySU p f F 3)) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      diagonal ![-1, -1, 1] := rfl


theorem dNeg_coe_eq_diagonal : ((dNeg : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = diagonal ![-1, -1, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_dNeg]

@[expose, reducible] def matU {n : ℕ} (g : ↥(unitarySU p f F n)) : Matrix (Fin n) (Fin n) F :=
  ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)

theorem matU_mul {n : ℕ} (g g' : ↥(unitarySU p f F n)) : matU (g * g') = matU g * matU g' := rfl

theorem matU_one {n : ℕ} : matU (1 : ↥(unitarySU p f F n)) = 1 := rfl

theorem matU_ext {n : ℕ} {g g' : ↥(unitarySU p f F n)} (hg : matU g = matU g') : g = g' :=
  Subtype.ext (Units.ext hg)

section Cover

variable (h : UnitaryFieldData p f F) {K : Type*} [Group K] (θ : ↥(unitarySU p f F 3) →* K)

theorem theta_eq_iff (hker : θ.ker = unitaryScalars h 3) {g g' : ↥(unitarySU p f F 3)} :
    θ g = θ g' ↔ ∃ c : Fˣ, h.norm (c : F) = 1 ∧ c ^ 3 = 1 ∧
      matU g' = matU g * Matrix.scalar (Fin 3) (c : F) := by
  rw [← inv_mul_eq_one, ← map_inv, ← map_mul, ← MonoidHom.mem_ker, hker, mem_unitaryScalars]
  constructor
  · rintro ⟨c, hc, hc3, hg⟩
    refine ⟨c, hc, hc3, ?_⟩
    have h1 : (g' : GL (Fin 3) F) = (g : GL (Fin 3) F) * GeneralLinearGroup.scalar (Fin 3) c := by
      have := congrArg (fun x : GL (Fin 3) F => (g : GL (Fin 3) F) * x) hg
      simpa using this
    have := congrArg (fun x : GL (Fin 3) F => (x : Matrix (Fin 3) (Fin 3) F)) h1
    simpa [GeneralLinearGroup.coe_scalar] using this
  · rintro ⟨c, hc, hc3, hg⟩
    refine ⟨c, hc, hc3, ?_⟩
    have h1 : (g' : GL (Fin 3) F) = (g : GL (Fin 3) F) * GeneralLinearGroup.scalar (Fin 3) c := by
      apply Units.ext
      simpa [GeneralLinearGroup.coe_scalar] using hg
    rw [Subgroup.coe_mul, Subgroup.coe_inv, h1, inv_mul_cancel_left]


theorem matU_ne_zero {n : ℕ} [NeZero n] (g : ↥(unitarySU p f F n)) : matU g ≠ 0 := by
  intro h0
  have hdet := ((Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit (g : GL (Fin n) F))).ne_zero
  apply hdet
  rw [show ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 0 from h0]
  simp

theorem cen_lift (hker : θ.ker = unitaryScalars h 3) (hsurj : Function.Surjective θ) (h2 : (2 : F) ≠ 0)
    (hq : Odd (p ^ f)) {x : K} (hx : x ∈ Subgroup.centralizer ({θ (dU hq)} : Set K)) :
    ∃ g : ↥(unitarySU p f F 3), θ g = x ∧ g * dU hq = dU hq * g := by
  obtain ⟨g, rfl⟩ := hsurj x
  have hcomm : θ (g * dU hq) = θ (dU hq * g) := by
    rw [map_mul, map_mul]
    exact mem_centralizer_singleton_iff.1 hx
  obtain ⟨c, hc, hc3, hM⟩ := (theta_eq_iff h θ hker).1 hcomm
  have hc3' : (c : F) ^ 3 = 1 := by simpa using congrArg (fun u : Fˣ => (u : F)) hc3
  have hM' : ((dNeg : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) * matU g =
      (matU g * ((dNeg : SL(3, F)) : Matrix (Fin 3) (Fin 3) F)) * Matrix.scalar (Fin 3) (c : F) := by
    rw [dNeg_coe_eq_diagonal]
    simpa [matU_mul, coe_dU] using hM
  have hc1 := eq_one_of_dNeg_scalar h2 (matU_ne_zero g) hc3' hM'
  refine ⟨g, rfl, matU_ext ?_⟩
  rw [matU_mul, matU_mul]
  have := hM
  rw [matU_mul, matU_mul, hc1] at this
  simpa using this.symm

end Cover


section Commutant

theorem form_of_commute_levi {A : Matrix (Fin 3) (Fin 3) F} {l : F} (hl0 : l ≠ 0) (hl1 : l ≠ 1)
    (hl2 : l ^ 2 ≠ 1)
    (hD : A * leviMat !![l, 0; 0, l⁻¹] = leviMat !![l, 0; 0, l⁻¹] * A)
    (hJ : A * leviMat !![0, 1; -1, 0] = leviMat !![0, 1; -1, 0] * A) :
    A 0 1 = 0 ∧ A 1 0 = 0 ∧ A 0 2 = 0 ∧ A 1 2 = 0 ∧ A 2 0 = 0 ∧ A 2 1 = 0 ∧ A 0 0 = A 1 1 := by
  have e01 := congrFun (congrFun hD 0) 1
  have e10 := congrFun (congrFun hD 1) 0
  have e02 := congrFun (congrFun hD 0) 2
  have e20 := congrFun (congrFun hD 2) 0
  have e12 := congrFun (congrFun hD 1) 2
  have e21 := congrFun (congrFun hD 2) 1
  simp [leviMat, Matrix.mul_apply, Fin.sum_univ_three] at e01 e10 e02 e20 e12 e21
  have hlinv : l⁻¹ ≠ 1 := fun h => hl1 (by simpa using congrArg (fun x => x⁻¹) h)
  have hll : l⁻¹ - l ≠ 0 := by
    intro h
    apply hl2
    have : l⁻¹ = l := sub_eq_zero.1 h
    field_simp at this
    linear_combination -this
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (mul_eq_zero.1 (show A 0 1 * (l⁻¹ - l) = 0 by linear_combination e01)).resolve_right hll
  · exact (mul_eq_zero.1 (show A 1 0 * (l - l⁻¹) = 0 by linear_combination e10)).resolve_right
      (fun h => hll (by linear_combination -h))
  · exact (mul_eq_zero.1 (show A 0 2 * (1 - l) = 0 by linear_combination e02)).resolve_right
      (sub_ne_zero.2 (Ne.symm hl1))
  · exact (mul_eq_zero.1 (show A 1 2 * (1 - l⁻¹) = 0 by linear_combination e12)).resolve_right
      (sub_ne_zero.2 (Ne.symm hlinv))
  · exact (mul_eq_zero.1 (show A 2 0 * (l - 1) = 0 by linear_combination e20)).resolve_right
      (sub_ne_zero.2 hl1)
  · exact (mul_eq_zero.1 (show A 2 1 * (l⁻¹ - 1) = 0 by linear_combination e21)).resolve_right
      (sub_ne_zero.2 hlinv)
  · have e := congrFun (congrFun hJ 0) 1
    simp [leviMat, Matrix.mul_apply, Fin.sum_univ_three] at e
    linear_combination e

end Commutant


section TestElements

variable (h : UnitaryFieldData p f F)

@[expose] noncomputable def jU : ↥(unitarySU p f F 2) :=
  ⟨GeneralLinearGroup.mkOfDetNeZero !![0, 1; -1, 0] (by simp [Matrix.det_fin_two]),
    (mem_unitarySU_iff h).2 ⟨by simp [Matrix.det_fin_two], by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩⟩

theorem matU_jU : matU (jU h) = !![0, 1; -1, 0] := rfl

@[expose] noncomputable def dTestU {l : F} (hl0 : l ≠ 0) (hl : h.norm l = 1) : ↥(unitarySU p f F 2) :=
  ⟨GeneralLinearGroup.mkOfDetNeZero !![l, 0; 0, l⁻¹] (by simp [Matrix.det_fin_two, hl0]),
    (mem_unitarySU_iff h).2 ⟨by simp [Matrix.det_fin_two, hl0], by
      have hbar : h.bar l = l⁻¹ := by
        have : l * h.bar l = 1 := hl
        exact eq_inv_of_mul_eq_one_right this
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hbar, hl0]⟩⟩

theorem matU_dTestU {l : F} (hl0 : l ≠ 0) (hl : h.norm l = 1) :
    matU (dTestU h hl0 hl) = !![l, 0; 0, l⁻¹] := rfl

theorem exists_norm_one_ne (h5 : 5 ≤ p ^ f) :
    ∃ l : F, l ≠ 0 ∧ h.norm l = 1 ∧ l ≠ 1 ∧ l ^ 2 ≠ 1 := by
  have := h.finite
  have hcyc : IsCyclic Fˣ := inferInstance
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have hcard : Nat.card F = (p ^ f) ^ 2 := by rw [h.card, ← pow_mul, mul_comm]
  have hord : orderOf g = (p ^ f) ^ 2 - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, hcard]
  set q := p ^ f with hq
  have hq5 : 5 ≤ q := h5
  have hnorm : ∀ u : Fˣ, h.norm (u : F) = ((u ^ (q + 1) : Fˣ) : F) := fun u => by
    rw [h.norm_eq_pow, Units.val_pow_eq_pow_val]
  have hqq : (q - 1) * (q + 1) = q ^ 2 - 1 := by
    have h1 : 1 ≤ q := by omega
    have h2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
    zify [h1, h2]
    ring
  refine ⟨((g ^ (q - 1) : Fˣ) : F), (g ^ (q - 1)).ne_zero, ?_, ?_, ?_⟩
  · rw [hnorm, ← pow_mul, hqq, ← hord, pow_orderOf_eq_one, Units.val_one]
  · intro h1
    have h1' : g ^ (q - 1) = 1 := Units.ext h1
    have hdvd : q ^ 2 - 1 ∣ q - 1 := by
      rw [← hord]; exact orderOf_dvd_of_pow_eq_one h1'
    have hle := Nat.le_of_dvd (by omega) hdvd
    have hle' : (q - 1) * ((q - 1) + 2) ≤ q - 1 := by
      have : q + 1 = (q - 1) + 2 := by omega
      rw [← this, hqq]; exact hle
    have hm4 : 4 ≤ q - 1 := by omega
    generalize q - 1 = m at hle' hm4
    nlinarith
  · intro h1
    have h1' : g ^ (2 * (q - 1)) = 1 := by
      have : ((g ^ (q - 1) : Fˣ) ^ 2 : Fˣ) = 1 := Units.ext (by simpa using h1)
      rwa [← pow_mul, mul_comm] at this
    have hdvd : q ^ 2 - 1 ∣ 2 * (q - 1) := by
      rw [← hord]; exact orderOf_dvd_of_pow_eq_one h1'
    have hle := Nat.le_of_dvd (by omega) hdvd
    have hle' : (q - 1) * ((q - 1) + 2) ≤ 2 * (q - 1) := by
      have : q + 1 = (q - 1) + 2 := by omega
      rw [← this, hqq]; exact hle
    have hm4 : 4 ≤ q - 1 := by omega
    generalize q - 1 = m at hle' hm4
    nlinarith

end TestElements


section Block

variable (h : UnitaryFieldData p f F)

@[expose] def IsLevi (M : Matrix (Fin 3) (Fin 3) F) : Prop :=
  M 0 2 = 0 ∧ M 1 2 = 0 ∧ M 2 0 = 0 ∧ M 2 1 = 0

variable {h}

theorem isLevi_of_commute (h2 : (2 : F) ≠ 0) {M : Matrix (Fin 3) (Fin 3) F}
    (hM : M * diagonal ![-1, -1, 1] = diagonal ![-1, -1, 1] * M) : IsLevi M := by
  have e02 := congrFun (congrFun hM 0) 2
  have e12 := congrFun (congrFun hM 1) 2
  have e20 := congrFun (congrFun hM 2) 0
  have e21 := congrFun (congrFun hM 2) 1
  simp [Matrix.mul_apply, diagonal] at e02 e12 e20 e21
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (mul_eq_zero.1 (show (2 : F) * M 0 2 = 0 by linear_combination e02)).resolve_left h2
  · exact (mul_eq_zero.1 (show (2 : F) * M 1 2 = 0 by linear_combination e12)).resolve_left h2
  · exact (mul_eq_zero.1 (show (2 : F) * M 2 0 = 0 by linear_combination -e20)).resolve_left h2
  · exact (mul_eq_zero.1 (show (2 : F) * M 2 1 = 0 by linear_combination -e21)).resolve_left h2

theorem isLevi_mul {M N : Matrix (Fin 3) (Fin 3) F} (hM : IsLevi M) (hN : IsLevi N) :
    IsLevi (M * N) ∧ (M * N) 2 2 = M 2 2 * N 2 2 := by
  obtain ⟨a1, a2, a3, a4⟩ := hM
  obtain ⟨b1, b2, b3, b4⟩ := hN
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩ <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, a1, a2, a3, a4, b1, b2, b3, b4]

@[expose] def blkU (M : Matrix (Fin 3) (Fin 3) F) : Matrix (Fin 2) (Fin 2) F :=
  Matrix.of fun i j => M i.castSucc j.castSucc

theorem leviMat_blkU {M : Matrix (Fin 3) (Fin 3) F} (hM : IsLevi M) (h22 : M 2 2 = 1) :
    leviMat (blkU M) = M := by
  obtain ⟨a1, a2, a3, a4⟩ := hM
  ext i j
  fin_cases i <;> fin_cases j <;> simp [leviMat, blkU, a1, a2, a3, a4, h22]

theorem leviMat_injective :
    Function.Injective (leviMat : Matrix (Fin 2) (Fin 2) F → Matrix (Fin 3) (Fin 3) F) := by
  intro A B hAB
  ext i j
  have := congrFun (congrFun hAB (Fin.castSucc i)) (Fin.castSucc j)
  fin_cases i <;> fin_cases j <;> simpa [leviMat] using this

theorem leviMat_unitary (h : UnitaryFieldData p f F) (B : Matrix (Fin 2) (Fin 2) F) :
    ((leviMat B).map h.bar)ᵀ * leviMat B = leviMat ((B.map h.bar)ᵀ * B) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [leviMat, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three]

theorem isLevi_levU (hq1 : 1 ≤ p ^ f) (B : ↥(unitarySU p f F 2)) :
    IsLevi (matU (levU hq1 B)) ∧ matU (levU hq1 B) 2 2 = 1 := by
  rw [show matU (levU hq1 B) = leviMat (((B : GL (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F) from rfl]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩ <;> simp [leviMat]

theorem exists_levU (h : UnitaryFieldData p f F) (hq1 : 1 ≤ p ^ f) (g : ↥(unitarySU p f F 3))
    (hg : IsLevi (matU g)) (h22 : matU g 2 2 = 1) : ∃ B : ↥(unitarySU p f F 2), levU hq1 B = g := by
  have hgM := (mem_unitarySU_iff h).1 g.2
  have hL := leviMat_blkU hg h22
  have hdet : (blkU (matU g)).det = 1 := by rw [← det_leviMat, hL]; exact hgM.1
  have hunit : ((blkU (matU g)).map h.bar)ᵀ * blkU (matU g) = 1 := by
    apply leviMat_injective
    rw [← leviMat_unitary, hL, leviMat_one]
    exact hgM.2
  refine ⟨⟨GeneralLinearGroup.mkOfDetNeZero (blkU (matU g)) (by rw [hdet]; exact one_ne_zero),
    (mem_unitarySU_iff h).2 ⟨hdet, hunit⟩⟩, ?_⟩
  apply matU_ext
  exact hL

end Block


theorem two_ne_zero_of_odd_pow (h : UnitaryFieldData p f F) (hq : Odd (p ^ f)) : (2 : F) ≠ 0 := by
  intro h0
  have := h.charP
  have hp2 : p ∣ 2 := (CharP.cast_eq_zero_iff F p 2).1 (by exact_mod_cast h0)
  have hpp : p = 2 := (Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_two).1 hp2
  subst hpp
  obtain ⟨k, hk⟩ := hq
  have : 2 ∣ 2 ^ f := dvd_pow_self 2 (by have := h.one_le; omega)
  omega

theorem matU_levU (hq1 : 1 ≤ p ^ f) (B : ↥(unitarySU p f F 2)) :
    matU (levU hq1 B) = leviMat (((B : GL (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F) := rfl

theorem matU_dU (hq : Odd (p ^ f)) :
    matU (dU (p := p) (f := f) (F := F) hq) = diagonal ![-1, -1, 1] := rfl

section Centralizer

theorem isLevi_of_mem_centralizer (h : UnitaryFieldData p f F) (hq : Odd (p ^ f)) {g : ↥(unitarySU p f F 3)}
    (hg : g ∈ Subgroup.centralizer ({dU hq} : Set ↥(unitarySU p f F 3))) : IsLevi (matU g) := by
  have := mem_centralizer_singleton_iff.1 hg
  refine isLevi_of_commute (two_ne_zero_of_odd_pow h hq) ?_
  have h1 := congrArg matU this
  rw [matU_mul, matU_mul, matU_dU] at h1
  exact h1

theorem det_matU_eq_one (h : UnitaryFieldData p f F) (g : ↥(unitarySU p f F 3)) : (matU g).det = 1 :=
  ((mem_unitarySU_iff h).1 g.2).1

theorem matU_22_ne_zero (h : UnitaryFieldData p f F) (hq : Odd (p ^ f)) {g : ↥(unitarySU p f F 3)}
    (hg : g ∈ Subgroup.centralizer ({dU hq} : Set ↥(unitarySU p f F 3))) : matU g 2 2 ≠ 0 := by
  obtain ⟨a1, a2, a3, a4⟩ := isLevi_of_mem_centralizer h hq hg
  intro h0
  have := det_matU_eq_one h g
  rw [Matrix.det_fin_three] at this
  simp [a1, a2, a3, a4, h0] at this

@[expose] noncomputable def cenHomU (h : UnitaryFieldData p f F) (hq : Odd (p ^ f)) :
    ↥(Subgroup.centralizer ({dU hq} : Set ↥(unitarySU p f F 3))) →* Fˣ where
  toFun g := Units.mk0 (matU (g : ↥(unitarySU p f F 3)) 2 2) (matU_22_ne_zero h hq g.2)
  map_one' := Units.ext (by simp [matU_one])
  map_mul' g g' := Units.ext (by
    simp only [Units.val_mk0, Units.val_mul, Subgroup.coe_mul, matU_mul]
    exact (isLevi_mul (isLevi_of_mem_centralizer h hq g.2) (isLevi_of_mem_centralizer h hq g'.2)).2)

theorem cenHomU_apply (h : UnitaryFieldData p f F) (hq : Odd (p ^ f))
    (g : ↥(Subgroup.centralizer ({dU hq} : Set ↥(unitarySU p f F 3)))) :
    ((cenHomU h hq g : Fˣ) : F) = matU (g : ↥(unitarySU p f F 3)) 2 2 := rfl

theorem levU_mem_centralizer (hq : Odd (p ^ f)) (B : ↥(unitarySU p f F 2)) :
    levU hq.pos B ∈ Subgroup.centralizer ({dU hq} : Set ↥(unitarySU p f F 3)) := by
  rw [mem_centralizer_singleton_iff]
  apply matU_ext
  rw [matU_mul, matU_mul, matU_levU, matU_dU]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [leviMat, Matrix.mul_apply, diagonal]

theorem cenHomU_levU (h : UnitaryFieldData p f F) (hq : Odd (p ^ f)) (B : ↥(unitarySU p f F 2)) :
    cenHomU h hq ⟨levU hq.pos B, levU_mem_centralizer hq B⟩ = 1 := by
  apply Units.ext
  rw [cenHomU_apply]
  exact (isLevi_levU hq.pos B).2

theorem mem_range_levU_of_cenHomU (h : UnitaryFieldData p f F) (hq : Odd (p ^ f))
    (g : ↥(Subgroup.centralizer ({dU hq} : Set ↥(unitarySU p f F 3))))
    (hg : cenHomU h hq g = 1) : (g : ↥(unitarySU p f F 3)) ∈ (levU hq.pos).range := by
  have h22 : matU (g : ↥(unitarySU p f F 3)) 2 2 = 1 := by
    have := congrArg (fun u : Fˣ => (u : F)) hg
    simpa [cenHomU_apply] using this
  obtain ⟨B, hB⟩ := exists_levU h hq.pos g (isLevi_of_mem_centralizer h hq g.2) h22
  exact ⟨B, hB⟩

end Centralizer


@[expose] noncomputable def negI (h : UnitaryFieldData p f F) : ↥(unitarySU p f F 2) :=
  ⟨GeneralLinearGroup.mkOfDetNeZero (-1 : Matrix (Fin 2) (Fin 2) F) (by simp [Matrix.det_neg]),
    (mem_unitarySU_iff h).2 ⟨by simp [Matrix.det_neg], by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩⟩

theorem matU_negI (h : UnitaryFieldData p f F) : matU (negI h) = -1 := rfl

theorem levU_negI (h : UnitaryFieldData p f F) (hq : Odd (p ^ f)) : levU hq.pos (negI h) = dU hq := by
  apply matU_ext
  rw [matU_levU, matU_dU]
  show leviMat (-1 : Matrix (Fin 2) (Fin 2) F) = _
  ext i j
  fin_cases i <;> fin_cases j <;> simp [leviMat, diagonal]

theorem levU_injective (hq1 : 1 ≤ p ^ f) : Function.Injective (levU (p := p) (f := f) (F := F) hq1) := by
  intro B B' hB
  have h1 : leviMat (matU B) = leviMat (matU B') := by
    have := congrArg matU hB
    rwa [matU_levU, matU_levU] at this
  exact matU_ext (leviMat_injective h1)

structure IsCover (h : UnitaryFieldData p f F) {K : Type*} [Group K]
    (θ : ↥(unitarySU p f F 3) →* K) : Prop where
  surj : Function.Surjective θ
  ker : θ.ker = unitaryScalars h 3

section Cover2

variable (h : UnitaryFieldData p f F) {K : Type*} [Group K] {θ : ↥(unitarySU p f F 3) →* K}

theorem IsCover.levU_eq (hθ : IsCover h θ) (hq1 : 1 ≤ p ^ f) {B B' : ↥(unitarySU p f F 2)}
    (hB : θ (levU hq1 B) = θ (levU hq1 B')) : B = B' := by
  obtain ⟨c, -, -, hc⟩ := (theta_eq_iff h θ hθ.ker).1 hB
  have h22 := congrFun (congrFun hc 2) 2
  rw [matU_levU, matU_levU] at h22
  simp [leviMat, Matrix.scalar_apply] at h22
  have hc1 : (c : F) = 1 := h22.symm
  have hc' : matU (levU hq1 B') = matU (levU hq1 B) := by
    rw [hc, hc1]; simp
  exact (levU_injective hq1 (matU_ext hc')).symm

theorem IsCover.injective_comp (hθ : IsCover h θ) (hq1 : 1 ≤ p ^ f) :
    Function.Injective (θ.comp (levU hq1)) := fun _ _ hB => hθ.levU_eq h hq1 hB

end Cover2


section InvPre

variable (h : UnitaryFieldData p f F) {K : Type*} [Group K] {θ : ↥(unitarySU p f F 3) →* K}

@[expose] noncomputable def levS (hq : Odd (p ^ f)) (θ : ↥(unitarySU p f F 3) →* K) : Subgroup K :=
  (θ.comp (levU hq.pos)).range

theorem mem_levS (hq : Odd (p ^ f)) {x : K} :
    x ∈ levS hq θ ↔ ∃ B : ↥(unitarySU p f F 2), θ (levU hq.pos B) = x := Iff.rfl

theorem θ_levU_mem_levS (hq : Odd (p ^ f)) (B : ↥(unitarySU p f F 2)) :
    θ (levU hq.pos B) ∈ levS hq θ := ⟨B, rfl⟩

theorem θ_dU_mem_levS (h : UnitaryFieldData p f F) (hq : Odd (p ^ f)) : θ (dU hq) ∈ levS hq θ :=
  ⟨negI h, by simp [levU_negI h hq]⟩

theorem card_levS (hθ : IsCover h θ) (hq : Odd (p ^ f)) :
    Nat.card ↥(levS hq θ) = p ^ f * ((p ^ f) ^ 2 - 1) := by
  have := h.finite
  have := h.charP
  have : Fact p.Prime := ⟨h.prime⟩
  have e := (MonoidHom.ofInjective (hθ.injective_comp h hq.pos)).toEquiv
  change Nat.card ↥((θ.comp (levU hq.pos)).range) = _
  rw [← Nat.card_congr e]
  exact card_statedSU_two h.card_eq_sq

theorem quasisimple_levS (hθ : IsCover h θ) (hq : Odd (p ^ f)) (h4 : 4 ≤ p ^ f) :
    CFSG.IsQuasisimple ↥(levS hq θ) := by
  have := h.finite
  have := h.charP
  have : Fact p.Prime := ⟨h.prime⟩
  obtain ⟨e⟩ := nonempty_sl2_mulEquiv_statedSU_two (K := F) (r := p) (f := f) h.card_eq_sq
  have hfin : Finite (CFSG.LieType.Steinberg.fixedSubfield F p f) := inferInstance
  have hq2 : IsQuasisimple SL(2, CFSG.LieType.Steinberg.fixedSubfield F p f) :=
    isQuasisimple_sl2c (by rw [CFSG.LieType.Steinberg.card_fixedSubfield h.card_eq_sq]; exact h4)
  have h1 : CFSG.IsQuasisimple ↥(unitarySU p f F 2) := LocalCores.isQuasisimple_of_mulEquiv e hq2
  exact LocalCores.isQuasisimple_of_mulEquiv (MonoidHom.ofInjective (hθ.injective_comp h hq.pos)) h1

theorem levS_le_centralizer (hq : Odd (p ^ f)) :
    levS hq θ ≤ Subgroup.centralizer ({θ (dU hq)} : Set K) := by
  rintro _ ⟨B, rfl⟩
  rw [mem_centralizer_singleton_iff]
  show θ (levU hq.pos B) * θ (dU hq) = θ (dU hq) * θ (levU hq.pos B)
  rw [← map_mul, ← map_mul, mem_centralizer_singleton_iff.1 (levU_mem_centralizer hq B)]


theorem levS_conj_mem (hθ : IsCover h θ) (hq : Odd (p ^ f)) {x : K}
    (hx : x ∈ Subgroup.centralizer ({θ (dU hq)} : Set K)) {s : K} (hs : s ∈ levS hq θ) :
    x * s * x⁻¹ ∈ levS hq θ := by
  obtain ⟨g, rfl, hg⟩ := cen_lift h θ hθ.ker hθ.surj (two_ne_zero_of_odd_pow h hq) hq hx
  obtain ⟨B, rfl⟩ := hs
  have hgC : g ∈ Subgroup.centralizer ({dU hq} : Set ↥(unitarySU p f F 3)) :=
    mem_centralizer_singleton_iff.2 hg
  let G : ↥(Subgroup.centralizer ({dU hq} : Set ↥(unitarySU p f F 3))) := ⟨g, hgC⟩
  let L : ↥(Subgroup.centralizer ({dU hq} : Set ↥(unitarySU p f F 3))) :=
    ⟨levU hq.pos B, levU_mem_centralizer hq B⟩
  have h1 : cenHomU h hq (G * L * G⁻¹) = 1 := by
    rw [map_mul, map_mul, map_inv, cenHomU_levU, mul_one, mul_inv_cancel]
  obtain ⟨B', hB'⟩ := mem_range_levU_of_cenHomU h hq _ h1
  refine ⟨B', ?_⟩
  have h2 : levU hq.pos B' = g * levU hq.pos B * g⁻¹ := hB'
  show θ (levU hq.pos B') = θ g * θ (levU hq.pos B) * (θ g)⁻¹
  rw [h2, map_mul, map_mul, map_inv]

theorem levS_commutator_mem (hθ : IsCover h θ) (hq : Odd (p ^ f)) {x y : K}
    (hx : x ∈ Subgroup.centralizer ({θ (dU hq)} : Set K))
    (hy : y ∈ Subgroup.centralizer ({θ (dU hq)} : Set K)) : ⁅x, y⁆ ∈ levS hq θ := by
  obtain ⟨g, rfl, hg⟩ := cen_lift h θ hθ.ker hθ.surj (two_ne_zero_of_odd_pow h hq) hq hx
  obtain ⟨g', rfl, hg'⟩ := cen_lift h θ hθ.ker hθ.surj (two_ne_zero_of_odd_pow h hq) hq hy
  let G : ↥(Subgroup.centralizer ({dU hq} : Set ↥(unitarySU p f F 3))) :=
    ⟨g, mem_centralizer_singleton_iff.2 hg⟩
  let G' : ↥(Subgroup.centralizer ({dU hq} : Set ↥(unitarySU p f F 3))) :=
    ⟨g', mem_centralizer_singleton_iff.2 hg'⟩
  have h1 : cenHomU h hq ⁅G, G'⁆ = 1 := by
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 (mul_comm _ _)
  obtain ⟨B', hB'⟩ := mem_range_levU_of_cenHomU h hq _ h1
  refine ⟨B', ?_⟩
  have h2 : levU hq.pos B' = ⁅g, g'⁆ := hB'
  show θ (levU hq.pos B') = ⁅θ g, θ g'⁆
  rw [h2, map_commutatorElement]

@[expose] noncomputable def toSL2 (h : UnitaryFieldData p f F) : ↥(unitarySU p f F 2) →* SL(2, F) where
  toFun B := ⟨matU B, ((mem_unitarySU_iff h).1 B.2).1⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl

theorem ringChar_ne_two_of_odd_pow (h : UnitaryFieldData p f F) (hq : Odd (p ^ f)) : ringChar F ≠ 2 :=
  fun h2 => two_ne_zero_of_odd_pow h hq (by
    have : CharP F 2 := h2 ▸ ringChar.charP F
    exact CharTwo.two_eq_zero)

theorem su2_sq_eq_one (h : UnitaryFieldData p f F) (hq : Odd (p ^ f)) {B : ↥(unitarySU p f F 2)}
    (hB : B * B = 1) : B = 1 ∨ B = negI h := by
  have h1 : toSL2 h B * toSL2 h B = 1 := by rw [← map_mul, hB, map_one]
  rcases sl2c_sq_eq_one (ringChar_ne_two_of_odd_pow h hq) h1 with h2 | h2
  · left
    apply matU_ext
    rw [matU_one]
    exact congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F)) h2
  · right
    apply matU_ext
    rw [matU_negI]
    exact congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F)) h2

theorem levS_involution (hθ : IsCover h θ) (hq : Odd (p ^ f)) {s : K} (hs : s ∈ levS hq θ)
    (hs2 : s * s = 1) : s = 1 ∨ s = θ (dU hq) := by
  obtain ⟨B, rfl⟩ := hs
  have h1 : θ (levU hq.pos (B * B)) = θ (levU hq.pos 1) := by
    rw [map_mul, map_mul, map_one, map_one]
    exact hs2
  have h2 : B * B = 1 := hθ.levU_eq h hq.pos h1
  rcases su2_sq_eq_one h hq h2 with h3 | h3
  · left
    rw [h3, map_one]
  · right
    show θ (levU hq.pos B) = θ (dU hq)
    rw [h3, levU_negI h hq]

theorem su2_center (h : UnitaryFieldData p f F) (h5 : 5 ≤ p ^ f)
    {B : ↥(unitarySU p f F 2)} (hcen : ∀ B' : ↥(unitarySU p f F 2), B' * B = B * B') :
    B = 1 ∨ B = negI h := by
  obtain ⟨l, hl0, hl, hl1, hl2⟩ := exists_norm_one_ne h h5
  have hD := hcen (dTestU h hl0 hl)
  have hJ := hcen (jU h)
  have hD' : leviMat (matU B) * leviMat !![l, 0; 0, l⁻¹] = leviMat !![l, 0; 0, l⁻¹] * leviMat (matU B) := by
    rw [← leviMat_mul, ← leviMat_mul, ← matU_dTestU h hl0 hl, ← matU_mul, ← matU_mul, hD]
  have hJ' : leviMat (matU B) * leviMat !![0, 1; -1, 0] = leviMat !![0, 1; -1, 0] * leviMat (matU B) := by
    rw [← leviMat_mul, ← leviMat_mul, ← matU_jU h, ← matU_mul, ← matU_mul, hJ]
  obtain ⟨e01, e10, -, -, -, -, e00⟩ := form_of_commute_levi hl0 hl1 hl2 hD' hJ'
  simp only [leviMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Matrix.empty_val'] at e01 e10 e00
  have hdet := ((mem_unitarySU_iff h).1 B.2).1
  rw [Matrix.det_fin_two] at hdet
  change matU B 0 0 * matU B 1 1 - matU B 0 1 * matU B 1 0 = 1 at hdet
  have hsq : matU B 0 0 * matU B 0 0 = 1 := by
    rw [← e00] at hdet
    rw [e01, e10] at hdet
    simpa using hdet
  rcases mul_self_eq_one_iff.1 hsq with h1 | h1
  · left
    apply matU_ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [e01, e10, h1, ← e00, matU_one]
  · right
    apply matU_ext
    rw [matU_negI]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [e01, e10, h1, ← e00]

theorem levS_center (hθ : IsCover h θ) (hq : Odd (p ^ f)) (h5 : 5 ≤ p ^ f) (s : ↥(levS hq θ))
    (hs : s ∈ Subgroup.center ↥(levS hq θ)) : (s : K) = 1 ∨ (s : K) = θ (dU hq) := by
  obtain ⟨B, hB⟩ : ∃ B : ↥(unitarySU p f F 2), θ (levU hq.pos B) = (s : K) := s.2
  have hcen : ∀ B' : ↥(unitarySU p f F 2), B' * B = B * B' := by
    intro B'
    have h1 := Subgroup.mem_center_iff.1 hs ⟨θ (levU hq.pos B'), θ_levU_mem_levS hq B'⟩
    have h2 := congrArg Subtype.val h1
    simp only [Subgroup.coe_mul] at h2
    rw [← hB] at h2
    apply hθ.levU_eq h hq.pos
    simp only [map_mul]
    exact h2
  rcases su2_center h h5 hcen with h3 | h3
  · left
    rw [← hB, h3, map_one, map_one]
  · right
    rw [← hB, h3, levU_negI h hq]

end InvPre

end CFSG.GH74.KGroups.L3Eps.Uni
