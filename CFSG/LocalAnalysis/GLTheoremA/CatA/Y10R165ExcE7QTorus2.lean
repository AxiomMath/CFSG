module

public import CFSG.RankThree.PartTwo.Census.Classical.EvenHyperbolic
public import CFSG.HardMathSupport.Timmesfeld.FieldBonus.SU3Core
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.Classical2.SLnRootPermutingFixedGroups

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE7Three

open Matrix CFSG.Open CFSG.RankThree.Classical2 CFSG.RankThree.PartTwo.Census
open scoped MatrixGroups Pointwise

section Hyperbolic

variable {F : Type} [Field F] [CharP F 2]

private noncomputable def hyperP (ω : F) : Matrix (Fin 2) (Fin 2) F := !![1, 1; 1, ω]

private noncomputable def hyperG (ω : F) : Matrix (Fin 2) (Fin 2) F := !![0, 1 + ω; 1 + ω⁻¹, 0]

private noncomputable def hyperM (ω : F) (a : Fˣ) : Matrix (Fin 2) (Fin 2) F :=
  hyperP ω * hypD a * (hyperP ω)⁻¹

private theorem hyperP_det {ω : F} (h1ω : 1 + ω ≠ 0) : (hyperP ω).det = 1 + ω := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have h : hyperP ω = !![1, 1; 1, ω] := rfl
  rw [h, Matrix.det_fin_two]
  simp [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  linear_combination -h2

private theorem hyperP_star_mul {φ : F →+* F} {ω : F} (hω0 : ω ≠ 0) (hφ : φ ω = ω⁻¹) :
    ((hyperP ω).map φ)ᵀ * hyperP ω = hyperG ω := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hyperP, hyperG, Matrix.mul_apply, Fin.sum_univ_two, hφ, hω0, CharTwo.add_self_eq_zero]

private theorem mul_inv_cancel_mul {x y : F} (hx : x ≠ 0) : x * y * x⁻¹ = y := by
  rw [← div_eq_mul_inv]
  exact mul_div_cancel_left₀ _ hx

private theorem hypD_star_mul_hyperG {φ : F →+* F} {ω : F} {a : Fˣ}
    (ha : φ (a : F) = (a : F)) :
    ((hypD a).map φ)ᵀ * hyperG ω * hypD a = hyperG ω := by
  have hD : ((hypD a).map φ)ᵀ = hypD a := by
    rw [hypD, diagonal_map (map_zero φ), diagonal_transpose]
    congr 1
    funext i
    fin_cases i <;> simp [ha]
  rw [hD]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hypD, hyperG, Matrix.diagonal_apply, Matrix.mul_apply, Fin.sum_univ_two,
      Units.val_inv_eq_inv_val]
  all_goals
    first
    | rfl
    | exact mul_inv_cancel_mul (x := (a : F)) a.ne_zero
    | simpa using mul_inv_cancel_mul (x := ((a : F))⁻¹) (inv_ne_zero a.ne_zero)

private theorem conj_cancel_inv_mul {P D : Matrix (Fin 2) (Fin 2) F} (hP : P⁻¹ * P = 1) :
    P⁻¹ * (P * D * P⁻¹) * P = D := by
  calc P⁻¹ * (P * D * P⁻¹) * P = (P⁻¹ * P) * D * (P⁻¹ * P) := by noncomm_ring
    _ = D := by rw [hP, one_mul, mul_one]

private theorem conj_mul_conj {P D D' : Matrix (Fin 2) (Fin 2) F} (hP : P⁻¹ * P = 1) :
    (P * D * P⁻¹) * (P * D' * P⁻¹) = P * (D * D') * P⁻¹ := by
  calc (P * D * P⁻¹) * (P * D' * P⁻¹) = P * D * (P⁻¹ * P) * D' * P⁻¹ := by noncomm_ring
    _ = P * (D * D') * P⁻¹ := by rw [hP]; noncomm_ring

private theorem star_conj_unitary {P D G : Matrix (Fin 2) (Fin 2) F} {φ : F →+* F}
    (hPinv' : P * P⁻¹ = 1) (hPG : (P.map φ)ᵀ * P = G)
    (hDG : (D.map φ)ᵀ * G * D = G) :
    ((P * D * P⁻¹).map φ)ᵀ * (P * D * P⁻¹) = 1 := by
  have hstar : ((P⁻¹).map φ)ᵀ * (P.map φ)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, ← Matrix.map_mul, hPinv',
      Matrix.map_one _ (map_zero φ) (map_one φ), Matrix.transpose_one]
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_mul]
  calc ((P⁻¹).map φ)ᵀ * ((D.map φ)ᵀ * (P.map φ)ᵀ) * (P * D * P⁻¹)
      = ((P⁻¹).map φ)ᵀ * ((D.map φ)ᵀ * ((P.map φ)ᵀ * P) * D) * P⁻¹ := by noncomm_ring
    _ = ((P⁻¹).map φ)ᵀ * ((D.map φ)ᵀ * G * D) * P⁻¹ := by rw [hPG]
    _ = ((P⁻¹).map φ)ᵀ * G * P⁻¹ := by rw [hDG]
    _ = ((P⁻¹).map φ)ᵀ * ((P.map φ)ᵀ * P) * P⁻¹ := by rw [← hPG]
    _ = (((P⁻¹).map φ)ᵀ * (P.map φ)ᵀ) * (P * P⁻¹) := by noncomm_ring
    _ = 1 := by rw [hstar, hPinv', mul_one]

private theorem hyperM_mul {ω : F} (hP : (hyperP ω)⁻¹ * hyperP ω = 1) (a b : Fˣ) :
    hyperM ω a * hyperM ω b = hyperM ω (a * b) := by
  rw [hyperM, hyperM, hyperM, conj_mul_conj hP, hypD_mul]

private theorem hyperM_one {ω : F} (hP : hyperP ω * (hyperP ω)⁻¹ = 1) : hyperM ω 1 = 1 := by
  rw [hyperM, hypD_one, mul_one]
  exact hP

private theorem det_hyperM {ω : F} (hdet : IsUnit (hyperP ω).det) (a : Fˣ) :
    (hyperM ω a).det = 1 := by
  have hpp : (hyperP ω).det * ((hyperP ω)⁻¹).det = 1 := by
    rw [← Matrix.det_mul, Matrix.mul_nonsing_inv _ hdet, Matrix.det_one]
  rw [hyperM, Matrix.det_mul, Matrix.det_mul, det_hypD]
  calc (hyperP ω).det * 1 * ((hyperP ω)⁻¹).det = (hyperP ω).det * ((hyperP ω)⁻¹).det := by ring
    _ = 1 := hpp

private theorem hyperM_unitary {φ : F →+* F} {ω : F} (hdet : IsUnit (hyperP ω).det)
    (hω0 : ω ≠ 0) (hφ : φ ω = ω⁻¹) {a : Fˣ} (ha : φ (a : F) = (a : F)) :
    ((hyperM ω a).map φ)ᵀ * hyperM ω a = 1 :=
  star_conj_unitary (Matrix.mul_nonsing_inv _ hdet)
    (hyperP_star_mul hω0 hφ) (hypD_star_mul_hyperG ha)

private theorem hyperM_injective {ω : F} (hdet : IsUnit (hyperP ω).det) :
    Function.Injective (hyperM ω) := by
  intro a b hab
  have hP : (hyperP ω)⁻¹ * hyperP ω = 1 := Matrix.nonsing_inv_mul _ hdet
  have hD : ∀ c : Fˣ, (hyperP ω)⁻¹ * hyperM ω c * hyperP ω = hypD c := fun c =>
    conj_cancel_inv_mul hP
  have h := congrFun (congrFun ((hD a).symm.trans (hab ▸ hD b)) 0) 0
  simp only [hypD, Matrix.diagonal_apply_eq, Matrix.cons_val_zero] at h
  exact Units.ext h

end Hyperbolic

section Center

variable {K : Type} [Field K] [Finite K] {L : Type} [Field L] [Algebra K L]
  [IsAlgClosure K L]

private theorem exists_scalar_of_mem_center {q0 : ℕ} (hq0 : Nat.card K = q0)
    {Φ' : SL(6, L) ≃* SL(6, L)} {H : SL(6, L)}
    (hfix : ∀ X : SL(6, L), X ∈ fixSubgroup Φ' ↔
      ∃ Y ∈ unitarySet q0 6, Matrix.SpecialLinearGroup.toGL X =
        Matrix.SpecialLinearGroup.toGL H * Y * (Matrix.SpecialLinearGroup.toGL H)⁻¹)
    {z : ↥(fixSubgroup Φ')} (hz : z ∈ Subgroup.center ↥(fixSubgroup Φ')) :
    ∃ c : L, ((z : SL(6, L)) : Matrix (Fin 6) (Fin 6) L) = Matrix.scalar (Fin 6) c := by
  classical
  set W : GL (Fin 6) L := (Matrix.SpecialLinearGroup.toGL H)⁻¹ *
    Matrix.SpecialLinearGroup.toGL (z : SL(6, L)) * Matrix.SpecialLinearGroup.toGL H with hW
  have hWcent : W ∈ Subgroup.centralizer (unitarySet q0 6) := by
    intro V hV
    obtain ⟨hVdet, -⟩ := hV.2
    set Ysl : SL(6, L) := ⟨V, hVdet⟩ with hYsl
    have hYtoGL : Matrix.SpecialLinearGroup.toGL Ysl = V := Units.ext rfl
    have hXmem : H * Ysl * H⁻¹ ∈ fixSubgroup Φ' :=
      (hfix _).2 ⟨V, hV, by simp only [map_mul, map_inv, hYtoGL]⟩
    have hcomm := Subgroup.mem_center_iff.mp hz (⟨H * Ysl * H⁻¹, hXmem⟩ : ↥(fixSubgroup Φ'))
    have h2 := congrArg (fun t : ↥(fixSubgroup Φ') =>
      Matrix.SpecialLinearGroup.toGL (t : SL(6, L))) hcomm
    simp only [Subgroup.coe_mul, map_mul, map_inv, hYtoGL] at h2
    rw [hW]
    calc V * ((Matrix.SpecialLinearGroup.toGL H)⁻¹ *
          Matrix.SpecialLinearGroup.toGL (z : SL(6, L)) * Matrix.SpecialLinearGroup.toGL H)
        = (Matrix.SpecialLinearGroup.toGL H)⁻¹ *
            ((Matrix.SpecialLinearGroup.toGL H * V * (Matrix.SpecialLinearGroup.toGL H)⁻¹) *
              Matrix.SpecialLinearGroup.toGL (z : SL(6, L))) *
            Matrix.SpecialLinearGroup.toGL H := by group
      _ = (Matrix.SpecialLinearGroup.toGL H)⁻¹ *
            (Matrix.SpecialLinearGroup.toGL (z : SL(6, L)) *
              (Matrix.SpecialLinearGroup.toGL H * V * (Matrix.SpecialLinearGroup.toGL H)⁻¹)) *
            Matrix.SpecialLinearGroup.toGL H := by rw [h2]
      _ = (Matrix.SpecialLinearGroup.toGL H)⁻¹ *
            Matrix.SpecialLinearGroup.toGL (z : SL(6, L)) *
              Matrix.SpecialLinearGroup.toGL H * V := by
            group
  rw [CFSG.RankThree.Classical2.centralizer_unitary_eq_range_scalar (k := K) (q := q0) hq0
    (n := 6) (by norm_num)] at hWcent
  obtain ⟨c, hc⟩ := hWcent
  have hcent : Matrix.GeneralLinearGroup.scalar (Fin 6) c ∈ Subgroup.center (GL (Fin 6) L) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨c, rfl⟩
  have hcommH := Subgroup.mem_center_iff.mp hcent (Matrix.SpecialLinearGroup.toGL H)
  have hzW : Matrix.SpecialLinearGroup.toGL (z : SL(6, L)) =
      Matrix.SpecialLinearGroup.toGL H * W * (Matrix.SpecialLinearGroup.toGL H)⁻¹ := by
    rw [hW]
    group
  refine ⟨(c : L), ?_⟩
  calc ((z : SL(6, L)) : Matrix (Fin 6) (Fin 6) L)
      = ((Matrix.SpecialLinearGroup.toGL (z : SL(6, L))) :
          Matrix (Fin 6) (Fin 6) L) := rfl
    _ = ((Matrix.SpecialLinearGroup.toGL H * W * (Matrix.SpecialLinearGroup.toGL H)⁻¹ :
          GL (Fin 6) L) : Matrix (Fin 6) (Fin 6) L) := by rw [hzW]
    _ = ((Matrix.SpecialLinearGroup.toGL H * Matrix.GeneralLinearGroup.scalar (Fin 6) c *
          (Matrix.SpecialLinearGroup.toGL H)⁻¹ : GL (Fin 6) L) :
            Matrix (Fin 6) (Fin 6) L) := by rw [hc]
    _ = Matrix.scalar (Fin 6) (c : L) := by
          rw [hcommH, mul_assoc, mul_inv_cancel, mul_one]
          exact Matrix.GeneralLinearGroup.coe_scalar c

private theorem eq_one_of_mem_center [CharP L 2] {q0 : ℕ} (hq0 : Nat.card K = q0)
    {Φ' : SL(6, L) ≃* SL(6, L)} {H : SL(6, L)}
    (hfix : ∀ X : SL(6, L), X ∈ fixSubgroup Φ' ↔
      ∃ Y ∈ unitarySet q0 6, Matrix.SpecialLinearGroup.toGL X =
        Matrix.SpecialLinearGroup.toGL H * Y * (Matrix.SpecialLinearGroup.toGL H)⁻¹)
    (h3 : ¬ 3 ∣ q0 + 1) {z : ↥(fixSubgroup Φ')}
    (hz : z ∈ Subgroup.center ↥(fixSubgroup Φ')) : z = 1 := by
  classical
  obtain ⟨c, hc⟩ := exists_scalar_of_mem_center hq0 hfix hz
  have hq0pos : 0 < q0 := by rw [← hq0]; exact Nat.card_pos
  have hc6 : c ^ 6 = 1 := by
    have h : (Matrix.scalar (Fin 6) c).det = 1 := by rw [← hc]; exact (z : SL(6, L)).2
    rwa [Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin] at h
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_pow (by norm_num : 6 ≠ 0)] at hc6
    exact zero_ne_one hc6
  obtain ⟨Y, hYU, hYeq⟩ := (hfix (z : SL(6, L))).1 z.2
  have hzGL : Matrix.SpecialLinearGroup.toGL (z : SL(6, L)) =
      Matrix.GeneralLinearGroup.scalar (Fin 6) (Units.mk0 c hc0) := by
    apply Units.ext
    change ((z : SL(6, L)) : Matrix (Fin 6) (Fin 6) L) = Matrix.scalar (Fin 6) c
    exact hc
  have hcent : Matrix.GeneralLinearGroup.scalar (Fin 6) (Units.mk0 c hc0) ∈
      Subgroup.center (GL (Fin 6) L) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨Units.mk0 c hc0, rfl⟩
  have hcommH := Subgroup.mem_center_iff.mp hcent (Matrix.SpecialLinearGroup.toGL H)
  have hYscal : Y = Matrix.GeneralLinearGroup.scalar (Fin 6) (Units.mk0 c hc0) := by
    have h1 : Matrix.SpecialLinearGroup.toGL H * Y * (Matrix.SpecialLinearGroup.toGL H)⁻¹ =
        Matrix.GeneralLinearGroup.scalar (Fin 6) (Units.mk0 c hc0) := by rw [← hYeq, hzGL]
    calc Y = (Matrix.SpecialLinearGroup.toGL H)⁻¹ *
            (Matrix.SpecialLinearGroup.toGL H * Y * (Matrix.SpecialLinearGroup.toGL H)⁻¹) *
            Matrix.SpecialLinearGroup.toGL H := by group
      _ = (Matrix.SpecialLinearGroup.toGL H)⁻¹ *
            Matrix.GeneralLinearGroup.scalar (Fin 6) (Units.mk0 c hc0) *
            Matrix.SpecialLinearGroup.toGL H := by rw [h1]
      _ = Matrix.GeneralLinearGroup.scalar (Fin 6) (Units.mk0 c hc0) := by
            rw [mul_assoc, ← hcommH, ← mul_assoc, inv_mul_cancel, one_mul]
  rw [hYscal] at hYU
  have hq1 : c ^ (q0 + 1) = 1 := by
    have h := hYU.2.2
    have h00 := congrFun (congrFun h 0) 0
    rw [Matrix.GeneralLinearGroup.coe_scalar] at h00
    simp [Matrix.scalar_apply, Matrix.diagonal_apply] at h00
    rwa [pow_succ]
  have hc3 : c ^ 3 = 1 := by
    have h : c ^ 3 * c ^ 3 = 1 := by
      rw [← pow_add]
      norm_num
      exact hc6
    have h2 : (2 : L) = 0 := CharTwo.two_eq_zero
    have hsq : (c ^ 3 + 1) * (c ^ 3 + 1) = 0 := by
      calc (c ^ 3 + 1) * (c ^ 3 + 1) = c ^ 3 * c ^ 3 + (c ^ 3 + c ^ 3) + 1 := by ring
        _ = 0 := by rw [h, CharTwo.add_self_eq_zero, add_zero]; linear_combination h2
    have hzero : c ^ 3 + 1 = 0 := by
      rcases mul_eq_zero.mp hsq with h' | h' <;> exact h'
    linear_combination hzero - h2
  have hgcd : Nat.gcd 3 (q0 + 1) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp (Nat.gcd_dvd_left 3 (q0 + 1)) with h1 | h1
    · exact h1
    · exact absurd (h1 ▸ Nat.gcd_dvd_right 3 (q0 + 1)) h3
  have hg : c ^ Nat.gcd 3 (q0 + 1) = 1 := pow_gcd_eq_one.mpr ⟨hc3, hq1⟩
  rw [hgcd] at hg
  have hc1 : c = 1 := by simpa using hg
  refine Subtype.ext (Subtype.ext ?_)
  rw [hc, hc1]
  simp

end Center

section Unitary

variable {K : Type} [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime]
  {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]

private lemma exists_unitary_root {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hFcard : Nat.card F = (2 ^ f) ^ 2) (h2f : 2 ≤ 2 ^ f) :
    ∃ ωu : Fˣ, (ωu : F) ^ (2 ^ f + 1) = 1 ∧ (ωu : F) ≠ 1 ∧ (ωu : F) ≠ 0 ∧
      (ωu : F) ^ (2 ^ f) = ((ωu : F))⁻¹ ∧ 1 + (ωu : F) ≠ 0 ∧
      IsUnit (hyperP (ωu : F)).det := by
  classical
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hFunits : Nat.card Fˣ = (2 ^ f) ^ 2 - 1 := by rw [Nat.card_units, hFcard]
  have hordg : orderOf g = (2 ^ f) ^ 2 - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, hFunits]
  set ωu : Fˣ := g ^ (2 ^ f - 1) with hωudef
  have hωpow_u : ωu ^ (2 ^ f + 1) = 1 := by
    rw [hωudef, ← pow_mul, show (2 ^ f - 1) * (2 ^ f + 1) = (2 ^ f) ^ 2 - 1 by
      rw [mul_comm, ← CFSG.ClassicalGroups.Unitary.sq_sub_one_eq (2 ^ f) (by omega)]]
    rw [← hordg]
    exact pow_orderOf_eq_one g
  have hωpow : ((ωu : F)) ^ (2 ^ f + 1) = 1 := by
    rw [← Units.val_pow_eq_pow_val, hωpow_u, Units.val_one]
  have hωne : (ωu : F) ≠ 1 := by
    intro h1
    have hu1 : ωu = 1 := Units.ext h1
    have hdvd2 : (2 ^ f) ^ 2 - 1 ∣ 2 ^ f - 1 := by
      rw [← hordg]
      exact orderOf_dvd_of_pow_eq_one (by rw [hωudef] at hu1; exact hu1)
    have hle := Nat.le_of_dvd (by omega) hdvd2
    have hle' : (2 ^ f) ^ 2 ≤ 2 ^ f := by omega
    nlinarith
  have hω0 : (ωu : F) ≠ 0 := ωu.ne_zero
  have hωinv : ((ωu : F)) ^ (2 ^ f) = ((ωu : F))⁻¹ := by
    have h := hωpow
    rw [pow_succ] at h
    exact eq_inv_of_mul_eq_one_left h
  have h1ω : 1 + (ωu : F) ≠ 0 := by
    intro h
    have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
    have h1 : (ωu : F) = 1 := by linear_combination h - h2
    exact hωne h1
  refine ⟨ωu, hωpow, hωne, hω0, hωinv, h1ω, ?_⟩
  rw [hyperP_det h1ω]
  exact isUnit_iff_ne_zero.mpr h1ω

private lemma exists_unitary_psi {F : Type} [Field F] [Finite F] [CharP F 2] {f q : ℕ}
    (hdvd' : q ∣ 2 ^ f - 1) {ωu : Fˣ} (hω0 : (ωu : F) ≠ 0)
    (hωinv : (ωu : F) ^ (2 ^ f) = ((ωu : F))⁻¹)
    (hdet : IsUnit (hyperP (ωu : F)).det)
    {φ : F →+* F} (hφdef : ∀ c : F, φ c = c ^ 2 ^ f)
    (hφω : φ (ωu : F) = ((ωu : F))⁻¹) :
    ∃ ψ : (Fin 3 → rootsOfUnity q F) →* ↥(StatedSU 6 (2 ^ f) F),
      Function.Injective ψ := by
  classical
  have hφmu : ∀ a : rootsOfUnity q F, φ ((a : Fˣ) : F) = ((a : Fˣ) : F) := by
    intro a
    have haq : ((a : Fˣ) : F) ^ q = 1 := by
      have h : (a : Fˣ) ^ q = 1 := by
        rw [← Subgroup.coe_pow, rootsOfUnity_pow_eq_one a, OneMemClass.coe_one]
      rw [← Units.val_pow_eq_pow_val, h, Units.val_one]
    obtain ⟨m, hm⟩ := hdvd'
    have hpos : 0 < 2 ^ f := pow_pos (by norm_num) f
    have h2f' : 2 ^ f = q * m + 1 := by omega
    rw [hφdef, h2f', pow_add, pow_mul, haq, one_pow, one_mul, pow_one]
  let ψ₀ : (Fin 3 → rootsOfUnity q F) →* GL (Fin 6) F :=
    { toFun := fun t => ⟨blk6 fun i => hyperM (ωu : F) (t i),
        blk6 fun i => hyperM (ωu : F) (t i)⁻¹, by
          rw [blk6_mul, ← blk6_one]
          congr 1
          funext i
          rw [Pi.mul_apply, hyperM_mul (Matrix.nonsing_inv_mul _ hdet), mul_inv_cancel,
            hyperM_one (Matrix.mul_nonsing_inv _ hdet)]
          rfl, by
          rw [blk6_mul, ← blk6_one]
          congr 1
          funext i
          rw [Pi.mul_apply, hyperM_mul (Matrix.nonsing_inv_mul _ hdet), inv_mul_cancel,
            hyperM_one (Matrix.mul_nonsing_inv _ hdet)]
          rfl⟩
      map_one' := Units.ext (by
        change blk6 (fun i => hyperM (ωu : F) ((1 : Fin 3 → rootsOfUnity q F) i)) = 1
        rw [← blk6_one]
        congr 1
        funext i
        rw [Pi.one_apply, OneMemClass.coe_one, hyperM_one (Matrix.mul_nonsing_inv _ hdet)]
        rfl)
      map_mul' := fun s t => Units.ext (by
        change blk6 (fun i => hyperM (ωu : F) ((s * t) i)) =
          blk6 (fun i => hyperM (ωu : F) (s i)) * blk6 fun i => hyperM (ωu : F) (t i)
        rw [blk6_mul]
        congr 1
        funext i
        rw [Pi.mul_apply, Pi.mul_apply, Subgroup.coe_mul,
          hyperM_mul (Matrix.nonsing_inv_mul _ hdet)]) }
  have hmemψ : ∀ t, ψ₀ t ∈ StatedSU 6 (2 ^ f) F := by
    intro t
    refine Subgroup.subset_closure ⟨?_, ?_⟩
    · change (blk6 fun i => hyperM (ωu : F) (t i)).det = 1
      rw [det_blk6]
      exact Finset.prod_eq_one fun i _ => det_hyperM hdet (t i)
    · change (((blk6 fun i => hyperM (ωu : F) (t i)).map (· ^ 2 ^ f))ᵀ *
        blk6 (fun i => hyperM (ωu : F) (t i))) = 1
      have hmap : (blk6 fun i => hyperM (ωu : F) (t i)).map (· ^ 2 ^ f) =
          (blk6 fun i => hyperM (ωu : F) (t i)).map φ := by
        ext i j
        rw [Matrix.map_apply, Matrix.map_apply, hφdef]
      rw [hmap]
      exact blk6_unitary _ φ fun i =>
        hyperM_unitary (φ := φ) hdet hω0 hφω (hφmu (t i))
  let ψ : (Fin 3 → rootsOfUnity q F) →* ↥(StatedSU 6 (2 ^ f) F) := ψ₀.codRestrict _ hmemψ
  refine ⟨ψ, ?_⟩
  intro s t hst
  have h1 : blk6 (fun i => hyperM (ωu : F) (s i)) =
      blk6 (fun i => hyperM (ωu : F) (t i)) := by
    have h := congrArg (fun g : ↥(StatedSU 6 (2 ^ f) F) =>
      ((g : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F)) hst
    change ((ψ₀ s : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) =
      ((ψ₀ t : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) at h
    exact h
  funext i
  exact Subtype.ext (hyperM_injective hdet (congrFun (blk6_injective h1) i))

private lemma exists_fixSubgroup_embedding {L : Type} [Field L] {F : Subfield L} {f : ℕ}
    [Finite F] [Fintype F] [CharP F 2]
    (hFmem : ∀ c : L, c ∈ F ↔ c ^ (2 ^ f) ^ 2 = c)
    (hFcard : Nat.card F = (2 ^ f) ^ 2)
    {Φ' : SL(6, L) ≃* SL(6, L)} {H : SL(6, L)}
    (hfix : ∀ X : SL(6, L), X ∈ fixSubgroup Φ' ↔
      ∃ Y ∈ unitarySet (2 ^ f) 6, Matrix.SpecialLinearGroup.toGL X =
        Matrix.SpecialLinearGroup.toGL H * Y * (Matrix.SpecialLinearGroup.toGL H)⁻¹) :
    ∃ Ψ : ↥(StatedSU 6 (2 ^ f) F) →* ↥(fixSubgroup Φ'),
      Function.Injective Ψ ∧ Function.Surjective Ψ := by
  classical
  have hmemY : ∀ Z : ↥(StatedSU 6 (2 ^ f) F),
      Matrix.SpecialLinearGroup.toGL (statedSUToSL F 6 (2 ^ f) Z) ∈ unitarySet (2 ^ f) 6 :=
    fun Z => (mem_range_statedSUToSL_iff (ℓ := 2) (f := f) (n := 6) Nat.prime_two F hFmem hFcard
      (by norm_num) _).mp ⟨Z, rfl⟩
  let Ψ : ↥(StatedSU 6 (2 ^ f) F) →* ↥(fixSubgroup Φ') :=
    { toFun := fun Z => ⟨H * statedSUToSL F 6 (2 ^ f) Z * H⁻¹,
        (hfix _).2 ⟨Matrix.SpecialLinearGroup.toGL (statedSUToSL F 6 (2 ^ f) Z), hmemY Z, by
          simp only [map_mul, map_inv]⟩⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun Z W => Subtype.ext (by
        simp only [Subtype.coe_mk, Subgroup.coe_mul, map_mul]
        group) }
  have hΨinj : Function.Injective Ψ := by
    intro Z W hZW
    have h := congrArg (fun t : ↥(fixSubgroup Φ') => (t : SL(6, L))) hZW
    change H * statedSUToSL F 6 (2 ^ f) Z * H⁻¹ = H * statedSUToSL F 6 (2 ^ f) W * H⁻¹ at h
    refine statedSUToSL_injective F 6 (2 ^ f) ?_
    have h2 := congrArg (fun t : SL(6, L) => H⁻¹ * t * H) h
    simpa [mul_assoc] using h2
  have hΨsurj : Function.Surjective Ψ := by
    intro X
    obtain ⟨Y, hYU, hYeq⟩ := (hfix X.1).1 X.2
    let Ysl : SL(6, L) := ⟨Y, hYU.2.1⟩
    have hYsl : Matrix.SpecialLinearGroup.toGL Ysl = Y := Units.ext rfl
    obtain ⟨Z, hZ⟩ := (mem_range_statedSUToSL_iff (ℓ := 2) (f := f) (n := 6) Nat.prime_two F
      hFmem hFcard (by norm_num) Ysl).mpr (by rw [hYsl]; exact hYU)
    refine ⟨Z, Subtype.ext (Matrix.SpecialLinearGroup.toGL_injective ?_)⟩
    change Matrix.SpecialLinearGroup.toGL (H * statedSUToSL F 6 (2 ^ f) Z * H⁻¹) =
      Matrix.SpecialLinearGroup.toGL (X : SL(6, L))
    rw [map_mul, map_mul, map_inv, hZ, hYsl]
    exact hYeq.symm
  exact ⟨Ψ, hΨinj, hΨsurj⟩

private lemma unitary_range_disjoint_kernel {K : Type} [Field K] [Finite K]
    {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L 2]
    {f : ℕ} (hK : Nat.card K = 2 ^ f)
    {Φ' : SL(6, L) ≃* SL(6, L)} {H : SL(6, L)}
    (hfix : ∀ X : SL(6, L), X ∈ fixSubgroup Φ' ↔
      ∃ Y ∈ unitarySet (Nat.card K) 6, Matrix.SpecialLinearGroup.toGL X =
        Matrix.SpecialLinearGroup.toGL H * Y * (Matrix.SpecialLinearGroup.toGL H)⁻¹)
    {J : Type*} [Group J] [Finite J] (ρ : ↥(fixSubgroup Φ') →* J)
    (hc : ∀ z ∈ ρ.ker, ∀ u : ↥(fixSubgroup Φ'), z * u = u * z) (hk : Nat.card ρ.ker ∣ 6)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hdvd : q ∣ Nat.card K - 1)
    {F : Subfield L} {ψJ : (Fin 3 → rootsOfUnity q F) →* ↥(fixSubgroup Φ')}
    (hEcard : Nat.card ↥(ψJ.range) = q ^ 3) :
    Disjoint ψJ.range ρ.ker := by
  classical
  rcases eq_or_ne q 3 with hq3 | hq3
  ·
    have h3 : ¬ 3 ∣ Nat.card K + 1 := by
      rw [hq3] at hdvd
      intro h
      have h2 : 3 ∣ Nat.card K + 1 - (Nat.card K - 1) := Nat.dvd_sub h hdvd
      have hsub : Nat.card K + 1 - (Nat.card K - 1) = 2 := by
        have := Nat.card_pos (α := K)
        omega
      rw [hsub] at h2
      norm_num at h2
    have hker : ρ.ker = ⊥ := by
      rw [eq_bot_iff]
      intro z hz
      rw [Subgroup.mem_bot]
      exact eq_one_of_mem_center rfl hfix h3
        (Subgroup.mem_center_iff.mpr fun u => (hc z hz u).symm)
    rw [hker]
    exact disjoint_bot_right
  ·
    have hq5 : 5 ≤ q := by
      have h2 : 2 ≤ q := hq.two_le
      by_contra h
      push Not at h
      interval_cases q
      · exact absurd rfl hq2
      · exact absurd rfl hq3
      · norm_num at hq
    have hq6 : ¬ q ∣ 6 := by
      intro h
      have h6 : q ≤ 6 := Nat.le_of_dvd (by norm_num) h
      interval_cases q
      · norm_num at h
      · exact absurd hq (by norm_num)
    have hqker : ¬ q ∣ Nat.card ρ.ker := fun h => hq6 (h.trans hk)
    have hcop : Nat.Coprime (q ^ 3) (Nat.card ρ.ker) :=
      Nat.Coprime.pow_left 3 ((Nat.Prime.coprime_iff_not_dvd hq).mpr hqker)
    have hcop' : Nat.Coprime (Nat.card ↥(ψJ.range)) (Nat.card ρ.ker) := by
      rw [hEcard]; exact hcop
    exact Subgroup.disjoint_of_coprime_natCard hcop'

private lemma one_le_f_and_two_le_pow {K : Type} [Finite K] [Nontrivial K] {f : ℕ}
    (hK : Nat.card K = 2 ^ f) :
    1 ≤ f ∧ 2 ≤ 2 ^ f := by
  have h2 : 1 < Nat.card K := Finite.one_lt_card
  rw [hK] at h2
  have hf : 1 ≤ f := by
    by_contra h
    push Not at h
    interval_cases f
    simp at h2
  refine ⟨hf, ?_⟩
  calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf

private lemma exists_elemAbelian_pRank_three_of_disjoint_ker {A G J : Type*} [Group A] [Group G]
    [Group J] [Finite J] {q : ℕ} (hq : q.Prime) {ρ : G →* J} {ψJ : A →* G}
    (hψJinj : Function.Injective ψJ) (hEel : IsElemAbelian q ψJ.range)
    (hAcard : Nat.card A = q ^ 3) (hdisj : Disjoint ψJ.range ρ.ker) :
    ∃ F : Subgroup J, IsElemAbelian q F ∧ 3 ≤ CFSG.Open.pRank q F := by
  have hinj : Function.Injective (ρ.comp ψJ) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro a ha
    rw [MonoidHom.mem_ker] at ha
    have hmem : ψJ a ∈ ψJ.range ⊓ ρ.ker := ⟨⟨a, rfl⟩, ha⟩
    rw [hdisj.eq_bot] at hmem
    rw [Subgroup.mem_bot] at hmem
    exact hψJinj (by rw [hmem, map_one])
  have hrange : (ρ.comp ψJ).range = ψJ.range.map ρ := by
    rw [MonoidHom.range_eq_map, MonoidHom.range_eq_map, Subgroup.map_map]
  have hcard : Nat.card ↥((ρ.comp ψJ).range) = q ^ 3 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
    exact hAcard
  refine ⟨ψJ.range.map ρ, hEel.map ρ, ?_⟩
  exact CFSG.SectionRank.le_pRank hq.one_lt le_rfl (hEel.map ρ) (hrange ▸ hcard)

theorem exists_elemAbelian_pRank_three_of_fixSubgroup_unitary
    (hℓ2 : ℓ = 2) (hK : Nat.card K = ℓ ^ f)
    {Φ' : SL(6, L) ≃* SL(6, L)} {H : SL(6, L)}
    (hfix : ∀ X : SL(6, L), X ∈ fixSubgroup Φ' ↔
      ∃ Y ∈ unitarySet (ℓ ^ f) 6, Matrix.SpecialLinearGroup.toGL X =
        Matrix.SpecialLinearGroup.toGL H * Y * (Matrix.SpecialLinearGroup.toGL H)⁻¹)
    {J : Type*} [Group J] [Finite J] (ρ : ↥(fixSubgroup Φ') →* J)
    (hρ : Function.Surjective ρ)
    (hc : ∀ z ∈ ρ.ker, ∀ u : ↥(fixSubgroup Φ'), z * u = u * z)
    (hk : Nat.card ρ.ker ∣ 6) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hdvd : q ∣ Nat.card K - 1) :
    ∃ F : Subgroup J, IsElemAbelian q F ∧ 3 ≤ CFSG.Open.pRank q F := by
  subst hℓ2
  classical
  haveI : NeZero q := ⟨hq.ne_zero⟩
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have hdvd' : q ∣ 2 ^ f - 1 := by rw [hK] at hdvd; exact hdvd
  obtain ⟨hf1, h2f⟩ := one_le_f_and_two_le_pow hK
  set F : Subfield L := (iterateFrobenius L 2 (2 * f)).eqLocusField (RingHom.id L) with hFdef
  have hq0sq : (2 ^ f) ^ 2 = 2 ^ (2 * f) := by rw [← pow_mul, mul_comm]
  have hF2 : ∀ c : L, c ∈ F ↔ c ^ 2 ^ (2 * f) = c := fun c => by
    rw [hFdef, RingHom.mem_eqLocusField, iterateFrobenius_def, RingHom.id_apply]
  have hFmem : ∀ c : L, c ∈ F ↔ c ^ (2 ^ f) ^ 2 = c := fun c => by
    rw [hq0sq]; exact hF2 c
  have hFcard : Nat.card F = (2 ^ f) ^ 2 := by
    rw [hq0sq, ← CFSG.RankThree.Classical2.natCard_setOf_pow_eq_self (Ω := L) (ℓ := 2)
      (by omega : 2 * f ≠ 0)]
    exact Nat.card_congr (Equiv.subtypeEquivRight hF2)
  haveI : Finite F := Nat.finite_of_card_ne_zero (by
    rw [hFcard]
    exact (pow_pos (pow_pos (by norm_num) f) 2).ne')
  haveI : Fintype F := Fintype.ofFinite F
  haveI : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2 * f) (by
    rw [← Nat.card_eq_fintype_card, hFcard, hq0sq])
  obtain ⟨ωu, hωpow, hωne, hω0, hωinv, h1ω, hdet⟩ :=
    exists_unitary_root (F := F) hFcard h2f
  let φ : F →+* F := iterateFrobenius F 2 f
  have hφdef : ∀ c : F, φ c = c ^ 2 ^ f := fun c => iterateFrobenius_def 2 f c
  have hφω : φ (ωu : F) = ((ωu : F))⁻¹ := by rw [hφdef]; exact hωinv
  have hq_dvd_F : q ∣ Nat.card F - 1 := by
    have hdecomp : Nat.card F - 1 = (2 ^ f - 1) * (2 ^ f + 1) := by
      rw [hFcard, mul_comm, ← CFSG.ClassicalGroups.Unitary.sq_sub_one_eq (2 ^ f) (by omega)]
    rw [hdecomp]
    exact Dvd.dvd.mul_right hdvd' _
  have hAcard : Nat.card (Fin 3 → rootsOfUnity q F) = q ^ 3 := by
    rw [Nat.card_pi]
    simp only [CFSG.LinearGroups.card_rootsOfUnity_of_dvd (K := F) (d := q) hq_dvd_F]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  obtain ⟨ψ, hψinj⟩ := exists_unitary_psi (F := F) hdvd' hω0 hωinv hdet hφdef hφω
  obtain ⟨Ψ, hΨinj, hΨsurj⟩ :=
    exists_fixSubgroup_embedding (F := F) hFmem hFcard hfix
  haveI hFfin : Finite ↥(fixSubgroup Φ') := Finite.of_surjective Ψ hΨsurj
  let ψJ : (Fin 3 → rootsOfUnity q F) →* ↥(fixSubgroup Φ') := Ψ.comp ψ
  have hψJinj : Function.Injective ψJ := hΨinj.comp hψinj
  have hEcard : Nat.card ↥(ψJ.range) = q ^ 3 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hψJinj).toEquiv]
    exact hAcard
  have hEel : IsElemAbelian q ψJ.range :=
    CFSG.HardMathSupport.Timmesfeld.FieldBonus.isElemAbelian_range_of_comm_pow
      (fun a b => mul_comm a b)
      (fun a => funext fun i => rootsOfUnity_pow_eq_one (a i)) ψJ
  have hfixK : ∀ X : SL(6, L), X ∈ fixSubgroup Φ' ↔
      ∃ Y ∈ unitarySet (Nat.card K) 6, Matrix.SpecialLinearGroup.toGL X =
        Matrix.SpecialLinearGroup.toGL H * Y * (Matrix.SpecialLinearGroup.toGL H)⁻¹ := by
    simpa only [← hK] using hfix
  have hdisj : Disjoint ψJ.range ρ.ker :=
    unitary_range_disjoint_kernel hK hfixK ρ hc hk hq hq2 hdvd hEcard
  exact exists_elemAbelian_pRank_three_of_disjoint_ker hq hψJinj hEel hAcard hdisj

end Unitary

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE7Three
