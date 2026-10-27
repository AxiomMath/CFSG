module

public import CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.TOdd.FullLin
public import CFSG.RankThree.PartTwo.KFacts.AutPSU

import Mathlib.Tactic.Group
import Mathlib.Tactic.Module
import Mathlib.Tactic.NoncommRing
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.TOdd

open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.ClassicalGroups.UnitaryFlag (unitarySU mem_unitarySU_iff)
open CFSG.RankThree.PartTwo.KFacts (unitaryIsom3 suConj coe_suConj mem_unitaryIsom3)

section MatrixLemmasU

open Matrix

variable {p n : ℕ} {F : Type} [Field F]

theorem adjU_add (hF : UnitaryFieldData p n F) (A B : Matrix (Fin 3) (Fin 3) F) :
    ((A + B).map hF.bar)ᵀ = (A.map hF.bar)ᵀ + (B.map hF.bar)ᵀ := by
  rw [Matrix.map_add _ (map_add hF.bar), Matrix.transpose_add]

theorem adjU_mul (hF : UnitaryFieldData p n F) (A B : Matrix (Fin 3) (Fin 3) F) :
    ((A * B).map hF.bar)ᵀ = (B.map hF.bar)ᵀ * (A.map hF.bar)ᵀ := by
  rw [Matrix.map_mul (f := hF.bar), Matrix.transpose_mul]

theorem adjU_smul (hF : UnitaryFieldData p n F) (c : F) (A : Matrix (Fin 3) (Fin 3) F) :
    ((c • A).map hF.bar)ᵀ = hF.bar c • (A.map hF.bar)ᵀ := by
  rw [Matrix.map_smul' _ _ _ (map_mul hF.bar), Matrix.transpose_smul]

theorem adjU_one (hF : UnitaryFieldData p n F) :
    ((1 : Matrix (Fin 3) (Fin 3) F).map hF.bar)ᵀ = 1 := by
  rw [Matrix.map_one _ (map_zero hF.bar) (map_one hF.bar), Matrix.transpose_one]

theorem three_ne_zero_of_cube_rootU {ω : F} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) : (3 : F) ≠ 0 := by
  intro h
  apply hω1
  have h' : (ω - 1) ^ 3 = 0 := by linear_combination hω3 + (ω - ω ^ 2) * h
  exact sub_eq_zero.1 (pow_eq_zero_iff (by norm_num) |>.1 h')

theorem cube_root_sq_add_eq_zeroU {ω : F} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) :
    ω ^ 2 + ω + 1 = 0 := by
  have h : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by linear_combination hω3
  rcases mul_eq_zero.1 h with h | h
  · exact absurd (sub_eq_zero.1 h) hω1
  · exact h

theorem exists_isom_commute_det_eq_aux (hF : UnitaryFieldData p n F)
    {S : Matrix (Fin 3) (Fin 3) F} (hS3 : S ^ 3 = 1) (hdet : S.det = 1) (hns : ∀ r : F, S ≠ r • 1)
    (hSu : (S.map hF.bar)ᵀ * S = 1) {ω : F} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1)
    {μ : F} (hμ : hF.bar μ * μ = 1) :
    ∃ Z : Matrix (Fin 3) (Fin 3) F, Z * S = S * Z ∧ Z.det = μ ∧ (Z.map hF.bar)ᵀ * Z = 1 := by
  have h3 : (3 : F) ≠ 0 := three_ne_zero_of_cube_rootU hω3 hω1
  have hωs := cube_root_sq_add_eq_zeroU hω3 hω1
  obtain ⟨P, hP, hSP⟩ := exists_eigenbasis hS3 hdet hns hω3 hω1
  have hPdet : P.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det P).1 hP).ne_zero
  have hS3' : S * (S * S) = 1 := by rw [← pow_three]; exact hS3
  have hS3'' : S * S * S = 1 := by rw [mul_assoc]; exact hS3'
  have hS4 : S * S * (S * S) = S := by
    rw [show S * S * (S * S) = S * S * S * S by noncomm_ring, hS3'', one_mul]
  have hSS : (S.map hF.bar)ᵀ = S * S := by
    calc (S.map hF.bar)ᵀ = (S.map hF.bar)ᵀ * (S * (S * S)) := by rw [hS3', mul_one]
      _ = ((S.map hF.bar)ᵀ * S) * (S * S) := by rw [← mul_assoc]
      _ = S * S := by rw [hSu, one_mul]
  set T : Matrix (Fin 3) (Fin 3) F := 1 + S + S * S with hT
  set c : F := (3 : F)⁻¹ with hc
  set E : Matrix (Fin 3) (Fin 3) F := c • T with hE
  have hTT : T * T = (3 : F) • T := by
    have e : T * T = (1 + S + S * S) + (S + S * S + S * (S * S)) +
        (S * S + S * S * S + S * S * (S * S)) := by
      rw [hT]; noncomm_ring
    rw [e, hS3', hS3'', hS4, hT]
    module
  have hE2 : E * E = E := by
    rw [hE, smul_mul_assoc, mul_smul_comm, smul_smul, hTT, smul_smul]
    congr 1
    rw [hc]; field_simp
  have hbc : hF.bar c = c := by rw [hc, map_inv₀, map_ofNat]
  have hEadj : (E.map hF.bar)ᵀ = E := by
    rw [hE, adjU_smul, hbc, hT, adjU_add, adjU_add, adjU_mul, adjU_one, hSS, hS4]
    congr 1
    abel
  have hEP : E * P = P * diagonal ![1, 0, 0] := by
    set Δ : Matrix (Fin 3) (Fin 3) F := diagonal ![1, ω, ω ^ 2] with hΔ
    have h4 : ω ^ 4 = ω := by
      calc ω ^ 4 = ω ^ 3 * ω := by ring
        _ = ω := by rw [hω3, one_mul]
    have hΔ3 : (1 : Matrix (Fin 3) (Fin 3) F) + Δ + Δ * Δ = diagonal ![(3 : F), 0, 0] := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [hΔ, diagonal_apply, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply]
      · norm_num
      · linear_combination hωs
      · linear_combination hωs + h4
    have hSSP : S * S * P = P * Δ * Δ := by rw [mul_assoc, hSP, ← mul_assoc, hSP]
    have hTP : T * P = P * diagonal ![(3 : F), 0, 0] := by
      rw [← hΔ3, hT, add_mul, add_mul, one_mul, hSP, hSSP]
      noncomm_ring
    have hD3 : c • (diagonal ![(3 : F), 0, 0] : Matrix (Fin 3) (Fin 3) F) =
        diagonal ![1, 0, 0] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [diagonal_apply, hc, h3]
    rw [hE, smul_mul_assoc, hTP, ← mul_smul_comm, hD3]
  refine ⟨1 + (μ - 1) • E, ?_, ?_, ?_⟩
  · have hSE : S * E = E * S := by
      rw [hE, hT, smul_mul_assoc, mul_smul_comm]
      congr 1
      noncomm_ring
    rw [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, hSE]
  · have hD : (1 : Matrix (Fin 3) (Fin 3) F) + (μ - 1) • diagonal ![(1 : F), 0, 0] =
        diagonal ![μ, 1, 1] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [diagonal_apply]
    have hZP : (1 + (μ - 1) • E) * P = P * diagonal ![μ, 1, 1] := by
      rw [← hD, add_mul, one_mul, smul_mul_assoc, hEP, mul_add, mul_one, mul_smul_comm]
    have h := congrArg Matrix.det hZP
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal] at h
    simp only [Fin.prod_univ_three] at h
    simp at h
    exact mul_right_cancel₀ hPdet (by rw [h, mul_comm])
  · have hZadj : ((1 + (μ - 1) • E).map hF.bar)ᵀ = 1 + (hF.bar μ - 1) • E := by
      rw [adjU_add, adjU_one, adjU_smul, hEadj, map_sub, map_one]
    rw [hZadj]
    have key : (1 + (hF.bar μ - 1) • E) * (1 + (μ - 1) • E) =
        1 + ((hF.bar μ - 1) + (μ - 1) + (hF.bar μ - 1) * (μ - 1)) • E := by
      simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, smul_smul, hE2]
      module
    rw [key]
    have h0 : (hF.bar μ - 1) + (μ - 1) + (hF.bar μ - 1) * (μ - 1) = 0 := by
      linear_combination hμ
    rw [h0, zero_smul, add_zero]

end MatrixLemmasU

section IsometryU

local notation "GL₃" => Matrix.GeneralLinearGroup (Fin 3)

variable {p n : ℕ} {F : Type} [Field F] (hF : UnitaryFieldData p n F)

theorem norm_det_isomU {A : GL₃ F} (hA : A ∈ unitaryIsom3 hF) :
    hF.bar (A : Matrix (Fin 3) (Fin 3) F).det * (A : Matrix (Fin 3) (Fin 3) F).det = 1 := by
  have h := congrArg Matrix.det (mem_unitaryIsom3.1 hA)
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h
  rwa [← RingHom.mapMatrix_apply, ← RingHom.map_det] at h

theorem det_mem_rootsOfUnityU {A : GL₃ F} (hA : A ∈ unitaryIsom3 hF) :
    Matrix.GeneralLinearGroup.det A ∈ rootsOfUnity (p ^ n + 1) F := by
  rw [mem_rootsOfUnity, Units.ext_iff, Units.val_pow_eq_pow_val, Units.val_one,
    ← hF.norm_eq_pow, UnitaryFieldData.norm, Matrix.GeneralLinearGroup.val_det_apply, mul_comm]
  exact norm_det_isomU hF hA

theorem scalarU_mem_unitaryIsom3 {w : Fˣ} (hw : w ∈ rootsOfUnity (p ^ n + 1) F) :
    Matrix.GeneralLinearGroup.scalar (Fin 3) w ∈ unitaryIsom3 hF := by
  rw [mem_unitaryIsom3, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.diagonal_map (map_zero hF.bar), Matrix.diagonal_transpose,
    Matrix.diagonal_mul_diagonal]
  have h1 : hF.bar (w : F) * (w : F) = 1 := by
    rw [mul_comm, ← UnitaryFieldData.norm, hF.norm_eq_pow, ← Units.val_pow_eq_pow_val,
      (mem_rootsOfUnity _ _).1 hw, Units.val_one]
  simp only [h1]
  exact Matrix.diagonal_one

theorem exists_isom_commute_det_eq (h3 : 3 ∣ p ^ n + 1) {S : unitarySU p n F 3} (hS3 : S ^ 3 = 1)
    (hns : ∀ r : F, ((S : GL₃ F) : Matrix (Fin 3) (Fin 3) F) ≠ r • 1)
    (μ : Fˣ) (hμ : μ ∈ rootsOfUnity (p ^ n + 1) F) :
    ∃ Z : unitaryIsom3 hF, (Z : GL₃ F) * (S : GL₃ F) = (S : GL₃ F) * (Z : GL₃ F) ∧
      Matrix.GeneralLinearGroup.det (Z : GL₃ F) = μ := by
  haveI := hF.finite
  obtain ⟨hSdet, hSu⟩ := (mem_unitarySU_iff hF).1 S.2
  have hS3' : ((S : GL₃ F) : Matrix (Fin 3) (Fin 3) F) ^ 3 = 1 := by
    have h := congrArg (fun s : unitarySU p n F 3 => ((s : GL₃ F) : Matrix (Fin 3) (Fin 3) F)) hS3
    simpa using h
  have h3card : 3 ∣ Nat.card F - 1 := by
    have hq := hF.one_lt_pow
    have hsq : (p ^ n) ^ 2 - 1 = (p ^ n + 1) * (p ^ n - 1) := by
      zify [hq.le, Nat.one_le_pow 2 (p ^ n) (by omega)]
      ring
    rw [hF.card_eq_sq, hsq]
    exact Dvd.dvd.mul_right h3 _
  obtain ⟨ω, hω3, hω1⟩ := exists_primitive_cube_root h3card
  have hμ' : hF.bar (μ : F) * (μ : F) = 1 := by
    rw [mul_comm, ← UnitaryFieldData.norm, hF.norm_eq_pow, ← Units.val_pow_eq_pow_val,
      (mem_rootsOfUnity _ _).1 hμ, Units.val_one]
  obtain ⟨Z, hZS, hZdet, hZu⟩ :=
    exists_isom_commute_det_eq_aux hF hS3' hSdet hns hSu hω3 hω1 hμ'
  let Zg : GL₃ F := Matrix.GeneralLinearGroup.mkOfDetNeZero Z (by rw [hZdet]; exact μ.ne_zero)
  have hZg : (Zg : Matrix (Fin 3) (Fin 3) F) = Z := rfl
  refine ⟨⟨Zg, mem_unitaryIsom3.2 (by rw [hZg]; exact hZu)⟩, ?_, ?_⟩
  · apply Units.ext
    exact hZS
  · apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply]
    exact hZdet

theorem exists_special_conj_eq_unitary (h3 : 3 ∣ p ^ n + 1) {S : unitarySU p n F 3}
    (hS3 : S ^ 3 = 1) (hns : ∀ r : F, ((S : GL₃ F) : Matrix (Fin 3) (Fin 3) F) ≠ r • 1)
    (A : unitaryIsom3 hF) :
    ∃ M : unitarySU p n F 3, M * S * M⁻¹ = suConj hF A S := by
  obtain ⟨Z, hZ, hZdet⟩ := exists_isom_commute_det_eq hF h3 hS3 hns
    (Matrix.GeneralLinearGroup.det (A : GL₃ F))⁻¹ (inv_mem (det_mem_rootsOfUnityU hF A.2))
  have hMu : (A : GL₃ F) * (Z : GL₃ F) ∈ unitaryIsom3 hF := mul_mem A.2 Z.2
  have hMdet : (((A : GL₃ F) * (Z : GL₃ F) : GL₃ F) : Matrix (Fin 3) (Fin 3) F).det = 1 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply, map_mul, hZdet, mul_inv_cancel, Units.val_one]
  refine ⟨⟨(A : GL₃ F) * (Z : GL₃ F), (mem_unitarySU_iff hF).2 ⟨hMdet, mem_unitaryIsom3.1 hMu⟩⟩, ?_⟩
  apply Subtype.ext
  rw [coe_suConj]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  calc (A : GL₃ F) * (Z : GL₃ F) * (S : GL₃ F) * ((A : GL₃ F) * (Z : GL₃ F))⁻¹
      = (A : GL₃ F) * ((Z : GL₃ F) * (S : GL₃ F)) * (Z : GL₃ F)⁻¹ * (A : GL₃ F)⁻¹ := by group
    _ = (A : GL₃ F) * ((S : GL₃ F) * (Z : GL₃ F)) * (Z : GL₃ F)⁻¹ * (A : GL₃ F)⁻¹ := by rw [hZ]
    _ = (A : GL₃ F) * (S : GL₃ F) * (A : GL₃ F)⁻¹ := by group

end IsometryU

section ActsViaU

local notation "GL₃" => Matrix.GeneralLinearGroup (Fin 3)

variable {G : Type*} [Group G] {p n : ℕ} {F : Type} [Field F] (hF : UnitaryFieldData p n F)

@[expose] def LayerActsViaU {x : G} (e : layerOf x ≃* unitarySU p n F 3) (g : G)
    (A : unitaryIsom3 hF) : Prop :=
  ∀ d d' : layerOf x, (d' : G) = g * d * g⁻¹ → e d' = suConj hF A (e d)

variable {hF} {x : G} {e : layerOf x ≃* unitarySU p n F 3} {g g' : G} {A A' : unitaryIsom3 hF}

theorem LayerActsViaU.one : LayerActsViaU hF e (1 : G) 1 := by
  intro d d' hd
  have : d' = d := Subtype.ext (by simpa using hd)
  subst this
  simp

theorem LayerActsViaU.mul (hg : g ∈ Subgroup.centralizer ({x} : Set G))
    (hA : LayerActsViaU hF e g A) (hA' : LayerActsViaU hF e g' A') :
    LayerActsViaU hF e (g' * g) (A' * A) := by
  intro d d' hd
  have hd'' : g * (d : G) * g⁻¹ ∈ layerOf x := conj_mem_layerOf hg d.2
  have h1 := hA d ⟨g * d * g⁻¹, hd''⟩ rfl
  have h2 := hA' ⟨g * d * g⁻¹, hd''⟩ d' (by rw [hd]; group)
  rw [h2, h1, map_mul, MulAut.mul_apply]

theorem LayerActsViaU.pow (hg : g ∈ Subgroup.centralizer ({x} : Set G))
    (hA : LayerActsViaU hF e g A) (k : ℕ) : LayerActsViaU hF e (g ^ k) (A ^ k) := by
  induction k with
  | zero => simpa using (LayerActsViaU.one (hF := hF) (e := e))
  | succ k ih =>
    rw [pow_succ', pow_succ']
    exact LayerActsViaU.mul (Subgroup.pow_mem _ hg k) ih hA

theorem mem_sup_of_conj_eq_unitary (hg : g ∈ Subgroup.centralizer ({x} : Set G)) (r : layerOf x)
    (hconj : ∀ d : layerOf x, g * (d : G) * g⁻¹ = (r : G) * d * (r : G)⁻¹) :
    g ∈ layerOf x ⊔ torusOf x := by
  have hrC : (r : G) ∈ Subgroup.centralizer ({x} : Set G) := layerOf_le_centralizer x r.2
  have hl : (r : G)⁻¹ * g ∈ torusOf x := by
    refine ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ hrC) hg, ?_⟩
    show (r : G)⁻¹ * g ∈ Subgroup.centralizer (layerOf x : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    have h := hconj ⟨d, hd⟩
    simp only at h
    calc d * ((r : G)⁻¹ * g) = (r : G)⁻¹ * ((r : G) * d * (r : G)⁻¹) * g := by group
      _ = (r : G)⁻¹ * (g * d * g⁻¹) * g := by rw [h]
      _ = (r : G)⁻¹ * g * d := by group
  have := Subgroup.mul_mem_sup r.2 hl
  simpa using this

theorem mem_sup_of_actsViaU (hg : g ∈ Subgroup.centralizer ({x} : Set G))
    (hA : LayerActsViaU hF e g A) (w : Fˣ) (hw : w ∈ rootsOfUnity (p ^ n + 1) F)
    (hdet : w ^ 3 = Matrix.GeneralLinearGroup.det (A : GL₃ F)) :
    g ∈ layerOf x ⊔ torusOf x := by
  set c : GL₃ F := Matrix.GeneralLinearGroup.scalar (Fin 3) w⁻¹ with hc
  have hcmem : c ∈ unitaryIsom3 hF := scalarU_mem_unitaryIsom3 hF (inv_mem hw)
  have hMmem : c * (A : GL₃ F) ∈ unitaryIsom3 hF := mul_mem hcmem A.2
  have hdet1 : ((c * (A : GL₃ F) : GL₃ F) : Matrix (Fin 3) (Fin 3) F).det = 1 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply, map_mul, hc,
      Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, inv_pow, ← hdet, inv_mul_cancel,
      Units.val_one]
  set M : unitarySU p n F 3 :=
    ⟨c * (A : GL₃ F), (mem_unitarySU_iff hF).2 ⟨hdet1, mem_unitaryIsom3.1 hMmem⟩⟩ with hM
  set r : layerOf x := e.symm M with hr
  have hconj : ∀ d : layerOf x, g * (d : G) * g⁻¹ = (r : G) * d * (r : G)⁻¹ := by
    intro d
    have h1 := hA d ⟨g * d * g⁻¹, conj_mem_layerOf hg d.2⟩ rfl
    have h2 : e ⟨g * d * g⁻¹, conj_mem_layerOf hg d.2⟩ = e (r * d * r⁻¹) := by
      rw [h1, map_mul, map_mul, map_inv, hr, e.apply_symm_apply]
      apply Subtype.ext
      rw [coe_suConj]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hM]
      have hcomm : ∀ B : GL₃ F, c * B = B * c := Matrix.GeneralLinearGroup.scalar_commute w⁻¹
      calc (A : GL₃ F) * ((e d : unitarySU p n F 3) : GL₃ F) * (A : GL₃ F)⁻¹
          = ((A : GL₃ F) * ((e d : unitarySU p n F 3) : GL₃ F) * (A : GL₃ F)⁻¹) * c * c⁻¹ := by
            group
        _ = c * ((A : GL₃ F) * ((e d : unitarySU p n F 3) : GL₃ F) * (A : GL₃ F)⁻¹) * c⁻¹ := by
            rw [hcomm]
        _ = _ := by group
    have h3 := e.injective h2
    simpa using congrArg Subtype.val h3
  exact mem_sup_of_conj_eq_unitary hg r hconj

end ActsViaU

theorem exists_cube_mul_pow_unitary {H : Type*} [CommGroup H] [IsCyclic H] {u v : H}
    (hu : ¬ ∃ w : H, w ^ 3 = u) : ∃ k : ℕ, ∃ w : H, w ^ 3 = v * u ^ k := by
  obtain ⟨ζ, hζ⟩ := IsCyclic.exists_generator (α := H)
  obtain ⟨a, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hζ u)
  obtain ⟨b, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hζ v)
  have ha : ¬ (3 : ℤ) ∣ a := by
    rintro ⟨c, hc⟩
    refine hu ⟨ζ ^ c, ?_⟩
    rw [← zpow_natCast, ← zpow_mul, hc]
    norm_num [mul_comm]
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (3 : ℤ) ∣ b + k * a := by
    have h1 : a % 3 = 1 ∨ a % 3 = 2 := by omega
    have h2 : b % 3 = 0 ∨ b % 3 = 1 ∨ b % 3 = 2 := by omega
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 | h2
    · exact ⟨0, by omega⟩
    · exact ⟨2, by push_cast; omega⟩
    · exact ⟨1, by push_cast; omega⟩
    · exact ⟨0, by omega⟩
    · exact ⟨1, by push_cast; omega⟩
    · exact ⟨2, by push_cast; omega⟩
  obtain ⟨c, hc⟩ := hk
  refine ⟨k, ζ ^ c, ?_⟩
  rw [← zpow_natCast, ← zpow_mul, ← zpow_natCast, ← zpow_mul, ← zpow_add]
  congr 1
  push_cast
  linarith

section M1M2U

local notation "GL₃" => Matrix.GeneralLinearGroup (Fin 3)

variable {G : Type*} [Group G] {p n : ℕ} {F : Type} [Field F] (hF : UnitaryFieldData p n F)
  {x : G}

theorem layer_M1_of_unitary (e : layerOf x ≃* unitarySU p n F 3)
    (hact : ∀ g ∈ Subgroup.centralizer ({x} : Set G), ∃ A : unitaryIsom3 hF,
      LayerActsViaU hF e g A) :
    ∀ g ∈ Subgroup.centralizer ({x} : Set G), g ∉ layerOf x ⊔ torusOf x →
      ∀ g' ∈ Subgroup.centralizer ({x} : Set G), ∃ k : ℕ, g' * g ^ k ∈ layerOf x ⊔ torusOf x := by
  intro g hg hgn g' hg'
  obtain ⟨A, hA⟩ := hact g hg
  obtain ⟨A', hA'⟩ := hact g' hg'
  let u : rootsOfUnity (p ^ n + 1) F :=
    ⟨Matrix.GeneralLinearGroup.det (A : GL₃ F), det_mem_rootsOfUnityU hF A.2⟩
  let v : rootsOfUnity (p ^ n + 1) F :=
    ⟨Matrix.GeneralLinearGroup.det (A' : GL₃ F), det_mem_rootsOfUnityU hF A'.2⟩
  have hu : ¬ ∃ w : rootsOfUnity (p ^ n + 1) F, w ^ 3 = u := fun ⟨w, hw⟩ =>
    hgn (mem_sup_of_actsViaU hg hA (w : Fˣ) w.2 (congrArg Subtype.val hw))
  obtain ⟨k, w, hw⟩ := exists_cube_mul_pow_unitary (v := v) hu
  refine ⟨k, ?_⟩
  refine mem_sup_of_actsViaU (A := A' * A ^ k)
    (Subgroup.mul_mem _ hg' (Subgroup.pow_mem _ hg k))
    (LayerActsViaU.mul (Subgroup.pow_mem _ hg k) (hA.pow hg k) hA') (w : Fˣ) w.2 ?_
  have h := congrArg Subtype.val hw
  rw [Subgroup.coe_mul, Subgroup.coe_pow] at h
  rw [Subgroup.coe_mul, Subgroup.coe_pow, map_mul, map_pow]
  exact h

theorem layer_M2_of_unitary (h3 : 3 ∣ p ^ n + 1)
    (hZD : ∀ w ∈ layerOf x, (∀ d ∈ layerOf x, w * d = d * w) → w ∈ Subgroup.zpowers x)
    (e : layerOf x ≃* unitarySU p n F 3)
    (hact : ∀ g ∈ Subgroup.centralizer ({x} : Set G), ∃ A : unitaryIsom3 hF,
      LayerActsViaU hF e g A) :
    ∀ s ∈ layerOf x, s ^ 3 = 1 → s ∉ Subgroup.zpowers x →
      ∀ g ∈ Subgroup.centralizer ({x} : Set G), ∃ h ∈ layerOf x, h * s * h⁻¹ = g * s * g⁻¹ := by
  intro s hs hs3 hsx g hg
  set d : layerOf x := ⟨s, hs⟩ with hd
  have hS3 : e d ^ 3 = 1 := by
    have : d ^ 3 = 1 := Subtype.ext (by simpa using hs3)
    rw [← map_pow, this, map_one]
  have hns : ∀ r : F, (((e d : unitarySU p n F 3) : GL₃ F) : Matrix (Fin 3) (Fin 3) F) ≠ r • 1 := by
    intro r hr
    apply hsx
    refine hZD s hs fun d₂ hd₂ => ?_
    have hcomm : e d * e ⟨d₂, hd₂⟩ = e ⟨d₂, hd₂⟩ * e d := by
      apply Subtype.ext
      apply Units.ext
      simp only [Subgroup.coe_mul, Units.val_mul, hr]
      simp
    have := e.injective (by simpa using hcomm : e (d * ⟨d₂, hd₂⟩) = e (⟨d₂, hd₂⟩ * d))
    simpa using congrArg Subtype.val this
  obtain ⟨A, hA⟩ := hact g hg
  have hd' : g * s * g⁻¹ ∈ layerOf x := conj_mem_layerOf hg hs
  have h1 := hA d ⟨g * s * g⁻¹, hd'⟩ rfl
  obtain ⟨M, hM⟩ := exists_special_conj_eq_unitary hF h3 hS3 hns A
  refine ⟨((e.symm M : layerOf x) : G), (e.symm M).2, ?_⟩
  have h2 : e ⟨g * s * g⁻¹, hd'⟩ = e (e.symm M * d * (e.symm M)⁻¹) := by
    rw [h1, ← hM]
    simp only [map_mul, map_inv, e.apply_symm_apply]
  have h3 := e.injective h2
  simpa using (congrArg Subtype.val h3).symm

end M1M2U

section PackagedU

variable {G : Type*} [Group G] [Finite G] {x a' : G}

theorem centralizer_le_of_layer_unitary {p n : ℕ} {F : Type} [Field F]
    (hF : UnitaryFieldData p n F) (h3 : 3 ∣ p ^ n + 1)
    (e : layerOf x ≃* unitarySU p n F 3)
    (hact : ∀ g ∈ Subgroup.centralizer ({x} : Set G), ∃ A : unitaryIsom3 hF,
      ∀ d d' : layerOf x, (d' : G) = g * d * g⁻¹ → e d' = suConj hF A (e d))
    (hx3 : x ^ 3 = 1) (hxD : x ∈ layerOf x)
    (hZD : ∀ w ∈ layerOf x, (∀ d ∈ layerOf x, w * d = d * w) → w ∈ Subgroup.zpowers x)
    (hZ3 : ∀ z ∈ Subgroup.centralizer (layerOf x : Set G),
      (∃ k : ℕ, z ^ (3 ^ k) = 1) → z ∈ Subgroup.zpowers x)
    (ha'C : a' * x = x * a') (ha'3 : a' ^ 3 = 1) (ha'x : a' ∉ Subgroup.zpowers x)
    {Γ : Subgroup G} (hDΓ : layerOf x ≤ Γ)
    (hΓ : ∀ l ∈ Subgroup.centralizer ({x} : Set G), l * a' = a' * l → l ∈ Γ) :
    Subgroup.centralizer ({x} : Set G) ≤ Γ :=
  centralizer_le_of_layer hx3 hxD hZD hZ3 ha'C ha'3 ha'x (layer_M1_of_unitary hF e hact)
    (layer_M2_of_unitary hF h3 hZD e hact) hDΓ hΓ

end PackagedU

end CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.TOdd
