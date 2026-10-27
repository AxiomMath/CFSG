module

public import CFSG.ClassicalInvolution.Asc77.AscE189SL4
public import CFSG.ClassicalInvolution.Asc77.AscE189Comp

public section

namespace CFSG.ClassicalInvolution.Asc77

open Matrix CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.Phan
  CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits
open scoped MatrixGroups

section UnitaryCore

variable {K : Type} [Field K] {σ : K ≃+* K}

theorem conjTr_apply' {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (i j : Fin n) :
    conjTr σ A i j = σ (A j i) := by
  simp [conjTr]

theorem sl4_unitary_core (hσ : ∀ x, σ (σ x) = x) {A : Matrix (Fin 4) (Fin 4) K}
    (hE : Sl4Ent A) (hAA : A * A = -1) (hU : conjTr σ A * A = 1) :
    conjTr σ (sl4G A) * sl4G A = 1 ∧ σ (sl4b A) = sl4c A ∧ σ (sl4c A) * sl4c A = 1 := by
  have hA' : conjTr σ A = -A := by
    calc conjTr σ A = conjTr σ A * (-(A * A)) := by rw [hAA]; simp
      _ = -(conjTr σ A * A * A) := by simp [Matrix.mul_assoc]
      _ = -A := by rw [hU]; simp
  have hσA : ∀ i j, σ (A j i) = -A i j := fun i j => by
    have := congrFun (congrFun hA' i) j
    rw [conjTr_apply'] at this
    simpa using this
  have hσb : σ (sl4b A) = sl4c A := by
    unfold sl4b sl4c
    rw [map_sub, map_mul, map_mul, hσA 2 0, hσA 3 1, hσA 3 0, hσA 2 1]
    ring
  have hσc : σ (sl4c A) = sl4b A := by rw [← hσb, hσ]
  have hbc := hE.bc
  refine ⟨?_, hσb, by rw [hσc]; exact hbc⟩
  obtain ⟨z00, z01, z10, z11, z22, z23, z32, z33, r00, r01, r10, r11⟩ := hE
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [conjTr_apply', sl4G, Matrix.mul_apply, Fin.sum_univ_four, hσA, hσb]
  · linear_combination (-1 : K) * r00
  · linear_combination (sl4b A) * r01
  · linear_combination (sl4c A) * r10
  · linear_combination (-(sl4c A) * sl4b A) * r11 + hbc

theorem unitary_block_two {b cc : K} (hσb : σ b = cc) (hσc : σ cc * cc = 1) (hbc : b * cc = 1) :
    conjTr σ (!![0, b; -cc, 0] : Matrix (Fin 2) (Fin 2) K) * !![0, b; -cc, 0] = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [conjTr_apply', Matrix.mul_apply, Fin.sum_univ_two, hσb]
  · exact hσc
  · rw [mul_comm]
    exact hbc

end UnitaryCore


section SU4

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

variable (K p f) in
@[expose] noncomputable def suOf {n : ℕ} (M : Matrix (Fin n) (Fin n) K) (hdet : M.det = 1)
    (hM : conjTr (unitaryInvolution K p f) M * M = 1) : Su K p f n :=
  ⟨Matrix.SpecialLinearGroup.toGL ⟨M, hdet⟩, hdet, hM⟩

theorem suMat_suOf {n : ℕ} (M : Matrix (Fin n) (Fin n) K) (hdet : M.det = 1)
    (hM : conjTr (unitaryInvolution K p f) M * M = 1) :
    suMat (suOf K p f M hdet hM) = M := rfl

theorem suMat_blockEmb_four_zero (A : Su K p f 2) :
    suMat (blockEmb K p f 4 2 0 (by norm_num) A) =
      !![suMat A 0 0, suMat A 0 1, 0, 0; suMat A 1 0, suMat A 1 1, 0, 0; 0, 0, 1, 0;
        0, 0, 0, 1] := by
  rw [suMat_blockEmb]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [blockMat_apply]

theorem suMat_blockEmb_four_two (A : Su K p f 2) :
    suMat (blockEmb K p f 4 2 2 (by norm_num) A) =
      !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, suMat A 0 0, suMat A 0 1;
        0, 0, suMat A 1 0, suMat A 1 1] := by
  rw [suMat_blockEmb]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [blockMat_apply]

theorem suMat_center_eq_neg_one (hK : Nat.card K = (p ^ f) ^ 2) {n : ℕ} (hn : 3 ≤ n)
    {ζ : Su K p f n} (hζ : ζ ∈ Subgroup.center (Su K p f n)) (hζ1 : ζ ≠ 1) (hζ2 : ζ * ζ = 1) :
    suMat ζ = -1 := by
  obtain ⟨u, hu⟩ := exists_scalar_of_mem_center (isUnitaryInvolution_unitaryInvolution hK) hn hζ
  have hu' : suMat ζ = Matrix.scalar (Fin n) (u : K) := hu
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hsq : (u : K) * u = 1 := by
    have h := congrArg suMat hζ2
    rw [suMat_mul, hu', ← map_mul, suMat_one, ← map_one (Matrix.scalar (Fin n)),
      Matrix.scalar_inj] at h
    exact h
  rcases mul_self_eq_one_iff.mp hsq with h | h
  · exfalso
    apply hζ1
    apply suMat_injective
    rw [hu', h, map_one, suMat_one]
  · rw [hu', h, map_neg, map_one]


theorem e189SU4_std (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) {ζ a : Su K p f 4}
    (hζ : ζ ∈ Subgroup.center (Su K p f 4)) (hζ1 : ζ ≠ 1) (hζ2 : ζ * ζ = 1) (ha2 : a * a = ζ)
    (haz : a * rootInvSU K p f two_le_four * a⁻¹ = ζ * rootInvSU K p f two_le_four) :
    ∃ y α β : Su K p f 4, α ∈ rootSU2 K p f two_le_four ∧
      β ∈ conjSub a (rootSU2 K p f two_le_four) ∧ α ^ 4 = 1 ∧ β ^ 4 = 1 ∧
      y * a * y⁻¹ = α * β := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_charP_ne_two hp
  have hσ := isUnitaryInvolution_unitaryInvolution hK
  have hζm : suMat ζ = -1 := suMat_center_eq_neg_one hK (by norm_num) hζ hζ1 hζ2
  have hAA : suMat a * suMat a = -1 := by rw [← suMat_mul, ha2, hζm]
  have hAD : suMat a * Matrix.diagonal ![(-1 : K), -1, 1, 1] =
      -(Matrix.diagonal ![(-1 : K), -1, 1, 1] * suMat a) := by
    have h' : a * rootInvSU K p f two_le_four = ζ * rootInvSU K p f two_le_four * a := by
      calc a * rootInvSU K p f two_le_four
          = a * rootInvSU K p f two_le_four * a⁻¹ * a := by group
        _ = ζ * rootInvSU K p f two_le_four * a := by rw [haz]
    have := congrArg suMat h'
    simp only [suMat_mul, suMat_rootInvSU, hζm, negBlock_four_zero] at this
    simpa only [neg_mul, one_mul] using this
  have hU : conjTr (unitaryInvolution K p f) (suMat a) * suMat a = 1 := a.2.2
  have hE := sl4Ent_of h2 hAA hAD
  obtain ⟨hGU, hσb, hσc⟩ := sl4_unitary_core hσ.invol hE hAA hU
  have hbc : sl4b (suMat a) * sl4c (suMat a) = 1 := hE.bc
  have hGdet : (sl4G (suMat a)).det = 1 := hE.det_G
  have hAG := hE.mul_G
  set b : K := sl4b (suMat a) with hb
  set cc : K := sl4c (suMat a) with hcc
  have hdet1 : (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) K).det = 1 := by
    simp [Matrix.det_fin_two_of]
  have hU1 : conjTr (unitaryInvolution K p f) (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) K) *
      !![0, -1; 1, 0] = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [conjTr_apply', Matrix.mul_apply, Fin.sum_univ_two]
  have hdet2 : (!![0, b; -cc, 0] : Matrix (Fin 2) (Fin 2) K).det = 1 := by
    rw [Matrix.det_fin_two_of]
    linear_combination hbc
  have hU2 : conjTr (unitaryInvolution K p f) (!![0, b; -cc, 0] : Matrix (Fin 2) (Fin 2) K) *
      !![0, b; -cc, 0] = 1 := unitary_block_two hσb hσc hbc
  set g : Su K p f 4 := suOf K p f (sl4G (suMat a)) hGdet hGU with hg
  set A₁ : Su K p f 2 := suOf K p f !![0, -1; 1, 0] hdet1 hU1 with hA₁
  set A₂ : Su K p f 2 := suOf K p f !![0, b; -cc, 0] hdet2 hU2 with hA₂
  set α : Su K p f 4 := blockEmb K p f 4 2 0 (by norm_num) A₁ with hα
  set β : Su K p f 4 := blockEmb K p f 4 2 2 (by norm_num) A₂ with hβ
  have hαm : suMat α = !![0, -1, 0, 0; 1, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] := by
    rw [hα, suMat_blockEmb_four_zero]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hA₁, suMat_suOf]
  have hβm : suMat β = !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, b; 0, 0, -cc, 0] := by
    rw [hβ, suMat_blockEmb_four_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hA₂, suMat_suOf]
  have hαβ : suMat (α * β) = !![0, -1, 0, 0; 1, 0, 0, 0; 0, 0, 0, b; 0, 0, -cc, 0] := by
    rw [suMat_mul, hαm, hβm]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]
  have hag : a * g = g * (α * β) := by
    apply suMat_injective
    rw [suMat_mul, suMat_mul, hαβ, hg, suMat_suOf]
    exact hAG
  refine ⟨g⁻¹, α, β, ⟨A₁, rfl⟩, ?_, ?_, ?_, ?_⟩
  · have hconj : conjSub a (rootSU2 K p f two_le_four) =
        longRootGroupSU K p f (-(Matrix.diagonal ![(-1 : K), -1, 1, 1])) := by
      rw [rootSU2_eq_longRootGroupSU h2 two_le_four]
      show (longRootGroupSU K p f (negBlock K 4 0)).map (MulAut.conj a).toMonoidHom = _
      rw [← longRootGroupSU_conj]
      congr 1
      rw [negBlock_four_zero]
      calc suMat a * Matrix.diagonal ![(-1 : K), -1, 1, 1] * suMat a⁻¹
          = -(Matrix.diagonal ![(-1 : K), -1, 1, 1] * suMat a * suMat a⁻¹) := by rw [hAD]; simp
        _ = -Matrix.diagonal ![(-1 : K), -1, 1, 1] := by
            rw [Matrix.mul_assoc, suMat_mul_suMat_inv, Matrix.mul_one]
    rw [hconj, mem_longRootGroupSU, hβm]
    constructor
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]
  · have hA₁sq : A₁ * A₁ = negOneSU K p f := by
      apply suMat_injective
      rw [suMat_mul, suMat_negOneSU, hA₁, suMat_suOf]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    have h4 : A₁ ^ 4 = 1 := by
      rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two, hA₁sq, negOneSU_mul_self]
    rw [hα, ← map_pow, h4, map_one]
  · have hA₂sq : A₂ * A₂ = negOneSU K p f := by
      apply suMat_injective
      rw [suMat_mul, suMat_negOneSU, hA₂, suMat_suOf]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
      · exact hbc
      · rw [mul_comm]
        exact hbc
    have h4 : A₂ ^ 4 = 1 := by
      rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two, hA₂sq, negOneSU_mul_self]
    rw [hβ, ← map_pow, h4, map_one]
  · calc g⁻¹ * a * g⁻¹⁻¹ = g⁻¹ * (a * g) := by rw [inv_inv, mul_assoc]
      _ = α * β := by rw [hag, ← mul_assoc, inv_mul_cancel, one_mul]

end SU4


section Transport

variable {X Y : Type} [Group X] [Group Y]

theorem e189AtFam_of_conjClass_equiv [Finite X] (φ : X ≃* Y) {F0' : Subgroup Y} {d' : Y}
    (hd' : IsUniqueInvolution F0' d') (hC' : ∀ c : Y, c * d' = d' * c → conjSub c F0' = F0')
    (hstd' : ∀ ζ ∈ Subgroup.center Y, ζ ≠ 1 → ζ * ζ = 1 → ∀ a : Y, a * a = ζ →
      a * d' * a⁻¹ = ζ * d' → ∃ y α β : Y, α ∈ F0' ∧ β ∈ conjSub a F0' ∧ α ^ 4 = 1 ∧
        β ^ 4 = 1 ∧ y * a * y⁻¹ = α * β) :
    E189AtFam X {F | ∃ g : X, F = conjSub g (F0'.map φ.symm.toMonoidHom)} := by
  have hinj : ∀ x ∈ F0', φ.symm.toMonoidHom x = 1 → x = 1 := fun x _ h => by
    simpa using h
  have hd := isUniqueInvolution_map_of_injOn φ.symm.toMonoidHom hinj hd'
  have hconj : ∀ (c : Y) (K : Subgroup Y), conjSub (φ.symm c) (K.map φ.symm.toMonoidHom) =
      (conjSub c K).map φ.symm.toMonoidHom := fun c K => (map_conjSub_eq _ c K).symm
  refine e189AtFam_of_conjClass hd ?_ ?_
  · intro c hc
    have h1 : φ c * d' = d' * φ c := by
      have := congrArg φ hc
      simpa using this
    have h2 := hC' (φ c) h1
    have := hconj (φ c) F0'
    rw [h2] at this
    simpa using this
  · intro ζ hζ hζ1 hζ2 a ha2 haz
    have hζc : φ ζ ∈ Subgroup.center Y := (MulEquivClass.apply_mem_center_iff φ).mpr hζ
    obtain ⟨y, α, β, hα, hβ, hα4, hβ4, hy⟩ := hstd' (φ ζ) hζc (by simpa using hζ1)
      (by rw [← map_mul, hζ2, map_one]) (φ a) (by rw [← map_mul, ha2])
      (by
        have := congrArg φ haz
        simpa using this)
    refine ⟨φ.symm y, φ.symm α, φ.symm β, Subgroup.mem_map_of_mem _ hα, ?_, ?_, ?_, ?_⟩
    · have h := Subgroup.mem_map_of_mem φ.symm.toMonoidHom hβ
      have h' := hconj (φ a) F0'
      simp only [MulEquiv.symm_apply_apply] at h'
      rw [← h'] at h
      exact h
    · rw [← map_pow, hα4, map_one]
    · rw [← map_pow, hβ4, map_one]
    · have := congrArg φ.symm hy
      simpa using this

end Transport


section Model

variable {p e : ℕ} [Fact p.Prime]

theorem e189ModelAt_psu_four (hp2 : p ≠ 2) (hadm : StatedLieAdmissible .PSU 4 p e) :
    E189ModelAt p e .PSU 4 := by
  have hf : 1 ≤ e := hadm.2.1
  have hK : Nat.card (GaloisField p (2 * e)) = (p ^ e) ^ 2 :=
    CFSG.LieType.Universal.card_galoisField_two_mul p e hf
  obtain ⟨φ, hφ⟩ := CFSG.ClassicalInvolution.RouteD.psu_model_equiv hp2 hadm
  have hcl := isClassicalSL2_rootSU2 hK hp2 two_le_four
  have hodd := odd_natCard_fixedSubfield hK hp2
  have : Finite (modelUniv .PSU 4 p e Fact.out).K :=
    Finite.of_equiv _ φ.symm.toEquiv
  set F0 : Subgroup (modelUniv .PSU 4 p e Fact.out).K :=
    (rootSU2 (GaloisField p (2 * e)) p e two_le_four).map φ.symm.toMonoidHom with hF0
  have hmapmap : ∀ (R : Subgroup (modelUniv .PSU 4 p e Fact.out).K),
      (R.map φ.toMonoidHom).map φ.symm.toMonoidHom = R := fun R => by
    rw [Subgroup.map_map]
    have : φ.symm.toMonoidHom.comp φ.toMonoidHom = MonoidHom.id _ := by
      ext x
      simp
    rw [this, Subgroup.map_id]
  have hmapmap' : ∀ (R : Subgroup (Su (GaloisField p (2 * e)) p e 4)),
      (R.map φ.symm.toMonoidHom).map φ.toMonoidHom = R := fun R => by
    rw [Subgroup.map_map]
    have : φ.toMonoidHom.comp φ.symm.toMonoidHom = MonoidHom.id _ := by
      ext x
      simp
    rw [this, Subgroup.map_id]
  have hfund : fundamentalSubgroups .PSU (modelUniv .PSU 4 p e Fact.out).D =
      {F | ∃ g : (modelUniv .PSU 4 p e Fact.out).K, F = conjSub g F0} := by
    ext R
    rw [hφ R]
    constructor
    · intro hR
      obtain ⟨g', hg'⟩ := (mem_longRootSetU_iff (by norm_num : 2 ≤ 4)).mp hR
      refine ⟨φ.symm g', ?_⟩
      rw [hF0, ← hmapmap R, hg']
      exact map_conj_eq_conjSub_map φ.symm.toMonoidHom g' _
    · rintro ⟨g, rfl⟩
      refine (mem_longRootSetU_iff (by norm_num : 2 ≤ 4)).mpr ⟨φ g, ?_⟩
      rw [map_conjSub_eq φ.toMonoidHom g F0, hF0, hmapmap']
      rfl
  have key := e189AtFam_of_conjClass_equiv φ (isUniqueInvolution_of_isClassicalSL2 hcl hodd)
    (fun c hc => conjSub_eq_of_isClassicalSL2 hcl hc)
    (fun ζ hζ hζ1 hζ2 a ha2 haz => e189SU4_std hK hp2 hζ hζ1 hζ2 ha2 haz)
  unfold E189ModelAt modelFund ModelGrp
  rw [hfund]
  exact key

end Model

end CFSG.ClassicalInvolution.Asc77
