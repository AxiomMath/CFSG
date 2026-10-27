module

public import CFSG.ClassicalInvolution.Asc77.AscC25X6
public import CFSG.ClassicalInvolution.ModelFacts.Orth15OuterU4Model

public section

namespace CFSG.ClassicalInvolution.Asc77

open Matrix CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.ModelFacts.UnitaryAut CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.ClassicalInvolution.ModelFacts.Orth15.ChainU
  CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterU4 CFSG.LieType.Steinberg
  CFSG.ClassicalInvolution.RouteD CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Generic (modelUniv)
open scoped MatrixGroups

namespace C25X

section MatrixU

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

omit [Finite K] in
theorem zMat_pair01_u : zMat K 4 ({0, 1} : Finset (Fin 4)) = Matrix.diagonal ![-1, -1, 1, 1] := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [zMat]

omit [Finite K] in
theorem zMat_pair02_u : zMat K 4 ({0, 2} : Finset (Fin 4)) = Matrix.diagonal ![-1, 1, -1, 1] := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [zMat]

@[expose] noncomputable def diagSU4 {i : K} (hi : i * i = -1)
    (hσi : unitaryInvolution K p f i = -i) : Su K p f 4 :=
  have hσi' : iterateFrobenius K p f i = -i := hσi
  mkSU K p f (Matrix.diagonal ![i, -i, 1, 1]) (by
    rw [Matrix.det_diagonal, Fin.prod_univ_four]; simp; linear_combination -hi) (by
    rw [conjTr_diagonal, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    fin_cases a <;> simp [hσi, hσi'] <;> linear_combination -hi)

theorem suMat_diagSU4 {i : K} (hi : i * i = -1) (hσi : unitaryInvolution K p f i = -i) :
    suMat (diagSU4 (p := p) (f := f) hi hσi) = Matrix.diagonal ![i, -i, 1, 1] := rfl

theorem nc4_su4_matrix (h2 : (2 : K) ≠ 0) {i : K} (hi : i * i = -1)
    (hσi : unitaryInvolution K p f i = -i) :
    ∃ R₁ ∈ longRootSetU (K := K) (p := p) (f := f) (show 2 ≤ 4 by norm_num),
      ∃ R₂ ∈ longRootSetU (K := K) (p := p) (f := f) (show 2 ≤ 4 by norm_num),
        ∃ y ∈ R₁, ∃ x₂ ∈ R₂, y * y * y * y = 1 ∧ y * y ≠ 1 ∧ x₂ * x₂ = 1 ∧ x₂ ≠ 1 ∧
          x₂ * y = y * x₂ ∧ (y * y) * x₂ ∉ Subgroup.center (Su K p f 4) := by
  let T₁ : Pair 4 := ⟨{0, 1}, by decide⟩
  let T₂ : Pair 4 := ⟨{0, 2}, by decide⟩
  have hm1 : (-1 : K) ≠ 1 := fun h => h2 (by linear_combination -h)
  have hi4 : i * i * i * i = 1 := by linear_combination (i * i - 1) * hi
  have hx2c : suMat (zEltU K p f T₂) = Matrix.diagonal ![-1, 1, -1, 1] := zMat_pair02_u
  have hyc := suMat_diagSU4 (p := p) (f := f) hi hσi
  refine ⟨LcU K p f T₁, LcU_mem_longRootSetU h2 (by norm_num) T₁, LcU K p f T₂,
    LcU_mem_longRootSetU h2 (by norm_num) T₂, diagSU4 (p := p) (f := f) hi hσi, ?_,
    zEltU K p f T₂, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show diagSU4 (p := p) (f := f) hi hσi ∈ longRootGroupSU K p f (zMat K 4 T₁.1)
    rw [mem_longRootGroupSU, hyc]
    show Matrix.diagonal ![i, -i, 1, 1] * zMat K 4 ({0, 1} : Finset (Fin 4)) = _ ∧ _
    rw [zMat_pair01_u]
    constructor
    · ext a b
      fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Matrix.diagonal_apply]
    · ext a b
      fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Matrix.diagonal_apply]
  · show zEltU K p f T₂ ∈ longRootGroupSU K p f (zMat K 4 T₂.1)
    rw [mem_longRootGroupSU]
    refine ⟨rfl, ?_⟩
    rw [Matrix.mul_add, Matrix.mul_one]
    show zMat K 4 T₂.1 + zMat K 4 T₂.1 * zMat K 4 T₂.1 = _
    rw [zMat_mul_self, add_comm]
  · apply suMat_injective
    rw [suMat_mul, suMat_mul, suMat_mul, hyc, suMat_one]
    ext a b
    fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Matrix.diagonal_apply, hi4]
  · intro h
    have h' := congrArg (fun m : Su K p f 4 => suMat m 0 0) h
    simp [suMat_mul, hyc, Matrix.mul_apply, Matrix.diagonal_apply] at h'
    exact hm1 (by rw [← hi]; exact h')
  · exact zEltU_mul_self T₂
  · intro h
    have h' := congrArg (fun m : Su K p f 4 => suMat m 0 0) h
    simp only [hx2c, suMat_one] at h'
    simp at h'
    exact hm1 h'
  · apply suMat_injective
    rw [suMat_mul, suMat_mul, hx2c, hyc]
    ext a b
    fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Matrix.diagonal_apply]
  · intro h
    have hg := Subgroup.mem_center_iff.mp h (blockEmb K p f 4 2 0 (by norm_num) (jSU K p f))
    have hg' := congrArg (fun m : Su K p f 4 => suMat m 0 1) hg
    simp [suMat_mul, hx2c, hyc, suMat_blockEmb_zero, suMat_jSU, Matrix.mul_apply,
      Matrix.diagonal_apply] at hg'
    have h3 : (2 : K) * (i * i) = 0 := by linear_combination hg'
    rw [hi] at h3
    exact h2 (by linear_combination -h3)

end MatrixU

section Row

variable (p : ℕ) [Fact p.Prime]

theorem nc4SU : NC4SU p := by
  intro e hadm hp2 hq h3
  have hf : 1 ≤ e := hadm.2.1
  have : NeZero (2 * e) := ⟨by omega⟩
  have hK : Nat.card (GaloisField p (2 * e)) = (p ^ e) ^ 2 := card_galoisField_two_mul_eq hq
  obtain ⟨φ, hφ⟩ := psu_model_equiv hp2 hadm
  obtain ⟨ω, hω, hσω⟩ : ∃ ω : GaloisField p (2 * e), ω * ω = -1 ∧
      unitaryInvolution (GaloisField p (2 * e)) p e ω = -ω := by
    have : Fintype (GaloisField p (2 * e)) := Fintype.ofFinite _
    obtain ⟨ω, hω⟩ : ∃ ω : GaloisField p (2 * e), ω * ω = -1 := by
      have hsq : IsSquare (-1 : GaloisField p (2 * e)) := by
        rw [FiniteField.isSquare_neg_one_iff, ← Nat.card_eq_fintype_card, hK]
        have hm : p ^ e = 4 * (p ^ e / 4) + 3 := by omega
        rw [hm]
        ring_nf
        omega
      obtain ⟨ω, hω⟩ := hsq
      exact ⟨ω, hω.symm⟩
    refine ⟨ω, hω, ?_⟩
    rw [unitaryInvolution_apply]
    have hω4 : ω ^ 4 = 1 := by linear_combination (ω * ω - 1) * hω
    have hm : p ^ e = 4 * (p ^ e / 4) + 3 := by omega
    rw [hm, pow_add, pow_mul, hω4, one_pow, one_mul]
    linear_combination ω * hω
  have h2 : (2 : GaloisField p (2 * e)) ≠ 0 := two_ne_zero_of_charP_ne_two (K := GaloisField p
    (2 * e)) hp2
  obtain ⟨R₁, hR₁, R₂, hR₂, y, hy, x₂, hx₂, h1, h2', h3', h4', h5, h6⟩ :=
    nc4_su4_matrix (p := p) (f := e) h2 hω hσω
  have hmap : ∀ R : Subgroup (Su (GaloisField p (2 * e)) p e 4),
      R ∈ longRootSetU (K := GaloisField p (2 * e)) (p := p) (f := e) (show 2 ≤ 4 by norm_num) →
      R.map φ.symm.toMonoidHom ∈ ModelFund p .PSU 4 e := by
    intro R hR
    refine (hφ _).mpr ?_
    have : (R.map φ.symm.toMonoidHom).map φ.toMonoidHom = R := by
      rw [Subgroup.map_map]
      have : φ.toMonoidHom.comp φ.symm.toMonoidHom = MonoidHom.id _ := by
        ext y
        simp
      rw [this, Subgroup.map_id]
    rw [this]
    exact hR
  refine ⟨R₁.map φ.symm.toMonoidHom, hmap R₁ hR₁, R₂.map φ.symm.toMonoidHom, hmap R₂ hR₂,
    φ.symm y, Subgroup.mem_map_of_mem _ hy, φ.symm x₂, Subgroup.mem_map_of_mem _ hx₂, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · rw [← map_mul, ← map_mul, ← map_mul, h1, map_one]
  · intro h
    apply h2'
    apply φ.symm.injective
    rw [map_mul, h, map_one]
  · rw [← map_mul, h3', map_one]
  · intro h
    apply h4'
    apply φ.symm.injective
    rw [h, map_one]
  · rw [← map_mul, ← map_mul, h5]
  · intro h
    apply h6
    have h' : φ.symm (y * y * x₂) ∈ Subgroup.center (modelUniv .PSU 4 p e Fact.out).K := by
      rw [map_mul, map_mul]
      exact h
    exact (CFSG.ClassicalInvolution.ModelFacts.Orth15.mulEquiv_mem_center_iff φ.symm _).mp h'

end Row

end C25X

end CFSG.ClassicalInvolution.Asc77
