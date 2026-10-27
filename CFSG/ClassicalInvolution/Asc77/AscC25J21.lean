module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Asc77.AscC25X8
public import CFSG.ClassicalInvolution.Uniform.UTwinSolv

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.C25J

open Matrix CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.ModelFacts.UnitaryAut CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.ClassicalInvolution.ModelFacts.Orth15.ChainU
  CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterU4 CFSG.LieType.Steinberg
  CFSG.ClassicalInvolution.RouteD CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Generic (modelUniv)
open CFSG.ClassicalInvolution.Asc77.C25X CFSG.ClassicalInvolution.Uniform
open scoped MatrixGroups

section SU

variable {p : ℕ} [Fact p.Prime]


theorem nc4SU_three {e : ℕ} (hadm : StatedLieAdmissible .PSU 4 p e) (hp2 : p ≠ 2)
    (h3 : p ^ e % 4 = 3) : NC4At p .PSU 4 e := by
  have hf : 1 ≤ e := hadm.2.1
  have : NeZero (2 * e) := ⟨by omega⟩
  have hK : Nat.card (GaloisField p (2 * e)) = (p ^ e) ^ 2 := by
    rw [GaloisField.card p (2 * e) (by omega), ← pow_mul, mul_comm]
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
  have h2 : (2 : GaloisField p (2 * e)) ≠ 0 :=
    two_ne_zero_of_charP_ne_two (K := GaloisField p (2 * e)) hp2
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

end SU

end CFSG.ClassicalInvolution.Asc77.C25J
