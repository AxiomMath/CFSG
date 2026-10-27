module

public import CFSG.CharacterTheory.TwoRankLowerBound.AlgebraicIntegerResidue

public noncomputable section

open Polynomial
open scoped Classical

namespace CFSG.BrauerCharacters

open CFSG.TwoRankLowerBound.Helpers

variable (ideal : Ideal ComplexAlgebraicIntegers)

@[expose] def ResidueField : Type := ComplexAlgebraicIntegers ⧸ ideal

variable [ideal.IsMaximal]

instance residueField_field : Field (ResidueField ideal) :=
  Ideal.Quotient.field ideal

instance residueField_charP (p : ℕ) [h : CharP (ComplexAlgebraicIntegers ⧸ ideal) p] :
    CharP (ResidueField ideal) p := h

@[expose] def residue : ComplexAlgebraicIntegers →+* ResidueField ideal := Ideal.Quotient.mk ideal

theorem residue_surjective : Function.Surjective (residue ideal) := Ideal.Quotient.mk_surjective

theorem mem_integralClosure_of_root (f : ComplexAlgebraicIntegers[X]) (hf : f.Monic) {z : ℂ}
    (hz : (f.map (integralClosure ℤ ℂ).val.toRingHom).IsRoot z) : z ∈ integralClosure ℤ ℂ := by
  have : Algebra.IsIntegral ℤ ComplexAlgebraicIntegers := complexAlgebraicIntegers_integral
  have hint : IsIntegral ComplexAlgebraicIntegers z := by
    refine ⟨f, hf, ?_⟩
    rw [eval₂_eq_eval_map]
    exact hz
  exact isIntegral_trans (R := ℤ) (A := ComplexAlgebraicIntegers) z hint

instance residueField_isAlgClosed : IsAlgClosed (ResidueField ideal) := by
  apply IsAlgClosed.of_exists_root
  intro g hg hirr
  have hlift : g ∈ lifts (residue ideal) :=
    (lifts_iff_coeff_lifts g).mpr fun n => residue_surjective ideal (g.coeff n)
  obtain ⟨f, hfg, hdeg, hmonic⟩ := lifts_and_natDegree_eq_and_monic hlift hg
  set fC := f.map (integralClosure ℤ ℂ).val.toRingHom with hfC
  have hdegC : 0 < fC.degree := by
    rw [hfC, hmonic.degree_map, degree_eq_natDegree hmonic.ne_zero, hdeg]
    exact_mod_cast natDegree_pos_iff_degree_pos.mpr (degree_pos_of_irreducible hirr)
  obtain ⟨z, hz⟩ := Complex.exists_root hdegC
  have hzO := mem_integralClosure_of_root f hmonic hz
  refine ⟨residue ideal ⟨z, hzO⟩, ?_⟩
  have hroot : f.eval ⟨z, hzO⟩ = 0 := by
    apply Subtype.ext
    have h : eval₂ (integralClosure ℤ ℂ).val.toRingHom z f = 0 := by
      rw [eval₂_eq_eval_map]
      exact hz
    rw [show z = (integralClosure ℤ ℂ).val.toRingHom ⟨z, hzO⟩ from rfl, eval₂_at_apply] at h
    simpa using h
  rw [← hfg, eval_map, eval₂_at_apply, hroot, map_zero]

end CFSG.BrauerCharacters
