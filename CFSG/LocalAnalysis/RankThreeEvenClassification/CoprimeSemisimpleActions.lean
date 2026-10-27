module

public import CFSG.Assembly.Defs
public import CFSG.LocalAnalysis.RankThreeEvenClassification.LocalCore

public section

namespace CFSG.RankThreeEvenClassification.Helpers

universe u v

theorem linear_coprime_power_isSemisimple {field : Type u} {space : Type v}
    [Field field] [AddCommGroup space] [Module field space]
    (characteristic : ℕ) [CharP field characteristic]
    (equivalence : space ≃ₗ[field] space) (exponent : ℕ)
    (hcoprime : ¬characteristic ∣ exponent) (hpower : equivalence ^ exponent = 1) :
    Module.End.IsSemisimple (equivalence : Module.End field space) := by
  apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero
    (p := Polynomial.X ^ exponent - Polynomial.C (1 : field))
  · exact (Polynomial.separable_X_pow_sub_C' characteristic exponent (1 : field)
      hcoprime one_ne_zero).squarefree
  · rw [map_sub, Polynomial.aeval_X_pow, Polynomial.aeval_C, map_one]
    have hlinearPower := congrArg
      (LinearEquiv.automorphismGroup.toLinearMapMonoidHom :
        (space ≃ₗ[field] space) →* Module.End field space) hpower
    rw [map_pow, map_one] at hlinearPower
    exact sub_eq_zero.mpr hlinearPower

theorem semisimple_plane_has_eigenbasis {field : Type u} {space : Type v}
    [Field field] [AddCommGroup space] [Module field space] [IsAlgClosed field]
    [FiniteDimensional field space] (hdimension : Module.finrank field space = 2)
    (equivalence : space ≃ₗ[field] space)
    (hsemisimple : Module.End.IsSemisimple (equivalence : Module.End field space)) :
    ∃ first second : space, first ≠ 0 ∧ second ≠ 0 ∧
      ∃ firstScalar secondScalar : field,
        equivalence first = firstScalar • first ∧
        equivalence second = secondScalar • second ∧
        (∀ firstCoefficient secondCoefficient : field,
          firstCoefficient • first + secondCoefficient • second = 0 →
            firstCoefficient = 0 ∧ secondCoefficient = 0) ∧
        ∀ member : space, ∃ firstCoefficient secondCoefficient : field,
          firstCoefficient • first + secondCoefficient • second = member := by
  have : Nontrivial space := Module.finrank_pos_iff.mp (hdimension ▸ (by omega : 0 < 2))
  obtain ⟨firstScalar, heigenvalue⟩ := Module.End.exists_eigenvalue
    (equivalence : Module.End field space)
  obtain ⟨first, heigenvector⟩ := heigenvalue.exists_hasEigenvector
  have hfirstNe := (Module.End.hasEigenvector_iff.mp heigenvector).2
  have hfirstEigen : equivalence first = firstScalar • first := heigenvector.apply_eq_smul
  let line := Submodule.span field {first}
  have hlineInvariant : line ∈ Module.End.invtSubmodule (equivalence : Module.End field space) := by
    apply (Module.End.mem_invtSubmodule_iff_mapsTo _).mpr
    intro member hmember
    obtain ⟨coefficient, rfl⟩ := Submodule.mem_span_singleton.mp hmember
    change equivalence (coefficient • first) ∈ line
    rw [map_smul, hfirstEigen, smul_smul]
    exact Submodule.mem_span_singleton.mpr ⟨coefficient * firstScalar, rfl⟩
  obtain ⟨complement, hcomplementInvariant, hcompl⟩ :=
    Module.End.isSemisimple_iff.mp hsemisimple line hlineInvariant
  have hlineDimension : Module.finrank field line = 1 := finrank_span_singleton hfirstNe
  have hcomplementDimension : Module.finrank field complement = 1 := by
    have hadd := Submodule.finrank_add_eq_of_isCompl hcompl
    rw [hlineDimension, hdimension] at hadd
    omega
  obtain ⟨second, hsecondNe, hsecondSpan⟩ := finrank_eq_one_iff'.mp hcomplementDimension
  have hsecondAmbientNe : (second : space) ≠ 0 := by
    intro heq
    exact hsecondNe (Subtype.ext heq)
  have hsecondImage : equivalence (second : space) ∈ complement :=
    (Module.End.mem_invtSubmodule_iff_mapsTo _).mp hcomplementInvariant second.property
  obtain ⟨secondScalar, hsecondScalar⟩ := hsecondSpan ⟨equivalence second, hsecondImage⟩
  have hsecondEigen : equivalence (second : space) = secondScalar • (second : space) :=
    (congrArg (fun member : complement => (member : space)) hsecondScalar).symm
  refine ⟨first, second, hfirstNe, hsecondAmbientNe, firstScalar, secondScalar,
    hfirstEigen, hsecondEigen, ?_, ?_⟩
  · intro firstCoefficient secondCoefficient heq
    have hlineMem : firstCoefficient • first ∈ line :=
      Submodule.mem_span_singleton.mpr ⟨firstCoefficient, rfl⟩
    have hcomplementMem : firstCoefficient • first ∈ complement := by
      have heqNeg : firstCoefficient • first = -(secondCoefficient • (second : space)) :=
        eq_neg_of_add_eq_zero_left heq
      rw [heqNeg]
      exact complement.neg_mem (complement.smul_mem secondCoefficient second.property)
    have hfirstZero := Submodule.disjoint_def.mp hcompl.disjoint _ hlineMem hcomplementMem
    have hfirstCoefficient : firstCoefficient = 0 :=
      (smul_eq_zero.mp hfirstZero).resolve_right hfirstNe
    rw [hfirstCoefficient, zero_smul, zero_add] at heq
    exact ⟨hfirstCoefficient, (smul_eq_zero.mp heq).resolve_right hsecondAmbientNe⟩
  · intro member
    have hmember : member ∈ line ⊔ complement := by
      rw [hcompl.sup_eq_top]
      trivial
    obtain ⟨firstPart, hfirstPart, secondPart, hsecondPart, heq⟩ := Submodule.mem_sup.mp hmember
    obtain ⟨firstCoefficient, hfirstCoefficient⟩ := Submodule.mem_span_singleton.mp hfirstPart
    obtain ⟨secondCoefficient, hsecondCoefficient⟩ := hsecondSpan ⟨secondPart, hsecondPart⟩
    refine ⟨firstCoefficient, secondCoefficient, ?_⟩
    rw [hfirstCoefficient]
    have hambient := congrArg (fun value : complement => (value : space)) hsecondCoefficient
    exact (congrArg (firstPart + ·) hambient).trans heq

end CFSG.RankThreeEvenClassification.Helpers
