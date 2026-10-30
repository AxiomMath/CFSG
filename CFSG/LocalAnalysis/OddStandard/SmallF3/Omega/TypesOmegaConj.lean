module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesOmega
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesInvol

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open TauCeti QuadraticMap CFSG.ClassicalInvolution CFSG.ClassicalGroups.Orthogonal

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

private lemma aux_reflect_neg (w : V) : reflect Q (-w) = reflect Q w := by
  by_cases hw : Q w = 0
  · rw [reflect_of_map_eq_zero hw, reflect_of_map_eq_zero (by rw [QuadraticMap.map_neg, hw])]
  · have hw' : Q (-w) ≠ 0 := by rwa [QuadraticMap.map_neg]
    apply LinearEquiv.ext
    intro y
    rw [reflect_apply hw', reflect_apply hw, QuadraticMap.map_neg, polar_neg_left, neg_div]
    rw [neg_smul, smul_neg, neg_neg]

private lemma aux_reflect_comm {t : OGroup Q} {w : V} (hQw : Q w ≠ 0)
    (hw : (t : V ≃ₗ[ZMod 3] V) w = w ∨ (t : V ≃ₗ[ZMod 3] V) w = -w) :
    reflect Q w * (t : V ≃ₗ[ZMod 3] V) = (t : V ≃ₗ[ZMod 3] V) * reflect Q w := by
  have hconj := reflect_conj (Q := Q) t.2 w
  have h1 : reflect Q ((t : V ≃ₗ[ZMod 3] V) w) = reflect Q w := by
    rcases hw with h | h
    · rw [h]
    · rw [h]; exact aux_reflect_neg w
  rw [h1] at hconj
  have h2 : (t : V ≃ₗ[ZMod 3] V) * reflect Q w = reflect Q w * (t : V ≃ₗ[ZMod 3] V) := by
    calc (t : V ≃ₗ[ZMod 3] V) * reflect Q w =
        ((t : V ≃ₗ[ZMod 3] V) * reflect Q w * (t : V ≃ₗ[ZMod 3] V)⁻¹) *
          (t : V ≃ₗ[ZMod 3] V) := by group
      _ = reflect Q w * (t : V ≃ₗ[ZMod 3] V) := by rw [hconj]
  exact h2.symm

private lemma aux_centralizer_map_eq_top_of_subspace (hQ : Q.Nondegenerate) {t : OGroup Q}
    {W : Submodule (ZMod 3) V}
    (hWnd : (Q.restrict W).Nondegenerate) (hW2 : 2 ≤ Module.finrank (ZMod 3) W)
    (hWsign : ∀ w ∈ W, (t : V ≃ₗ[ZMod 3] V) w = w ∨ (t : V ≃ₗ[ZMod 3] V) w = -w) :
    (Subgroup.centralizer ({t} : Set (OGroup Q))).map (detSpinorNorm hQ) = ⊤ := by
  obtain ⟨w1, hw1⟩ := exists_eq_unit_of_two_le_finrank (R := Q.restrict W) hWnd hW2
    (1 : (ZMod 3)ˣ)
  obtain ⟨w2, hw2⟩ := exists_eq_unit_of_two_le_finrank (R := Q.restrict W) hWnd hW2
    (-1 : (ZMod 3)ˣ)
  have hw1' : Q (w1 : V) = 1 := by simpa using hw1
  have hw2' : Q (w2 : V) = -1 := by simpa using hw2
  have hQw1 : Q (w1 : V) ≠ 0 := by rw [hw1']; exact one_ne_zero
  have hQw2 : Q (w2 : V) ≠ 0 := by rw [hw2']; exact neg_ne_zero.mpr one_ne_zero
  let _ : Invertible (Q (w1 : V)) := invertibleOfNonzero hQw1
  let _ : Invertible (Q (w2 : V)) := invertibleOfNonzero hQw2
  have hmem1 : reflectionOrthogonal Q (w1 : V) ∈ Subgroup.centralizer ({t} : Set (OGroup Q)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    apply Subtype.ext
    change (h : V ≃ₗ[ZMod 3] V) * ((reflectionOrthogonal Q (w1 : V) : OGroup Q) : V ≃ₗ[ZMod 3] V) =
      ((reflectionOrthogonal Q (w1 : V) : OGroup Q) : V ≃ₗ[ZMod 3] V) * (h : V ≃ₗ[ZMod 3] V)
    rw [CFSG.ClassicalInvolution.coe_reflectionOrthogonal_eq_reflect]
    exact (aux_reflect_comm hQw1 (hWsign _ w1.2)).symm
  have hmem2 : reflectionOrthogonal Q (w2 : V) ∈ Subgroup.centralizer ({t} : Set (OGroup Q)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    apply Subtype.ext
    change (h : V ≃ₗ[ZMod 3] V) * ((reflectionOrthogonal Q (w2 : V) : OGroup Q) : V ≃ₗ[ZMod 3] V) =
      ((reflectionOrthogonal Q (w2 : V) : OGroup Q) : V ≃ₗ[ZMod 3] V) * (h : V ≃ₗ[ZMod 3] V)
    rw [CFSG.ClassicalInvolution.coe_reflectionOrthogonal_eq_reflect]
    exact (aux_reflect_comm hQw2 (hWsign _ w2.2)).symm
  have hx1 : detSpinorNorm hQ (reflectionOrthogonal Q (w1 : V)) =
      ((-1 : (ZMod 3)ˣ), (1 : Multiplicative (SquareClassGroup (ZMod 3)))) := by
    rw [detSpinorNorm_reflectionOrthogonal,
      show unitOfInvertible (Q (w1 : V)) = (1 : (ZMod 3)ˣ) from
        Units.ext (by rw [val_unitOfInvertible, hw1']; rfl), map_one]
  have hx2 : detSpinorNorm hQ (reflectionOrthogonal Q (w2 : V)) =
      ((-1 : (ZMod 3)ˣ), Multiplicative.ofAdd (squareClass (-1 : (ZMod 3)ˣ))) := by
    rw [detSpinorNorm_reflectionOrthogonal, squareClassHom_apply,
      show unitOfInvertible (Q (w2 : V)) = (-1 : (ZMod 3)ˣ) from
        Units.ext (by rw [val_unitOfInvertible, hw2']; rfl)]
  refine aux_subgroup_eq_top_of_mem ?_ ?_
  · exact Subgroup.mem_map.mpr ⟨reflectionOrthogonal Q (w1 : V), hmem1, hx1⟩
  · exact Subgroup.mem_map.mpr ⟨reflectionOrthogonal Q (w2 : V), hmem2, hx2⟩

theorem map_centralizer_detSpinorNorm_eq_top (hQ : Q.Nondegenerate)
    (h3 : 3 ≤ Module.finrank (ZMod 3) V) {t : OGroup Q} (htt : t * t = 1) :
    (Subgroup.centralizer {t}).map (detSpinorNorm hQ) = ⊤ := by
  have hdim := finrank_fixSp_add_finrank_commSp (Q := Q) t
  have hcases : 2 ≤ Module.finrank (ZMod 3) (fixSp t) ∨
      2 ≤ Module.finrank (ZMod 3) (commSp t) := by
    by_contra h
    push Not at h
    omega
  rcases hcases with hC2 | hN2
  · exact aux_centralizer_map_eq_top_of_subspace hQ (nondegenerate_restrict_fixSp hQ htt) hC2
      (fun w hw => Or.inl (mem_fixSp_iff.mp hw))
  · exact aux_centralizer_map_eq_top_of_subspace hQ (nondegenerate_restrict_commSp hQ htt) hN2
      (fun w hw => Or.inr ((mem_commSp_iff htt).mp hw))

theorem exists_mem_omegaGroup_conj (hQ : Q.Nondegenerate) (h3 : 3 ≤ Module.finrank (ZMod 3) V)
    {s t : OGroup Q} (hs : s * s = 1) (ht : t * t = 1) (h : invType s = invType t) :
    ∃ c ∈ omegaGroup hQ, c * s * c⁻¹ = t := by
  obtain ⟨g, hg⟩ := isConj_iff.mp (isConj_of_invType_eq hQ hs ht h)
  have htop := map_centralizer_detSpinorNorm_eq_top hQ h3 ht
  have hmem : (detSpinorNorm hQ g)⁻¹ ∈
      (Subgroup.centralizer ({t} : Set (OGroup Q))).map (detSpinorNorm hQ) := by
    rw [htop]
    exact Subgroup.mem_top _
  obtain ⟨z, hz, hzg⟩ := Subgroup.mem_map.mp hmem
  refine ⟨z * g, ?_, ?_⟩
  · rw [mem_omegaGroup_iff, map_mul, hzg, inv_mul_cancel]
  · have hcomm : z * t = t * z :=
      (Subgroup.mem_centralizer_iff.mp hz t (Set.mem_singleton t)).symm
    calc z * g * s * (z * g)⁻¹ = z * (g * s * g⁻¹) * z⁻¹ := by group
      _ = z * t * z⁻¹ := by rw [hg]
      _ = t := by rw [hcomm]; group

end CFSG.OddStandard.SmallF3.Omega
