module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FA8FinOP

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

private lemma fa8fin_h_det (hQ : Q.Nondegenerate) {g : OGroup Q} (hg : g ∈ omegaGroup hQ) :
    QuadraticMap.orthogonalDet Q g = 1 := by
  have h := (mem_omegaGroup_iff hQ).mp hg
  rw [CFSG.ClassicalInvolution.detSpinorNorm_apply] at h
  exact congrArg Prod.fst h

private lemma fa8fin_h_blockHom_exists (hQ : Q.Nondegenerate) {s g : OGroup Q}
    (hs : s * s = 1) (hcomm : g * s = s * g) :
    ∃ p : OGroup (Q.restrict (fixSp s)) × OGroup (Q.restrict (commSp s)),
      blockHom hs p = g := by
  have hmem : g ∈ (blockHom hs).range := by
    rw [range_blockHom hQ hs]
    exact Subgroup.mem_centralizer_singleton_iff.mpr hcomm
  exact MonoidHom.mem_range.mp hmem

theorem fa8fin_claimS (hQ : Q.Nondegenerate) {s : OGroup Q} (hs : s * s = 1)
    (hW : Module.finrank (ZMod 3) (commSp s) = 4) (hP : Module.finrank (ZMod 3) (fixSp s) = 2)
    (hsgn : quadSign (Q.restrict (fixSp s)) = -1) {R : Subgroup (OGroup Q)}
    (hΩ : R ≤ omegaGroup hQ) (hcent : ∀ g ∈ R, g * s = s * g)
    (hsq : ∀ g ∈ R, g * g = 1 ∨ g * g = s)
    (hpartner : ∀ g ∈ R, g ≠ 1 → g ≠ s → ∃ h ∈ R, h * g * h⁻¹ = s * g) {g : OGroup Q}
    (hg : g ∈ R) :
    ∃ p : OGroup (Q.restrict (fixSp s)) × OGroup (Q.restrict (commSp s)),
      blockHom hs p = g ∧ (p.1 = 1 ∨ p.1 = piOrth (Q.restrict (fixSp s))) := by
  by_cases hg1 : g = 1
  · refine ⟨(1, 1), ?_, Or.inl rfl⟩
    rw [hg1]
    exact map_one (blockHom hs)
  by_cases hgs : g = s
  · refine ⟨(1, piOrth (Q.restrict (commSp s))), ?_, Or.inl rfl⟩
    rw [hgs]
    exact blockHom_one_piOrth hs
  · obtain ⟨p, hp⟩ := fa8fin_h_blockHom_exists hQ hs (hcent g hg)
    have hpp : blockHom hs (p * p) = g * g := by
      rw [map_mul, hp]
    have hsqp : p * p = (1, 1) ∨
        p * p = (1, piOrth (Q.restrict (commSp s))) := by
      rcases hsq g hg with hcase | hcase
      · left
        apply blockHom_injective hs
        rw [hpp, hcase]
        exact (map_one (blockHom hs)).symm
      · right
        apply blockHom_injective hs
        rw [hpp, hcase]
        exact (blockHom_one_piOrth hs).symm
    have hp1sq : p.1 * p.1 = 1 := by
      rcases hsqp with h | h <;> simpa using congrArg Prod.fst h
    have hp2det : QuadraticMap.orthogonalDet (Q.restrict (commSp s)) p.2 = 1 := by
      rcases hsqp with h | h
      · have hp2sq : p.2 * p.2 = 1 := by simpa using congrArg Prod.snd h
        obtain ⟨h', hh'R, hconj⟩ := hpartner g hg hg1 hgs
        obtain ⟨q, hq⟩ := fa8fin_h_blockHom_exists hQ hs (hcent h' hh'R)
        have heq : q * p * q⁻¹ = (1, piOrth (Q.restrict (commSp s))) * p := by
          apply blockHom_injective hs
          calc blockHom hs (q * p * q⁻¹)
              = blockHom hs q * blockHom hs p * blockHom hs q⁻¹ := by
                rw [map_mul, map_mul, map_inv]
            _ = h' * g * h'⁻¹ := by rw [hq, hp, map_inv, hq]
            _ = s * g := hconj
            _ = blockHom hs (1, piOrth (Q.restrict (commSp s))) * blockHom hs p := by
                rw [blockHom_one_piOrth hs, hp]
            _ = blockHom hs ((1, piOrth (Q.restrict (commSp s))) * p) :=
                (map_mul _ _ _).symm
        have hconj2 : q.2 * p.2 * q.2⁻¹ =
            piOrth (Q.restrict (commSp s)) * p.2 := by
          simpa using congrArg Prod.snd heq
        have hres := (orthogonalDet_of_conj (V := commSp s) (Q := Q.restrict (commSp s))
          (nondegenerate_restrict_commSp hQ hs) (t := p.2) (s := q.2) hp2sq hconj2).2
        rw [hW] at hres
        simpa using hres
      · have hp2sq : p.2 * p.2 = piOrth (Q.restrict (commSp s)) := by
          simpa using congrArg Prod.snd h
        have hev : Even (Module.finrank (ZMod 3) (commSp s)) := by
          rw [hW]; exact ⟨2, rfl⟩
        exact orthogonalDet_eq_one_of_mul_self_eq_piOrth (V := commSp s)
          (Q := Q.restrict (commSp s)) hev hp2sq
    have hdetg : QuadraticMap.orthogonalDet Q g = 1 := fa8fin_h_det hQ (hΩ hg)
    have hdetp : QuadraticMap.orthogonalDet (Q.restrict (fixSp s)) p.1 = 1 := by
      have hd := orthogonalDet_blockHom (s := s) hs p
      rw [hp, hdetg, hp2det, mul_one] at hd
      exact hd.symm
    exact ⟨p, hp, fa8fin_oGroup_two_minus_det_sq (nondegenerate_restrict_fixSp hQ hs) hP hsgn
      hdetp hp1sq⟩

end CFSG.OddStandard.SmallF3.Omega
