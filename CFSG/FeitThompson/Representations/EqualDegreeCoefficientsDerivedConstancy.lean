module

public import CFSG.FeitThompson.Representations.FixedDegreeCharacterSumVanishing
public import CFSG.FeitThompson.Representations.NormalInducedCharactersOrthogonal
public import CFSG.FeitThompson.Representations.CentralScalarInductionDegreeSum
public import CFSG.FeitThompson.Representations.OddOrderNonrealCharacters
import CFSG.FeitThompson.Representations.BlockDifferenceOrthogonalConstantOffCore
public import CFSG.FeitThompson.Representations.CyclicTIIsometryMixedSetValues

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

variable {H : Type*} [Group H]

def HasEqualDegreeCoeffs [Fintype H] (f : H → ℂ) : Prop :=
  ∀ lam ∈ nonprincipalIrr H, ∀ mu ∈ nonprincipalIrr H, lam 1 = mu 1 →
    cfInner f lam = cfInner f mu

theorem hasEqualDegreeCoeffs_iff [Fintype H] {f : H → ℂ} :
    HasEqualDegreeCoeffs f ↔ ∀ lam ∈ Irr H, ∀ mu ∈ Irr H, lam ≠ 1 → mu ≠ 1 → lam 1 = mu 1 →
      cfInner f lam = cfInner f mu := by
  simp only [HasEqualDegreeCoeffs, mem_nonprincipalIrr]
  exact ⟨fun h lam hl mu hm hl1 hm1 => h lam ⟨hl, hl1⟩ mu ⟨hm, hm1⟩,
    fun h lam hl mu hm => h lam hl.1 mu hm.1 hl.2 hm.2⟩

theorem HasEqualDegreeCoeffs.cfInner_eq [Fintype H] {f : H → ℂ} (hf : HasEqualDegreeCoeffs f)
    {lam mu : H → ℂ} (hl : lam ∈ Irr H) (hm : mu ∈ Irr H) (hl1 : lam ≠ 1) (hm1 : mu ≠ 1)
    (hdeg : lam 1 = mu 1) : cfInner f lam = cfInner f mu :=
  hasEqualDegreeCoeffs_iff.1 hf lam hl mu hm hl1 hm1 hdeg

theorem HasEqualDegreeCoeffs.smul [Fintype H] {f : H → ℂ} (hf : HasEqualDegreeCoeffs f) (c : ℂ) :
    HasEqualDegreeCoeffs (c • f) := by
  intro lam hl mu hm hdeg
  rw [cfInner_smul_left, cfInner_smul_left, hf lam hl mu hm hdeg]

theorem HasEqualDegreeCoeffs.sum_nonprincipalIrrDeg [Fintype H] {f : H → ℂ}
    (hf : HasEqualDegreeCoeffs f) {d : ℕ} {χ₀ : H → ℂ}
    (h₀ : χ₀ ∈ nonprincipalIrrDegFinset H d) {x : H} (hx : x ∉ commutator H) :
    ∑ χ ∈ nonprincipalIrrDegFinset H d, cfInner f χ * χ x
      = cfInner f χ₀ * (if d = 1 then -1 else 0) := by
  obtain ⟨h₀irr, h₀ne, h₀deg⟩ := mem_nonprincipalIrrDeg.1 (mem_nonprincipalIrrDegFinset.1 h₀)
  have hstep : ∑ χ ∈ nonprincipalIrrDegFinset H d, cfInner f χ * χ x
      = ∑ χ ∈ nonprincipalIrrDegFinset H d, cfInner f χ₀ * χ x := by
    refine Finset.sum_congr rfl fun χ hχ => ?_
    obtain ⟨hirr, hne, hdeg⟩ := mem_nonprincipalIrrDeg.1 (mem_nonprincipalIrrDegFinset.1 hχ)
    rw [hf.cfInner_eq hirr h₀irr hne h₀ne (by rw [hdeg, h₀deg])]
  rw [hstep, ← Finset.mul_sum, sum_nonprincipalIrrDeg_apply_of_notMem_commutator hx]

theorem HasEqualDegreeCoeffs.sum_nonprincipalIrrDeg_eq_zero [Fintype H] {f : H → ℂ}
    (hf : HasEqualDegreeCoeffs f) {d : ℕ} (hd : d ≠ 1) {x : H} (hx : x ∉ commutator H) :
    ∑ χ ∈ nonprincipalIrrDegFinset H d, cfInner f χ * χ x = 0 := by
  rcases Finset.eq_empty_or_nonempty (nonprincipalIrrDegFinset H d) with he | ⟨χ₀, h₀⟩
  · rw [he, Finset.sum_empty]
  · rw [hf.sum_nonprincipalIrrDeg h₀ hx, if_neg hd, mul_zero]

theorem exists_mem_Irr_ne_one_apply_one_eq_one_of_notMem_commutator [Finite H] {x : H}
    (hx : x ∉ commutator H) : ∃ ν ∈ Irr H, ν ≠ 1 ∧ ν 1 = 1 ∧ ν x ≠ 1 := by
  obtain ⟨ν, hν⟩ := exists_monoidHom_apply_ne_one_of_notMem_commutator hx
  refine ⟨fun h => (ν h : ℂ), monoidHom_mem_Irr ((Units.coeHom ℂ).comp ν), ?_, by simp, hν⟩
  intro h
  exact hν (congrFun h x)

theorem exists_mem_Irr_ne_one_apply_one_eq_one_of_nontrivial_quotient_commutator [Finite H]
    (h : Nontrivial (H ⧸ commutator H)) : ∃ ν ∈ Irr H, ν ≠ 1 ∧ ν 1 = 1 := by
  obtain ⟨x, hx⟩ : ∃ x : H, x ∉ commutator H := by
    by_contra hc
    exact QuotientGroup.nontrivial_iff.1 h ((Subgroup.eq_top_iff' _).2 (by simpa using hc))
  obtain ⟨ν, hν, h1, h2, -⟩ := exists_mem_Irr_ne_one_apply_one_eq_one_of_notMem_commutator hx
  exact ⟨ν, hν, h1, h2⟩

theorem HasEqualDegreeCoeffs.apply_eq_cfInner_one_sub_cfInner [Fintype H] {f : H → ℂ}
    (hfc : f ∈ classFun H) (hf : HasEqualDegreeCoeffs f)
    {ν : H → ℂ} (hν : ν ∈ Irr H) (hν1 : ν ≠ 1) (hνdeg : ν 1 = 1)
    {x : H} (hx : x ∉ commutator H) :
    f x = cfInner f (principalClassFun H : H → ℂ) - cfInner f ν := by
  classical
  rw [coe_principalClassFun]
  set N : Finset (H → ℂ) := (irrFinset H).erase 1 with hN
  have hfilter : ∀ d : ℕ, N.filter (fun χ => χ 1 = (d : ℂ)) = nonprincipalIrrDegFinset H d := by
    intro d
    ext χ
    simp only [hN, Finset.mem_filter, Finset.mem_erase, mem_irrFinset,
      mem_nonprincipalIrrDegFinset, mem_nonprincipalIrrDeg]
    tauto
  have hνmem : ν ∈ nonprincipalIrrDegFinset H 1 :=
    mem_nonprincipalIrrDegFinset.2 (mem_nonprincipalIrrDeg.2 ⟨hν, hν1, by simpa using hνdeg⟩)
  have hνN : ν ∈ N := Finset.mem_erase.2 ⟨hν1, mem_irrFinset.2 hν⟩
  set T : Finset ℂ := N.image (fun χ => χ 1) with hT
  have hmaps : ∀ χ ∈ N, χ 1 ∈ T := fun χ hχ => Finset.mem_image_of_mem _ hχ
  have hfib := Finset.sum_fiberwise_of_maps_to hmaps (fun χ => cfInner f χ * χ x)
  have hzero : ∀ z ∈ T, z ≠ 1 →
      ∑ χ ∈ N.filter (fun χ => χ 1 = z), cfInner f χ * χ x = 0 := by
    intro z hz hz1
    obtain ⟨χ₀, hχ₀N, rfl⟩ := Finset.mem_image.1 hz
    have hχ₀ : χ₀ ∈ Irr H := mem_irrFinset.1 (Finset.mem_erase.1 hχ₀N).2
    obtain ⟨d, -, hdeg⟩ := NormalInducedFamily.exists_apply_one_eq_of_mem_Irr hχ₀
    rw [hdeg] at hz1 ⊢
    have hd : d ≠ 1 := fun h => hz1 (by rw [h]; norm_num)
    rw [hfilter d]
    exact hf.sum_nonprincipalIrrDeg_eq_zero hd hx
  have h1T : (1 : ℂ) ∈ T := by rw [← hνdeg]; exact hmaps ν hνN
  have hsum : ∑ χ ∈ N, cfInner f χ * χ x = -cfInner f ν := by
    rw [← hfib, Finset.sum_eq_single_of_mem (1 : ℂ) h1T hzero]
    have h1 : N.filter (fun χ => χ 1 = (1 : ℂ)) = nonprincipalIrrDegFinset H 1 := by
      simpa using hfilter 1
    rw [h1, hf.sum_nonprincipalIrrDeg hνmem hx, if_pos rfl, mul_neg, mul_one]
  have hexp := apply_eq_sum_cfInner_mul hfc x
  rw [← Finset.add_sum_erase (irrFinset H) (fun χ => cfInner f χ * χ x)
    (mem_irrFinset.2 (one_mem_Irr (G := H)))] at hexp
  rw [hexp, ← hN, hsum]
  simp [sub_eq_add_neg]

theorem HasEqualDegreeCoeffs.apply_eq_apply_of_notMem_commutator [Fintype H] {f : H → ℂ}
    (hfc : f ∈ classFun H) (hf : HasEqualDegreeCoeffs f) {x y : H}
    (hx : x ∉ commutator H) (hy : y ∉ commutator H) : f x = f y := by
  obtain ⟨ν, hν, hν1, hνdeg, -⟩ :=
    exists_mem_Irr_ne_one_apply_one_eq_one_of_notMem_commutator hx
  rw [hf.apply_eq_cfInner_one_sub_cfInner hfc hν hν1 hνdeg hx,
    hf.apply_eq_cfInner_one_sub_cfInner hfc hν hν1 hνdeg hy]

end CFSG.FeitThompson
