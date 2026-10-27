module

public import CFSG.ClassicalGroups.Orthogonal.Eichler
public import CFSG.ClassicalGroups.Orthogonal.Hyperbolic

public section

namespace CFSG.ClassicalGroups.Orthogonal

open QuadraticMap

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem rootGroup_smul {u : V} {c : K} (hc : c ≠ 0) : rootGroup Q (c • u) = rootGroup Q u := by
  ext g
  rw [mem_rootGroup, mem_rootGroup]
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [polar_smul_left_eq] at hw
    refine ⟨c • w, ?_, (eichler_smul_left c u w).symm⟩
    rw [polar_smul_right_eq, (mul_eq_zero.mp hw).resolve_left hc, mul_zero]
  · rintro ⟨w, hw, rfl⟩
    refine ⟨c⁻¹ • w, ?_, ?_⟩
    · simp [polar_smul_left_eq, polar_smul_right_eq, hw]
    · rw [eichler_smul_left, smul_smul, mul_inv_cancel₀ hc, one_smul]

private theorem exists_perp_ne_zero_of_finrank [FiniteDimensional K V]
    (h3 : 3 ≤ Module.finrank K V) (P : HypPair Q) : ∃ z ∈ P.perp, z ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have htop : Submodule.span K (Set.range ![P.e, P.f]) = ⊤ := by
    rw [eq_top_iff]
    intro v _
    have hv : P.proj v = 0 := hcon _ (P.proj_mem_perp v)
    have hdec := P.eq_add_proj v
    rw [hv, add_zero] at hdec
    rw [hdec]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, by simp⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, by simp⟩))
  have hle : Module.finrank K (Submodule.span K (Set.range ![P.e, P.f])) ≤ 2 := by
    have h := finrank_range_le_card (R := K) ![P.e, P.f]
    rw [Fintype.card_fin] at h
    exact h
  rw [htop, finrank_top] at hle
  omega

private theorem smul_of_rootGroup_le [FiniteDimensional K V] (hQ : (polarBilin Q).Nondegenerate)
    (h3 : 3 ≤ Module.finrank K V) {x y : V} (hx0 : x ≠ 0) (hy0 : y ≠ 0) (hx : Q x = 0)
    (hle : rootGroup Q x ≤ rootGroup Q y) : ∃ c : K, c ≠ 0 ∧ y = c • x := by
  obtain ⟨P, rfl⟩ := exists_hypPair hQ hx hx0
  have key : ∀ z, polar Q P.e z = 0 →
      polar Q y P.e • z = (polar Q y z + Q z * polar Q y P.e) • P.e := by
    intro z hz
    have hmem : eichler Q P.e z ∈ rootGroup Q y := hle (eichler_mem_rootGroup hz)
    obtain ⟨w, -, hw⟩ := mem_rootGroup.mp hmem
    have hfix : eichler Q P.e z y = y := by
      rw [← hw]
      exact eichler_apply_self y w
    rw [eichler_apply hx hz] at hfix
    linear_combination (norm := module) hfix
  have hyx : polar Q y P.e = 0 := by
    by_contra hyx0
    obtain ⟨z, hzperp, hz0⟩ := exists_perp_ne_zero_of_finrank h3 P
    have hz := key z (HypPair.mem_perp.mp hzperp).1
    have h2 := congrArg (polar Q P.f) hz
    rw [polar_smul_right_eq, polar_smul_right_eq, (HypPair.mem_perp.mp hzperp).2, P.polar_fe,
      mul_zero, mul_one] at h2
    rw [← h2, zero_smul, smul_eq_zero] at hz
    exact hz.elim hyx0 hz0
  have hyperp : ∀ z ∈ P.perp, polar Q y z = 0 := by
    intro z hzperp
    have hz := key z (HypPair.mem_perp.mp hzperp).1
    rw [hyx, zero_smul, mul_zero, add_zero] at hz
    exact (smul_eq_zero.mp hz.symm).resolve_right P.e_ne_zero
  have hproj : P.proj y = 0 := by
    refine HypPair.polarNondegOn_perp hQ P _ (P.proj_mem_perp y) fun z hz => ?_
    obtain ⟨hze, hzf⟩ := HypPair.mem_perp.mp hz
    rw [HypPair.proj, polar_sub_left, polar_sub_left, polar_smul_left_eq, polar_smul_left_eq,
      hze, hzf, hyperp z hz]
    ring
  have hy_eq : y = polar Q y P.f • P.e := by
    have h := P.eq_add_proj y
    rw [hyx, hproj] at h
    simpa using h
  refine ⟨polar Q y P.f, fun hc => hy0 ?_, hy_eq⟩
  rw [hy_eq, hc, zero_smul]

theorem rootGroup_eq_iff [FiniteDimensional K V] (hQ : (polarBilin Q).Nondegenerate)
    (h3 : 3 ≤ Module.finrank K V) {x y : V} (hx0 : x ≠ 0) (hy0 : y ≠ 0) (hx : Q x = 0) :
    rootGroup Q x = rootGroup Q y ↔ ∃ c : K, c ≠ 0 ∧ y = c • x := by
  constructor
  · intro hEq
    exact smul_of_rootGroup_le hQ h3 hx0 hy0 hx hEq.le
  · rintro ⟨c, hc, rfl⟩
    exact (rootGroup_smul hc).symm

end CFSG.ClassicalGroups.Orthogonal
