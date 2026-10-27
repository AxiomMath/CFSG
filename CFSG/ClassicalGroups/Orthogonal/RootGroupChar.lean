module

public import CFSG.ClassicalGroups.Orthogonal.Eichler
public import CFSG.ClassicalGroups.Orthogonal.Hyperbolic

public section

namespace CFSG.ClassicalGroups.Orthogonal

open QuadraticMap

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

private theorem mem_rootGroup_of_hypPair (P : HypPair Q) {g : V ≃ₗ[K] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hgu : g P.e = P.e)
    (hgperp : ∀ x, polar Q x P.e = 0 → ∃ c : K, g x - x = c • P.e) :
    g ∈ rootGroup Q P.e := by
  have hgf_polar : polar Q (g P.f) P.e = 1 := by
    rw [← hgu, polar_map_of_mem hg, P.polar_fe]
  have hv : polar Q (g P.f - P.f) P.e = 0 := by
    rw [polar_sub_left, hgf_polar, P.polar_fe, sub_self]
  obtain ⟨a, w, hwperp, hgf⟩ : ∃ a : K, ∃ w : V, w ∈ P.perp ∧ g P.f = P.f + a • P.e + w := by
    refine ⟨polar Q (g P.f - P.f) P.f, P.proj (g P.f - P.f), P.proj_mem_perp _, ?_⟩
    have hdec := P.eq_add_proj (g P.f - P.f)
    rw [hv, zero_smul, add_zero] at hdec
    linear_combination (norm := module) hdec
  obtain ⟨hw1, hw2⟩ := HypPair.mem_perp.mp hwperp
  have ha : a = -Q w := by
    have hQ0 : Q (g P.f) = 0 := by rw [map_of_mem hg, P.Q_f]
    rw [hgf, QuadraticMap.map_add Q (P.f + a • P.e) w, QuadraticMap.map_add Q P.f (a • P.e),
      map_smul_eq_sq, P.Q_f, P.Q_e, polar_add_left, polar_smul_left_eq, polar_smul_right_eq,
      P.polar_fe, hw1, hw2] at hQ0
    linear_combination hQ0
  subst ha
  have hEf : eichler Q P.e w P.f = g P.f := by
    rw [eichler_apply P.Q_e hw1, P.polar_fe, hw2, hgf]
    module
  have hf : ∀ t : K, g (t • P.f) = eichler Q P.e w (t • P.f) := fun t => by
    rw [map_smul, map_smul, hEf]
  have hperp : ∀ y, polar Q y P.e = 0 → g y = eichler Q P.e w y := by
    intro y hy
    obtain ⟨c, hc⟩ := hgperp y hy
    have hgy : g y = y + c • P.e := by linear_combination (norm := module) hc
    have key := polar_map_of_mem hg y P.f
    rw [← hEf, hgy, eichler_apply P.Q_e hw1, P.polar_fe, hw2] at key
    simp only [polar_add_left, polar_add_right, polar_sub_right, polar_smul_left_eq,
      polar_smul_right_eq, one_smul, hy, P.polar_ef, P.polar_ee, hw1] at key
    have hc' : c = -polar Q y w := by linear_combination key
    rw [eichler_apply P.Q_e hw1, hy, hgy, hc']
    module
  have hall : g = eichler Q P.e w := by
    refine LinearEquiv.ext fun x => ?_
    have hy : polar Q (x - polar Q x P.e • P.f) P.e = 0 := by
      rw [polar_sub_left, polar_smul_left_eq, P.polar_fe, mul_one, sub_self]
    have hsplit : g x = g (x - polar Q x P.e • P.f) + g (polar Q x P.e • P.f) := by
      rw [← map_add, sub_add_cancel]
    have hsplit' : eichler Q P.e w x = eichler Q P.e w (x - polar Q x P.e • P.f) +
        eichler Q P.e w (polar Q x P.e • P.f) := by
      rw [← map_add, sub_add_cancel]
    rw [hsplit, hsplit', hperp _ hy, hf]
  rw [hall]
  exact eichler_mem_rootGroup hw1

theorem mem_rootGroup_iff (hQ : (polarBilin Q).Nondegenerate) {u : V} (hu : Q u = 0)
    (hu0 : u ≠ 0) {g : V ≃ₗ[K] V} :
    g ∈ rootGroup Q u ↔ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q ∧ g u = u ∧
      ∀ x, polar Q x u = 0 → ∃ c : K, g x - x = c • u := by
  constructor
  · intro hg
    obtain ⟨w, hw, rfl⟩ := mem_rootGroup.mp hg
    refine ⟨eichler_mem_orthogonalGroup Q u w, eichler_apply_self u w,
      fun x hx => ⟨-polar Q x w, ?_⟩⟩
    rw [eichler_apply hu hw, hx]
    module
  · rintro ⟨hg, hgu, hgperp⟩
    obtain ⟨P, hP⟩ := exists_hypPair hQ hu hu0
    subst hP
    exact mem_rootGroup_of_hypPair P hg hgu hgperp

end CFSG.ClassicalGroups.Orthogonal
