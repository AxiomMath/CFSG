module

public import CFSG.RankThree.PartOne.SEITZ3.MaxDefs
public import CFSG.RankThree.PartTwo.KFacts.AutG2

public section

namespace CFSG.HardMathSupport.Seitz.G2Noninner.Coordinator

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.ComponentClassification.UnbalancedCatalog CFSG.RankThree.PartOne.SEITZ3
  CFSG.RankThree.PartTwo.KFacts

variable {K : Type} [Field K]

theorem eq_one_of_mem_center_of_odd {A : Matrix.SpecialLinearGroup (Fin 2) K}
    (hA : A ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K)) (hodd : Odd (orderOf A)) :
    A = 1 := by
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hA
  have hr2 : r ^ 2 = 1 := by simpa using hr
  have h2 : A ^ 2 = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one, ← hrA, ← map_pow,
      hr2, map_one]
  have hd : orderOf A ∣ 2 := orderOf_dvd_of_pow_eq_one h2
  rcases (Nat.dvd_prime Nat.prime_two).1 hd with h | h
  · exact orderOf_eq_one_iff.1 h
  · rw [h] at hodd
    exact absurd hodd (by decide)


theorem eq_one_of_rootSL2_mul_eq_one {A B : Matrix.SpecialLinearGroup (Fin 2) K}
    (hA : Odd (orderOf A)) (h : rootSL2 .G2 K g2a A * rootSL2 .G2 K g2v B = 1) :
    A = 1 ∧ B = 1 := by
  have hAB : rootSL2 .G2 K g2a A = rootSL2 .G2 K g2v B⁻¹ := by
    rw [map_inv]
    exact eq_inv_of_mul_eq_one_left h
  have hc : A ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) := by
    refine Subgroup.mem_center_iff.2 fun C => rootSL2_injective_of_field (τ := .G2) g2a ?_
    rw [map_mul, map_mul, hAB]
    exact (rootSL2_g2v_mul_rootSL2_g2a B⁻¹ C).symm
  have hA1 : A = 1 := eq_one_of_mem_center_of_odd hc hA
  refine ⟨hA1, rootSL2_injective_of_field (τ := .G2) g2v ?_⟩
  rw [hA1, map_one, one_mul] at h
  rw [h, map_one]

theorem commute_a1a1Hom (x y : Matrix.SpecialLinearGroup (Fin 2) K) :
    Commute (a1a1Hom K (x, 1)) (a1a1Hom K (1, y)) :=
  Commute.map (Prod.ext (by simp) (by simp)) (a1a1Hom K)

theorem a1a1Hom_pow_eq_one {x : Matrix.SpecialLinearGroup (Fin 2) K} {n : ℕ} (hx : x ^ n = 1) :
    a1a1Hom K (x, 1) ^ n = 1 ∧ a1a1Hom K (1, x) ^ n = 1 := by
  refine ⟨?_, ?_⟩
  · rw [← map_pow, Prod.pow_mk, hx, one_pow, ← Prod.one_eq_mk, map_one]
  · rw [← map_pow, Prod.pow_mk, hx, one_pow, ← Prod.one_eq_mk, map_one]

theorem a1a1Hom_indep {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {x : Matrix.SpecialLinearGroup (Fin 2) K} (hx : orderOf x = p) (i j : ℤ)
    (h : a1a1Hom K (x, 1) ^ i * a1a1Hom K (1, x) ^ j = 1) : (p : ℤ) ∣ i ∧ (p : ℤ) ∣ j := by
  have h' : a1a1Hom K (x ^ i, x ^ j) = 1 := by
    rw [← h, ← map_zpow, ← map_zpow, ← map_mul]
    congr 1
    exact Prod.ext (by simp) (by simp)
  have hc : rootSL2 .G2 K g2a (x ^ i) * rootSL2 .G2 K g2v (x ^ j) = 1 := by
    have := congrArg (fun y : adjointGroup .G2 K => (y : ModGL .G2 K)) h'
    simpa only [a1a1Hom_apply, OneMemClass.coe_one] using this
  have hodd : Odd (orderOf (x ^ i)) := by
    have hd : orderOf (x ^ i) ∣ p := orderOf_dvd_of_pow_eq_one (by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hx, pow_orderOf_eq_one,
        one_zpow])
    rcases hp.eq_one_or_self_of_dvd _ hd with h1 | h1
    · rw [h1]
      exact odd_one
    · rw [h1]
      exact hp.odd_of_ne_two hp2
  obtain ⟨h1, h2⟩ := eq_one_of_rootSL2_mul_eq_one hodd hc
  refine ⟨?_, ?_⟩
  · rw [← hx]
    exact orderOf_dvd_iff_zpow_eq_one.2 h1
  · rw [← hx]
    exact orderOf_dvd_iff_zpow_eq_one.2 h2

theorem g2FieldHom_a1a1Hom_inl (σ : K ≃+* K) {x : Matrix.SpecialLinearGroup (Fin 2) K}
    (hx : Matrix.SpecialLinearGroup.map σ.toRingHom x = x) :
    g2FieldHom K σ (a1a1Hom K (x, 1)) = a1a1Hom K (x, 1) := by
  apply Subtype.ext
  rw [coe_g2FieldHom, a1a1Hom_apply_inl, entrywise_rootSL2_of_field, hx]

theorem g2FieldHom_a1a1Hom_inr (σ : K ≃+* K) {x : Matrix.SpecialLinearGroup (Fin 2) K}
    (hx : Matrix.SpecialLinearGroup.map σ.toRingHom x = x) :
    g2FieldHom K σ (a1a1Hom K (1, x)) = a1a1Hom K (1, x) := by
  apply Subtype.ext
  rw [coe_g2FieldHom, a1a1Hom_apply_inr, entrywise_rootSL2_of_field, hx]

end CFSG.HardMathSupport.Seitz.G2Noninner.Coordinator
