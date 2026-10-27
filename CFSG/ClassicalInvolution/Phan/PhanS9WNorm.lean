module

public import CFSG.ClassicalInvolution.Phan.PhanS9WKfld

public section

namespace CFSG.ClassicalInvolution.PhanB3.S

open CFSG.LieType.Universal.Spin QuadraticMap

variable {F K : Type} [Field F] [Field K] [Algebra F K] (D : KDat F K)

theorem exists_normalize [Finite F] (hodd : Odd (Nat.card F)) (h2 : (2 : K) ≠ 0)
    {a' b' : W7 F} (hab : polar (quadOdd 3 F) a' b' = 0)
    (hq : quadOdd 3 F a' = quadOdd 3 F b') (ha0 : quadOdd 3 F a' ≠ 0) {α : F} (hα : α ≠ 0) :
    ∃ (μ : K) (a'' b'' : W7 F), μ ≠ 0 ∧
      μ • (emb (K := K) a' + D.θ • emb (K := K) b') =
        emb (K := K) a'' + D.θ • emb (K := K) b'' ∧
      quadOdd 3 F a'' = α ∧ quadOdd 3 F b'' = α ∧ polar (quadOdd 3 F) a'' b'' = 0 ∧
      ∀ r, polar (quadOdd 3 F) a' r = 0 → polar (quadOdd 3 F) b' r = 0 →
        polar (quadOdd 3 F) a'' r = 0 ∧ polar (quadOdd 3 F) b'' r = 0 := by
  classical
  have := Fintype.ofFinite F
  have hcard : Fintype.card F % 2 = 1 := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.odd_iff.mp hodd
  obtain ⟨m₁, m₂, hm⟩ := CFSG.RankThree.Classical.exists_mul_sq_add_mul_sq_eq hcard
    (one_ne_zero : (1 : F) ≠ 0) (one_ne_zero : (1 : F) ≠ 0) (α / quadOdd 3 F a')
  have hm' : (m₁ ^ 2 + m₂ ^ 2) * quadOdd 3 F a' = α := by
    rw [one_mul, one_mul] at hm
    rw [hm]
    field_simp
  have hmne : m₁ ^ 2 + m₂ ^ 2 ≠ 0 := by
    intro h
    rw [h, zero_mul] at hm'
    exact hα hm'.symm
  have hpol := CFSG.RankThree.Classical.polar_smul_add_smul (quadOdd 3 F) hab m₁ (-m₂) m₂ m₁
  have hQ1 := CFSG.RankThree.Classical.quad_smul_add_smul (quadOdd 3 F) hab m₁ (-m₂)
  have hQ2 := CFSG.RankThree.Classical.quad_smul_add_smul (quadOdd 3 F) hab m₂ m₁
  refine ⟨algebraMap F K m₁ + D.θ * algebraMap F K m₂, m₁ • a' + (-m₂) • b',
    m₂ • a' + m₁ • b', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    obtain ⟨h1, h3⟩ := theta_indep D h2 h
    exact hmne (by rw [h1, h3]; ring)
  · rw [emb_add, emb_add, emb_smul, emb_smul, emb_smul, emb_smul, map_neg]
    linear_combination (norm := module) (algebraMap F K m₂) • theta_mul_self D •
      (emb (K := K) b')
  · rw [hQ1, ← hq]
    linear_combination hm'
  · rw [hQ2, ← hq]
    linear_combination hm'
  · rw [hpol, ← hq]
    ring
  · intro r h1 h2'
    refine ⟨?_, ?_⟩
    · rw [polar_add_left, polar_smul_left, polar_smul_left, h1, h2']
      simp
    · rw [polar_add_left, polar_smul_left, polar_smul_left, h1, h2']
      simp

end CFSG.ClassicalInvolution.PhanB3.S
