module

public import CFSG.ClassicalInvolution.Phan.PhanS9WKfld

public section

namespace CFSG.ClassicalInvolution.PhanB3.S

open CFSG.LieType.Universal.Spin QuadraticMap

theorem refl_identity {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
    (θ S T cp cq N : K) (hθ : θ * θ = -1) (hN : N = S * S + T * T) (hN0 : N ≠ 0)
    (hcp : cp * N = 2 * S) (hcq : cq * N = 2 * T) (P Q' : M) :
    (P - cp • (S • P + T • Q')) + θ • (Q' - cq • (S • P + T • Q')) =
      (-(S + θ * T) ^ 2 / N) • (P - θ • Q') := by
  have hl : (cp + θ * cq) * N = 2 * (S + θ * T) := by linear_combination hcp + θ * hcq
  have key : N • ((P - cp • (S • P + T • Q')) + θ • (Q' - cq • (S • P + T • Q'))) =
      N • ((-(S + θ * T) ^ 2 / N) • (P - θ • Q')) := by
    have e : N * (-(S + θ * T) ^ 2 / N) = -(S + θ * T) ^ 2 := by field_simp
    rw [smul_smul, e]
    subst hN
    linear_combination (norm := module) (T ^ 2) • hθ • P +
      (-(θ * T ^ 2 + 2 * S * T)) • hθ • Q' - (S • hl • P) - (T • hl • Q')
  exact smul_right_injective M hN0 key

variable {F K : Type} [Field F] [Field K] [Algebra F K] (D : KDat F K)

theorem extK_reflection_plane {p q : W7 F} (hpq : polar (quadOdd 3 F) p q = 0) {α : F}
    (hp : quadOdd 3 F p = α) (hq : quadOdd 3 F q = α) (hα : α ≠ 0) {s t : F}
    (hn : s ^ 2 + t ^ 2 ≠ 0) {w : W7 F} (hw : w = s • p + t • q)
    [Invertible (quadOdd 3 F w)] :
    extK (K := K) (TauCeti.QuadraticMap.reflection (quadOdd 3 F) w).toLinearMap
        (emb p + D.θ • emb q) =
      (-(algebraMap F K s + D.θ * algebraMap F K t) ^ 2 / algebraMap F K (s ^ 2 + t ^ 2)) •
        (emb p - D.θ • emb q) := by
  have hQw : quadOdd 3 F w = α * (s ^ 2 + t ^ 2) := by
    rw [hw, CFSG.RankThree.Classical.quad_smul_add_smul _ hpq, hp, hq]
    ring
  have hpp : polar (quadOdd 3 F) w p = 2 * (s * α) := by
    have := CFSG.RankThree.Classical.polar_smul_add_smul (quadOdd 3 F) hpq s t 1 0
    simp only [one_smul, zero_smul, add_zero] at this
    rw [hw, this, hp]
    ring
  have hpq' : polar (quadOdd 3 F) w q = 2 * (t * α) := by
    have := CFSG.RankThree.Classical.polar_smul_add_smul (quadOdd 3 F) hpq s t 0 1
    simp only [one_smul, zero_smul, zero_add] at this
    rw [hw, this, hq]
    ring
  have hrefl : ∀ z : W7 F, TauCeti.QuadraticMap.reflection (quadOdd 3 F) w z =
      z - (polar (quadOdd 3 F) w z / quadOdd 3 F w) • w := fun z =>
    TauCeti.QuadraticMap.reflection_apply_eq_sub_div _ w z
  have hcp : polar (quadOdd 3 F) w p / quadOdd 3 F w * (s ^ 2 + t ^ 2) = 2 * s := by
    rw [hpp, hQw]
    field_simp
  have hcq : polar (quadOdd 3 F) w q / quadOdd 3 F w * (s ^ 2 + t ^ 2) = 2 * t := by
    rw [hpq', hQw]
    field_simp
  have hmap : ∀ z : W7 F, extK (K := K)
      (TauCeti.QuadraticMap.reflection (quadOdd 3 F) w).toLinearMap (emb z) =
      emb z - algebraMap F K (polar (quadOdd 3 F) w z / quadOdd 3 F w) •
        (algebraMap F K s • emb p + algebraMap F K t • emb q) := fun z => by
    rw [extK_emb, LinearEquiv.coe_coe, hrefl, emb_sub, emb_smul, hw, emb_add, emb_smul, emb_smul]
  rw [map_add, map_smul, hmap, hmap]
  have hS : algebraMap F K (s ^ 2 + t ^ 2) =
      algebraMap F K s * algebraMap F K s + algebraMap F K t * algebraMap F K t := by
    simp only [map_add, map_pow]
    ring
  exact refl_identity D.θ _ _ _ _ _ (theta_mul_self D) hS
    ((map_ne_zero_iff _ (algebraMap F K).injective).2 hn)
    (by rw [← map_mul, hcp, map_mul, map_ofNat]) (by rw [← map_mul, hcq, map_mul, map_ofNat])
    (emb p) (emb q)

theorem extK_reflection_self {p q : W7 F} (hpq : polar (quadOdd 3 F) p q = 0)
    [Invertible (quadOdd 3 F p)] :
    extK (K := K) (TauCeti.QuadraticMap.reflection (quadOdd 3 F) p).toLinearMap
        (emb p - D.θ • emb q) = -(emb p + D.θ • emb q) := by
  rw [map_sub, map_smul, extK_emb, extK_emb, LinearEquiv.coe_coe,
    TauCeti.QuadraticMap.reflection_apply_self,
    TauCeti.QuadraticMap.reflection_apply_of_polar_eq_zero _ p hpq, emb_neg]
  module

theorem extK_reflection_pair {p q : W7 F} (hpq : polar (quadOdd 3 F) p q = 0) {α : F}
    (hp : quadOdd 3 F p = α) (hq : quadOdd 3 F q = α) (hα : α ≠ 0) {s t : F}
    (hn : s ^ 2 + t ^ 2 ≠ 0) {w : W7 F} (hw : w = s • p + t • q)
    [Invertible (quadOdd 3 F p)] [Invertible (quadOdd 3 F w)] :
    ∃ c : K, c ≠ 0 ∧ extK (K := K) (TauCeti.QuadraticMap.reflection (quadOdd 3 F) p *
        TauCeti.QuadraticMap.reflection (quadOdd 3 F) w : W7 F ≃ₗ[F] W7 F).toLinearMap
        (emb p + D.θ • emb q) = c • (emb p + D.θ • emb q) := by
  have hcomp : (TauCeti.QuadraticMap.reflection (quadOdd 3 F) p *
        TauCeti.QuadraticMap.reflection (quadOdd 3 F) w : W7 F ≃ₗ[F] W7 F).toLinearMap =
      (TauCeti.QuadraticMap.reflection (quadOdd 3 F) p).toLinearMap ∘ₗ
        (TauCeti.QuadraticMap.reflection (quadOdd 3 F) w).toLinearMap := rfl
  have hN : algebraMap F K (s ^ 2 + t ^ 2) ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap F K).injective).2 hn
  have hN' : algebraMap F K (s ^ 2 + t ^ 2) = (algebraMap F K s + D.θ * algebraMap F K t) *
      (algebraMap F K s - D.θ * algebraMap F K t) := by
    simp only [map_add, map_pow]
    linear_combination (algebraMap F K t) ^ 2 * theta_mul_self D
  have hSθ : algebraMap F K s + D.θ * algebraMap F K t ≠ 0 := fun h => by
    rw [h, zero_mul] at hN'
    exact hN hN'
  refine ⟨(algebraMap F K s + D.θ * algebraMap F K t) ^ 2 / algebraMap F K (s ^ 2 + t ^ 2),
    div_ne_zero (pow_ne_zero 2 hSθ) hN, ?_⟩
  rw [hcomp, extK_comp, LinearMap.comp_apply, extK_reflection_plane D hpq hp hq hα hn hw,
    map_smul, extK_reflection_self D hpq, smul_neg, ← neg_smul]
  congr 1
  ring

end CFSG.ClassicalInvolution.PhanB3.S
