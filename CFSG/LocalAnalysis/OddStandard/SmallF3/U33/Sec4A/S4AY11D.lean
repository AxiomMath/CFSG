module

public import CFSG.GH74.GLS.Bg.TwoGroups.L26Abel
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AY11B

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup
open scoped Pointwise commutatorElement

section Y11D

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G}

theorem m11_V_le_nR (h : L41GPh8 t L S x₁ x₂ lam rho) :
    l41V S t x₁ x₂ ≤ normalizer ((l41R t x₁ x₂ rho : Subgroup G) : Set G) := by
  rw [h.rfacts.V_eq]
  exact sup_le Subgroup.le_normalizer (m11_K_le_nR h)

theorem m11_sq_mem_R (h : L41GPh8 t L S x₁ x₂ lam rho) {g : G} (hg : g ∈ l41V S t x₁ x₂) :
    g * g ∈ l41R t x₁ x₂ rho := by
  have hl2 : lam * lam = 1 := n4_lam_sq h.toCtx0
  have ht2 : t * t = 1 := t_mul_self h.hyp
  have htl : t * lam = lam * t := m13_t_comm_L h.toL41GPh5 (generators_mem_L h.toCtx0).2.2
  have hKinv : ∀ k : G, k ∈ normalizer ((l41R t x₁ x₂ rho : Subgroup G) : Set G) → k * k = 1 →
      ∀ r ∈ l41R t x₁ x₂ rho, (r * k) * (r * k) ∈ l41R t x₁ x₂ rho := by
    intro k hk hk2 r hr
    have e : (r * k) * (r * k) = r * (k * r * k⁻¹) * (k * k) := by group
    rw [e, hk2, mul_one]
    exact Subgroup.mul_mem _ hr ((Subgroup.mem_normalizer_iff.mp hk r).mp hr)
  obtain ⟨r, hr, hcases⟩ := m11_mem_V_cases h hg
  obtain ⟨-, hlamN, htN⟩ := n4_mem_normalizer_R h
  rcases hcases with hg1 | hg1 | hg1 | hg1 <;> rw [hg1]
  · exact Subgroup.mul_mem _ hr hr
  · exact hKinv t htN ht2 r hr
  · exact hKinv lam hlamN hl2 r hr
  · refine hKinv (t * lam) (Subgroup.mul_mem _ htN hlamN) ?_ r hr
    rw [htl]
    exact m11_lamt_sq h.toL41GPh5

theorem m11_quot_V_R (h : L41GPh8 t L S x₁ x₂ lam rho) :
    Sec4SectionIso (l41V S t x₁ x₂) (l41R t x₁ x₂ rho)
      (CFSG.GH74.GLS.Bg.TwoGroups.E2 2) := by
  classical
  have hRV := m11_R_le_V h
  haveI hN : ((l41R t x₁ x₂ rho).subgroupOf (l41V S t x₁ x₂)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRV).mpr (m11_V_le_nR h)
  have hcard : Nat.card (↥(l41V S t x₁ x₂) ⧸
      (l41R t x₁ x₂ rho).subgroupOf (l41V S t x₁ x₂)) = 2 ^ 2 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
      ((l41R t x₁ x₂ rho).subgroupOf (l41V S t x₁ x₂))
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRV).toEquiv, m11_card_V h,
      h.rfacts.card_R] at h1
    omega
  have h2 : ∀ q : ↥(l41V S t x₁ x₂) ⧸ (l41R t x₁ x₂ rho).subgroupOf (l41V S t x₁ x₂),
      q * q = 1 := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H g =>
      rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact m11_sq_mem_R h g.2
  have hc : ∀ a b : ↥(l41V S t x₁ x₂) ⧸ (l41R t x₁ x₂ rho).subgroupOf (l41V S t x₁ x₂),
      a * b = b * a := by
    intro a b
    have hinv : ∀ q : ↥(l41V S t x₁ x₂) ⧸ (l41R t x₁ x₂ rho).subgroupOf (l41V S t x₁ x₂),
        q⁻¹ = q := fun q => inv_eq_of_mul_eq_one_right (h2 q)
    calc a * b = (a * b)⁻¹ := (hinv _).symm
      _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
      _ = b * a := by rw [hinv a, hinv b]
  obtain ⟨e⟩ := CFSG.GH74.GLS.Bg.TwoGroups.L26.elemAbelian_equiv hc h2 2 hcard
  refine ⟨e.toMonoidHom.comp (QuotientGroup.mk' _), ?_, ?_⟩
  · exact e.surjective.comp (QuotientGroup.mk'_surjective _)
  · rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']

end Y11D

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
