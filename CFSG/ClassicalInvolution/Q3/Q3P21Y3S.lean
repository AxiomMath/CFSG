module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Q3.Q3TPCtx

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3P21

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Q3 (IsClassicalMember3)


@[expose] def LiftYStmt {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G}
    {K : Subgroup G} (c : Q3TP.TCtxS3 .PSU 4 Ω K z) : Prop :=
  ∀ (t : G) (ht : t * z * t⁻¹ = z) (K₂ K₂' T : Subgroup G) (w : G),
    K₂ ∈ centralizingMembers Ω {z} → K₂' ∈ centralizingMembers Ω {z} →
    T ∈ centralizingMembers Ω {z} → locImg Ω z T ≤ c.d.Q₁ → IsClassicalMember3 K₂ w →
    w * t = t * w → ∀ y₀ : locQuot Ω z, y₀ ∈ c.d.ψ.range →
      (∀ a ∈ locImg Ω z K₂, y₀ * a * y₀⁻¹ = Gaps.locAut c.hΩ.conjInvariant ht a) →
      (∀ a ∈ locImg Ω z K₂', y₀ * a * y₀⁻¹ = Gaps.locAut c.hΩ.conjInvariant ht a) →
      ∃ (y : G) (hy : y ∈ locLayer Ω z), Gaps.locMk Ω z ⟨y, hy⟩ = y₀ ∧ y * w * y⁻¹ = w ∧
        K ≤ Subgroup.centralizer ({y} : Set G) ∧ T ≤ Subgroup.centralizer ({y} : Set G) ∧
        (∀ k ∈ K₂, y * k * y⁻¹ = t * k * t⁻¹) ∧ (∀ k ∈ K₂', y * k * y⁻¹ = t * k * t⁻¹)

@[expose] def StabStmt {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G}
    {K : Subgroup G} (c : Q3TP.TCtxS3 .PSU 4 Ω K z) : Prop :=
  ∀ (t : G) (ht : t * z * t⁻¹ = z), t * t = 1 → conjSub t K = K →
    ∀ x, Gaps.locAut c.hΩ.conjInvariant ht (c.d.ψ x) ∈ c.d.ψ.range

theorem locAut_locMk_of_commute {G : Type} [Group G] {Ω : Set (Subgroup G)}
    (hΩ : ConjInvariant Ω) {t z y : G} (ht : t * z * t⁻¹ = z) (hy : y ∈ locLayer Ω z)
    (hyt : y * t * y⁻¹ = t) :
    Gaps.locAut hΩ ht (Gaps.locMk Ω z ⟨y, hy⟩) = Gaps.locMk Ω z ⟨y, hy⟩ := by
  rw [Gaps.locAut_mk]
  congr 1
  apply Subtype.ext
  rw [Gaps.coe_layerAut]
  have h1 : y * t = t * y := mul_inv_eq_iff_eq_mul.mp hyt
  calc t * y * t⁻¹ = y * t * t⁻¹ := by rw [h1]
    _ = y := by group

end CFSG.ClassicalInvolution.Q3.Q3P21
