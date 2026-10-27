module

public import CFSG.GroupTheory.WeirSylow.OrthogonalTypes

public section

namespace CFSG.ClassicalInvolution.RouteD.TWY

open CFSG.GroupTheory.WeirSylow CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.LieType.Universal.Spin (quadPlus quadMinus)

variable {F : Type} [Field F] [Finite F]

section Prod

variable {V₁ V₂ : Type} [AddCommGroup V₁] [Module F V₁] [FiniteDimensional F V₁]
  [AddCommGroup V₂] [Module F V₂] [FiniteDimensional F V₂] {Q₁ : QuadraticForm F V₁}
  {Q₂ : QuadraticForm F V₂}

theorem isPlusType_prod_iff (hQ₁ : (polarBilin Q₁).Nondegenerate)
    (hQ₂ : (polarBilin Q₂).Nondegenerate) {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hda : Module.finrank F V₁ = 2 * a) (hdb : Module.finrank F V₂ = 2 * b) :
    IsPlusType (Q₁.prod Q₂) ↔ (IsPlusType Q₁ ↔ IsPlusType Q₂) := by
  by_cases h₂ : IsPlusType Q₂
  · obtain ⟨e⟩ := nonempty_isometry_quadPlus hQ₂ hdb h₂
    have e' : (Q₁.prod Q₂).IsometryEquiv (Q₁.prod (quadPlus b F)) :=
      (QuadraticMap.IsometryEquiv.refl Q₁).prod e
    rw [isPlusType_congr e']
    by_cases h₁ : IsPlusType Q₁
    · exact iff_of_true (h₁.prod (isPlusType_quadPlus F b)) (iff_of_true h₁ h₂)
    · exact iff_of_false (not_isPlusType_prod_quadPlus hQ₁ ha hda h₁ b)
        (fun h => h₁ (h.mpr h₂))
  · rcases exists_isometry_quadPlus_or_quadMinus Q₂ hQ₂ hb hdb with he | ⟨b', c', hirr, he⟩
    · obtain ⟨e⟩ := he
      exact absurd ((isPlusType_congr e).2 (isPlusType_quadPlus F b)) h₂
    obtain ⟨e⟩ := he
    have e' : (Q₁.prod Q₂).IsometryEquiv (Q₁.prod (quadMinus b F b' c')) :=
      (QuadraticMap.IsometryEquiv.refl Q₁).prod e
    rw [isPlusType_congr e']
    by_cases h₁ : IsPlusType Q₁
    · exact iff_of_false (not_isPlusType_prod_quadMinus hQ₁ hda h₁ hb hirr)
        (fun h => h₂ (h.mp h₁))
    · exact iff_of_true (isPlusType_prod_quadMinus hQ₁ ha hda h₁ b hirr)
        ⟨fun h => absurd h h₁, fun h => absurd h h₂⟩

end Prod

section Internal

variable {V : Type} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  {Q : QuadraticForm F V}

@[expose] noncomputable def orthSumIsometry {X W : Submodule F V} (hc : IsCompl X W)
    (horth : ∀ x ∈ X, ∀ y ∈ W, polar Q x y = 0) :
    ((Q.restrict X).prod (Q.restrict W)).IsometryEquiv Q where
  toLinearEquiv := Submodule.prodEquivOfIsCompl X W hc
  map_app' p := by
    show Q (Submodule.prodEquivOfIsCompl X W hc p) = Q p.1 + Q p.2
    rw [Submodule.coe_prodEquivOfIsCompl', QuadraticMap.map_add Q, horth _ p.1.2 _ p.2.2, add_zero]

theorem isPlusType_iff_of_isCompl {X W : Submodule F V} (hc : IsCompl X W)
    (horth : ∀ x ∈ X, ∀ y ∈ W, polar Q x y = 0) (hX : PolarNondegOn Q X)
    (hW : PolarNondegOn Q W) {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hXd : Module.finrank F X = 2 * a) (hWd : Module.finrank F W = 2 * b) :
    IsPlusType Q ↔ (IsPlusType (Q.restrict X) ↔ IsPlusType (Q.restrict W)) := by
  rw [← isPlusType_congr (orthSumIsometry hc horth)]
  exact isPlusType_prod_iff (nondegenerate_polarBilin_restrict hX)
    (nondegenerate_polarBilin_restrict hW) ha hb hXd hWd

end Internal

end CFSG.ClassicalInvolution.RouteD.TWY
