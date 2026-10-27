module

public import CFSG.LieType.CurtisTits.Recognition
public import CFSG.Blueprint.Catalog

public section

namespace CFSG.LieType.CurtisTits

open CFSG.Blueprint.Chevalley CFSG.Blueprint

variable {K : Type*} [Group K]

theorem adjointQuotientEquiv_of_surjective (hK : IsQuasisimple K) {τ : Tag} {k : Type}
    [Field k] (φ : K →* ↥(adjointGroup τ k)) (hφ : Function.Surjective φ) (hφ1 : ∃ x, φ x ≠ 1) :
    Nonempty (K ⧸ Subgroup.center K ≃* AdjointQuotient τ k) :=
  ⟨centralQuotientEquivOfIsQuasisimple hK hφ (ker_le_center_of_isQuasisimple hK hφ1)⟩

theorem untwistedChevalleyModel_of_surjective (hK : IsQuasisimple K) {τ : Tag} {k : Type}
    [Field k] [Finite k] {q : ℕ} (hk : Nat.card k = q) (φ : K →* ↥(adjointGroup τ k))
    (hφ : Function.Surjective φ) (hφ1 : ∃ x, φ x ≠ 1) {G : Type} [Group G]
    (e : G ≃* K ⧸ Subgroup.center K) : UntwistedChevalleyModel G τ q := by
  obtain ⟨e'⟩ := adjointQuotientEquiv_of_surjective hK φ hφ hφ1
  exact ⟨k, inferInstance, inferInstance, hk, ⟨e.trans e'⟩⟩

theorem twistedChevalleyModel_of_surjective (hK : IsQuasisimple K) {t : TwistTag} {k : Type}
    [Field k] [Finite k] {q : ℕ} (hk : Nat.card k = q ^ t.order) (σ : k →+* k)
    (hσ : ∀ c, σ c = c ^ q)
    (φ : K →* ↥⁅twistedFixedGroup t k σ, twistedFixedGroup t k σ⁆) (hφ : Function.Surjective φ)
    (hφ1 : ∃ x, φ x ≠ 1) {G : Type} [Group G] (e : G ≃* K ⧸ Subgroup.center K) :
    TwistedChevalleyModel G t q :=
  ⟨k, inferInstance, inferInstance, hk, σ, hσ,
    ⟨e.trans (centralQuotientEquivOfIsQuasisimple hK hφ (ker_le_center_of_isQuasisimple hK hφ1))⟩⟩

end CFSG.LieType.CurtisTits
