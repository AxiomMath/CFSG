module

public import CFSG.LieType.Chevalley.TwistedE6NormalForm

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.ComponentClassification

theorem twisted_E6_odd_exact_automorphism_normal_form
    {p f : ℕ} (hp : p.Prime) (_hp2 : p ≠ 2)
    (hf : 1 ≤ f) (K : Type) [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (p ^ f)) :
    orbitField TwistTag.E6 K σ.toRingHom ⟨0, by decide⟩ = ⊤ ∧
    orbitField TwistTag.E6 K σ.toRingHom ⟨1, by decide⟩ = ⊤ ∧
    (∀ c, c ∈ orbitField TwistTag.E6 K σ.toRingHom ⟨2, by decide⟩ ↔ σ c = c) ∧
    (∀ c, c ∈ orbitField TwistTag.E6 K σ.toRingHom ⟨3, by decide⟩ ↔ σ c = c) ∧
    (∀ u, compatDiag TwistTag.E6 σ.toRingHom u =
      ![orbitFieldUnit TwistTag.E6 σ.toRingHom (u ⟨0, by decide⟩),
        orbitFieldUnit TwistTag.E6 σ.toRingHom (u ⟨3, by decide⟩),
        orbitFieldUnit TwistTag.E6 σ.toRingHom (u ⟨1, by decide⟩),
        orbitFieldUnit TwistTag.E6 σ.toRingHom (u ⟨2, by decide⟩),
        Units.map σ.toRingHom.toMonoidHom
          (orbitFieldUnit TwistTag.E6 σ.toRingHom (u ⟨1, by decide⟩)),
        Units.map σ.toRingHom.toMonoidHom
          (orbitFieldUnit TwistTag.E6 σ.toRingHom (u ⟨0, by decide⟩))]) ∧
    (∀ u (g : twistedE6RootGroup K σ),
      ((compatDiagAutHom TwistTag.E6 K σ.toRingHom u g : twistedE6RootGroup K σ) :
        ModGL TwistTag.E6.tag K) =
      rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σ.toRingHom u) * g *
        (rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σ.toRingHom u))⁻¹) ∧
    (∀ (δ : K ≃+* K) (g : twistedE6RootGroup K σ),
      ((fieldActor σ δ g : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) =
        Units.map (entrywiseHom δ.toRingHom) g) ∧
    (∀ α : MulAut (twistedE6RootGroup K σ), ∃ g u δ,
      α = MulAut.conj g * compatDiagAutHom TwistTag.E6 K σ.toRingHom u * fieldActor σ δ) ∧
    (∃ Θ : MulAut (twistedE6RootGroup K σ) →* RingAut K,
      (∀ α g u δ, α = MulAut.conj g * compatDiagAutHom TwistTag.E6 K σ.toRingHom u *
        fieldActor σ δ → Θ α = δ) ∧
      Function.Surjective Θ ∧
      Θ.ker = twistedE6Inn K σ ⊔ twistedE6Diag K σ ∧
      (∀ a b : ↥(twistedE6Inn K σ ⊔ twistedE6Diag K σ) ⧸
          (twistedE6Inn K σ).subgroupOf (twistedE6Inn K σ ⊔ twistedE6Diag K σ), a * b = b * a) ∧
      (∀ a : ↥(twistedE6Inn K σ ⊔ twistedE6Diag K σ) ⧸
          (twistedE6Inn K σ).subgroupOf (twistedE6Inn K σ ⊔ twistedE6Diag K σ), a ^ 3 = 1) ∧
      ∀ α : MulAut (twistedE6RootGroup K σ), α ^ 2 = 1 →
        α ∈ twistedE6Inn K σ ∨ (Θ α = σ ∧ ∃ g u,
          α = MulAut.conj g * compatDiagAutHom TwistTag.E6 K σ.toRingHom u * fieldActor σ σ)) ∧
    (∀ g : twistedE6RootGroup K σ,
      ((fieldActor σ σ g : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) =
        diagramMap TwistTag.E6 K * g * (diagramMap TwistTag.E6 K)⁻¹) ∧
    ⁅twistedFixedGroup TwistTag.E6 K σ.toRingHom, twistedFixedGroup TwistTag.E6 K σ.toRingHom⁆ =
      twistedE6RootGroup K σ ∧
    Subgroup.center (twistedE6RootGroup K σ) = ⊥ ∧
    Nonempty (DerivedCentralQuotient (twistedFixedGroup TwistTag.E6 K σ.toRingHom) ≃*
      twistedE6RootGroup K σ) ∧
    ∀ (G : Type) [Group G], ChevalleyExceptionalModel G .twistedE6 p f →
      ∃ (K' : Type) (_ : Field K') (_ : Finite K') (σ' : K' ≃+* K'),
        Nat.card K' = (p ^ f) ^ 2 ∧ (∀ c, σ' c = c ^ (p ^ f)) ∧
        Nonempty (G ≃* twistedE6RootGroup K' σ') :=
  twisted_E6_all_characteristic_exact_automorphism_normal_form hp hf K hK σ hσ

end CFSG.LieType.Chevalley
