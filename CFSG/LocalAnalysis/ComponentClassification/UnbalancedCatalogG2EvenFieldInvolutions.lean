module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenAutomorphisms
public import CFSG.LieType.Chevalley.EvenQuadraticGraphFieldDescent

public noncomputable section

namespace CFSG.ComponentClassification.UnbalancedCatalog

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem even_G2_involution_inner_or_canonical_field {f : ℕ} (hf : 2 ≤ f) (K : Type) [Field K]
    (hK : Nat.card K = 2 ^ f) (α : MulAut (adjointGroup .G2 K)) (hα : orderOf α = 2) :
    α ∈ inner (adjointGroup .G2 K) ∨
      (Even f ∧ ∀ δ : K →+* K, (∀ c, δ c = c ^ 2 ^ (f / 2)) →
        ∃ β ψ : MulAut (adjointGroup .G2 K),
          (∀ u, (β u : ModGL .G2 K) = Units.map (entrywiseHom δ) (u : ModGL .G2 K)) ∧
          ψ * α * ψ⁻¹ = β ∧
          (Subgroup.centralizer {α}).map (MulAut.conj ψ).toMonoidHom =
            Subgroup.centralizer {β}) := by
  obtain ⟨hNF, Θ, hΘ, -, hker, hinv⟩ := even_G2_exact_automorphism_normal_form hf K hK
  have hα2 : α ^ 2 = 1 := by rw [← hα, pow_orderOf_eq_one]
  obtain ⟨⟨g, σ⟩, hgσ, -⟩ := hNF α
  have hσ : Θ α = σ := hΘ α g σ hgσ
  rcases hinv α hα2 with h1 | ⟨hev, hpow, -⟩
  · left
    have hmem : α ∈ Θ.ker := MonoidHom.mem_ker.2 h1
    rw [hker] at hmem
    exact hmem
  · right
    refine ⟨hev, fun δ hδ => ?_⟩
    obtain ⟨e, he⟩ := hev
    have he' : f / 2 = e := by omega
    have he1 : 1 ≤ e := by omega
    have hK' : Nat.card K = 2 ^ (2 * e) := by rw [hK, show f = 2 * e by omega]
    have hδe : ∀ c, δ c = c ^ 2 ^ e := fun c => by rw [hδ, he']
    obtain ⟨β, hβ, hdesc⟩ :=
      (even_exceptional_quadratic_field_graph_field_involution_descent he1 K hK' δ hδe).1 .G2
    have hσδ : σ.toRingHom = δ := by
      refine RingHom.ext fun c => ?_
      rw [hδ, ← hpow c, hσ]
      rfl
    have hαform : ∀ u, (α u : ModGL .G2 K) = (g : ModGL .G2 K) * rootDiagUnit .G2 1 *
        Units.map (entrywiseHom δ) (u : ModGL .G2 K) * (rootDiagUnit .G2 1)⁻¹ *
          (g : ModGL .G2 K)⁻¹ := fun u => by
      rw [hgσ u, rootDiagUnit_one, mul_one, inv_one, mul_one, hσδ]
    obtain ⟨-, hψ⟩ := hdesc g 1
    obtain ⟨ψ, hψα, -, -, hcent, -⟩ := hψ α hαform (by rw [← sq, hα2])
    refine ⟨β, ψ, hβ, MulEquiv.ext fun u => Subtype.ext ?_, hcent⟩
    rw [hψα u, hβ u]

end CFSG.ComponentClassification.UnbalancedCatalog
