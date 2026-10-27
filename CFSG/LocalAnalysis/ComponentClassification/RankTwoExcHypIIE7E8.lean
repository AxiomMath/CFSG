module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoExcHypIIBasic
public import CFSG.LieType.Chevalley.EvenQuadraticGraphFieldDescent
public import CFSG.LieType.Chevalley.EvenCanonicalFieldCentralizer
public import CFSG.LieType.Chevalley.ExceptionalG2F4ModelSchreier

public section

namespace CFSG.ComponentClassification.RankTwoExcHypII

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.RankTwoHypIIY
open CFSG.ComponentClassification.OuterAutomorphisms (inner_normal)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)

theorem rigidInvolution_E7_E8
    {τ : Tag}
    (hτ : τ = .E7 ∨ τ = .E8) {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K]
    (hK : Nat.card K = 2 ^ f) (α : MulAut (adjointGroup τ K))
    (hαX : α ∉ OuterAutomorphisms.inner (adjointGroup τ K)) (hα2 : α ^ 2 = 1) :
    RigidInvolution (OuterAutomorphisms.inner (adjointGroup τ K)) α := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : Finite (ModGL τ K) := finite_modGL
  have : Finite (adjointGroup τ K) := Subtype.finite
  have hZ : center (adjointGroup τ K) = ⊥ := center_adjointGroup_eq_bot
  obtain ⟨hNF, Θ, hΘ, -, hker, hinv⟩ :=
    even_E7_E8_exact_inner_field_automorphism_normal_form hf K hK τ hτ
  obtain ⟨⟨g, σ⟩, hgσ, -⟩ := hNF α
  have hΘα : Θ α = σ := hΘ α g σ hgσ
  rcases hinv α hα2 with h1 | ⟨⟨e, he⟩, hpow⟩
  · have hmem : α ∈ Θ.ker := MonoidHom.mem_ker.2 h1
    rw [hker] at hmem
    exact absurd hmem hαX
  have he1 : 1 ≤ e := by omega
  have hK' : Nat.card K = 2 ^ (2 * e) := by rw [hK, he, two_mul]
  have hσ : ∀ c, σ c = c ^ 2 ^ e := fun c => by
    rw [← hΘα, hpow, show f / 2 = e by omega]
  obtain ⟨β, -, hdesc⟩ :=
    (even_exceptional_quadratic_field_graph_field_involution_descent he1 K hK' σ.toRingHom hσ).1 τ
  obtain ⟨-, hψ⟩ := hdesc g 1
  obtain ⟨ψ, hψα, -⟩ := hψ α (fun u => by
    rw [hgσ u, rootDiagUnit_one, mul_one, inv_one, mul_one]) (by rw [← sq, hα2])
  have hψ' : ψ * α * ψ⁻¹ = entrywiseAdjointAut τ σ :=
    MulEquiv.ext fun u => Subtype.ext (by rw [hψα u, coe_entrywiseAdjointAut])
  refine rigidInvolution_of_conj hψ' ?_
  set η := entrywiseAdjointAut τ σ
  have hη2 : η ^ 2 = 1 := by
    rw [← hψ', sq, show ψ * α * ψ⁻¹ * (ψ * α * ψ⁻¹) = ψ * (α * α) * ψ⁻¹ by group, ← sq, hα2,
      mul_one, mul_inv_cancel]
  have hηX : η ∉ OuterAutomorphisms.inner (adjointGroup τ K) := fun h => hαX (by
    have := (inner_normal _).conj_mem _ h ψ⁻¹
    rwa [← hψ', show ψ⁻¹ * (ψ * α * ψ⁻¹) * ψ⁻¹⁻¹ = α by group] at this)
  obtain ⟨-, -, hJC, -, ⟨-, hJs, hJe, -, -⟩, -, -, -, hNη, hNnorm, hcent⟩ :=
    even_E7_E8_canonical_field_full_centralizer τ hτ he1 K hK' σ hσ
  exact rigidInvolution_of_simple' hZ hηX hη2 hJC hJs hJe hNη hNnorm hcent.le

theorem hypII_of_E7_E8
    {A : Type} [Group A] [Finite A]
    (hA : commutator A = ⊤) {t : CFSG.Assembly.LowTwoRank.StatedLieTag} (ht : t = .E7 ∨ t = .E8)
    {m : ℕ} (hm : 1 ≤ m) (h : ChevalleyExceptionalModel (A ⧸ center A) t 2 m) : HypII A := by
  obtain ⟨τ, hτ, hmod⟩ : ∃ τ : Tag, (τ = .E7 ∨ τ = .E8) ∧
      UntwistedChevalleyModel (A ⧸ center A) τ (2 ^ m) := by
    rcases ht with rfl | rfl
    · exact ⟨.E7, Or.inl rfl, h.2⟩
    · exact ⟨.E8, Or.inr rfl, h.2⟩
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup τ hmod
  have : Finite (adjointGroup τ K) := Finite.of_equiv _ e.toEquiv
  exact hypII_of_forall_rigid center_adjointGroup_eq_bot
    (fun α hα hα2 => rigidInvolution_E7_E8 hτ hm hK α hα hα2) hA e

end CFSG.ComponentClassification.RankTwoExcHypII
