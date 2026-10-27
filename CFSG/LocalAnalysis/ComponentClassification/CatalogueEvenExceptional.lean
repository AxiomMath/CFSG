module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueUAlmostSimple
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenAlmostSimple
public import CFSG.LocalAnalysis.ComponentClassification.SteinbergBNEvenInnerInvolutionOddCore
public import CFSG.LieType.Chevalley.EvenOuterInvolutionOddCoreF4
public import CFSG.LieType.Chevalley.EvenOuterInvolutionOddCoreE7E8
public import CFSG.LieType.Chevalley.EvenOuterInvolutionOddCoreTriality
public import CFSG.RankThree.Chevalley.SteinbergCFExceptionalModelCover

public section

namespace CFSG.ComponentClassification.CatalogueU

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.UnbalancedCatalog.EvenLinearSL (conjModel conjModel_apply
  conjModel_of_mem center_eq_bot_of_simple)

@[expose] def EvenE6OuterInvolutionInput : Prop :=
  (∀ f : ℕ, 1 ≤ f → ∀ (k : Type) [Field k], Nat.card k = 2 ^ f →
    ∀ H : Subgroup (MulAut (adjointGroup .E6 k)), inner (adjointGroup .E6 k) ≤ H →
      ∀ α ∈ H, α ∉ inner (adjointGroup .E6 k) → orderOf α = 2 →
        CFSG.oddCore ↥(H ⊓ centralizer {α}) = ⊥) ∧
  ∀ f : ℕ, 1 ≤ f → ∀ (K : Type) [Field K] [Finite K], Nat.card K = (2 ^ f) ^ 2 →
    ∀ σ : K ≃+* K, (∀ c, σ c = c ^ 2 ^ f) →
    ∀ H : Subgroup (MulAut (graphFixedRootGroup .E6 K σ.toRingHom)),
      inner (graphFixedRootGroup .E6 K σ.toRingHom) ≤ H →
      ∀ α ∈ H, α ∉ inner (graphFixedRootGroup .E6 K σ.toRingHom) → orderOf α = 2 →
        CFSG.oddCore ↥(H ⊓ centralizer {α}) = ⊥

theorem oddCore_eq_bot_of_pPrimeCore_two {G : Type*} [Group G]
    (h : CFSG.pPrimeCore 2 G = ⊥) : CFSG.oddCore G = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ((CFSG.oddCore_eq_piCore G).trans (CFSG.pPrimeCore_eq_piCore G 2).symm).trans h

theorem oddCore_centralizer_eq_bot_of_conjModel {X : Type} [Group X] [Finite X]
    [IsSimpleGroup (CFSG.generalizedFitting X)]
    (hnonab : ∃ a b : CFSG.generalizedFitting X, a * b ≠ b * a) {C : Type} [Group C]
    (θ : CFSG.generalizedFitting X ≃* C)
    (h : ∀ H : Subgroup (MulAut C), inner C ≤ H → ∀ α ∈ H, orderOf α = 2 →
      CFSG.oddCore ↥(H ⊓ centralizer {α}) = ⊥)
    {z : X} (hz : orderOf z = 2) : CFSG.oddCore ↥(centralizer {z}) = ⊥ := by
  set F := CFSG.generalizedFitting X with hF
  set ρ := conjModel θ with hρ
  have hinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxC : x ∈ centralizer (F : Set X) := by
      rw [mem_centralizer_iff]
      intro y hy
      have h1 := congrArg (fun φ : MulAut C => φ (θ ⟨y, hy⟩)) hx
      simp only [MulAut.one_apply] at h1
      rw [hρ, conjModel_apply] at h1
      have h2 := congrArg Subtype.val (θ.injective h1)
      simp only at h2
      rw [mul_inv_eq_iff_eq_mul] at h2
      exact h2.symm
    have hxF : x ∈ F := CFSG.centralizer_generalizedFitting_le X hxC
    have hcen : (⟨x, hxF⟩ : F) ∈ center F := by
      rw [mem_center_iff]
      intro y
      exact Subtype.ext (mem_centralizer_iff.mp hxC y y.2)
    rw [center_eq_bot_of_simple hnonab, mem_bot] at hcen
    exact congrArg Subtype.val hcen
  have hinner : inner C ≤ ρ.range := by
    rintro _ ⟨p, rfl⟩
    obtain ⟨y, rfl⟩ := θ.surjective p
    exact ⟨y, conjModel_of_mem θ y⟩
  have hρz : orderOf (ρ z) = 2 := by rw [orderOf_injective ρ hinj z, hz]
  exact UnbalancedCatalog.EvenCatalog.oddCore_eq_bot_of_mulEquiv
    (UnbalancedCatalog.EvenCatalog.centralizerMapEquiv hinj z).symm
    (h ρ.range hinner (ρ z) ⟨z, rfl⟩ hρz)

theorem adjointGroup_involution_centralizer_oddCore (hE6 : EvenE6OuterInvolutionInput)
    {τ : Tag} (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {f : ℕ} (hf : 1 ≤ f) (K : Type)
    [Field K] (hK : Nat.card K = 2 ^ f) (H : Subgroup (MulAut (adjointGroup τ K)))
    (hH : inner (adjointGroup τ K) ≤ H) (α : MulAut (adjointGroup τ K)) (hαH : α ∈ H)
    (hα : orderOf α = 2) : CFSG.oddCore ↥(H ⊓ centralizer {α}) = ⊥ := by
  by_cases hin : α ∈ inner (adjointGroup τ K)
  · have hτ' : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ (τ = .G2 ∧ 2 ≤ f) := by
      rcases hτ with h | h | h | h
      · exact .inl h
      · exact .inr (.inl h)
      · exact .inr (.inr (.inl h))
      · exact .inr (.inr (.inr (.inl h)))
    exact oddCore_eq_bot_of_pPrimeCore_two
      (even_exceptional_inner_involution_full_centralizer_odd_core.1 τ f K hf hK hτ' H hH α hin
        hα)
  · rcases hτ with rfl | rfl | rfl | rfl
    · exact even_F4_outer_involution_full_centralizer_odd_core hf K hK H hH hin hα
    · exact hE6.1 f hf K hK H hH α hαH hin hα
    · exact even_E7_E8_outer_involution_full_centralizer_odd_core .E7 (.inl rfl) hf K hK H hH hin
        hα
    · exact even_E7_E8_outer_involution_full_centralizer_odd_core .E8 (.inr rfl) hf K hK H hH hin
        hα

theorem graphFixedRootGroup_involution_centralizer_oddCore (hE6 : EvenE6OuterInvolutionInput)
    (t : TwistTag) {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ f) ^ t.order) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ f)
    (H : Subgroup (MulAut (graphFixedRootGroup t K σ.toRingHom)))
    (hH : inner (graphFixedRootGroup t K σ.toRingHom) ≤ H)
    (α : MulAut (graphFixedRootGroup t K σ.toRingHom)) (hαH : α ∈ H) (hα : orderOf α = 2) :
    CFSG.oddCore ↥(H ⊓ centralizer {α}) = ⊥ := by
  by_cases hin : α ∈ inner (graphFixedRootGroup t K σ.toRingHom)
  · exact oddCore_eq_bot_of_pPrimeCore_two
      (even_exceptional_inner_involution_full_centralizer_odd_core.2 t f K σ hf hK hσ H hH α
        hin hα)
  · cases t
    · exact hE6.2 f hf K hK σ hσ H hH α hαH hin hα
    · exact even_triality_outer_involution_full_centralizer_odd_core hf K hK σ hσ H hH hin hα

theorem evenExceptionalCheck_of_E6Outer (hE6 : EvenE6OuterInvolutionInput) :
    EvenExceptionalCheck := by
  intro X _ _ hsimple hnonab t f ht hmodel hz
  exfalso
  obtain ⟨z, hz2, hcore⟩ := hz
  apply hcore
  have hF : CFSG.generalizedFitting X = GeneralizedFitting.subgroup X :=
    CFSG.generalizedFitting_eq_componentClassification X
  have hsimple' : IsSimpleGroup (CFSG.generalizedFitting X) := hF ▸ hsimple
  have hnonab' : ∃ a b : CFSG.generalizedFitting X, a * b ≠ b * a := hF ▸ hnonab
  have hmodel' : ChevalleyExceptionalModel (CFSG.generalizedFitting X) t 2 f := hF ▸ hmodel
  obtain ⟨hadm, hcase⟩ := hmodel'
  have hf : 1 ≤ f := hadm.2.1
  simp only [chevalleyExceptionalTags, Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (UnbalancedCatalog.even_G2_almost_simple_odd_core_vanishing hnonab'
      ⟨hadm, hcase⟩).2 z hz2
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hcase
    exact oddCore_centralizer_eq_bot_of_conjModel hnonab'
      (e.trans (RankThree.Chevalley.adjointQuotientEquiv _ K))
      (adjointGroup_involution_centralizer_oddCore hE6 (.inl rfl) hf K hK) hz2
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hcase
    exact oddCore_centralizer_eq_bot_of_conjModel hnonab'
      (e.trans (RankThree.Chevalley.adjointQuotientEquiv _ K))
      (adjointGroup_involution_centralizer_oddCore hE6 (.inr (.inl rfl)) hf K hK) hz2
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hcase
    exact oddCore_centralizer_eq_bot_of_conjModel hnonab'
      (e.trans (RankThree.Chevalley.adjointQuotientEquiv _ K))
      (adjointGroup_involution_centralizer_oddCore hE6 (.inr (.inr (.inl rfl))) hf K hK) hz2
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hcase
    exact oddCore_centralizer_eq_bot_of_conjModel hnonab'
      (e.trans (RankThree.Chevalley.adjointQuotientEquiv _ K))
      (adjointGroup_involution_centralizer_oddCore hE6 (.inr (.inr (.inr rfl))) hf K hK) hz2
  all_goals
    obtain ⟨K, _, _, hK, σ, hσ, ⟨e⟩⟩ := hcase
    obtain ⟨σ', rfl⟩ : ∃ σ' : K ≃+* K, σ'.toRingHom = σ :=
      ⟨RingEquiv.ofBijective σ ⟨σ.injective, Finite.surjective_of_injective σ.injective⟩,
        RingHom.ext fun _ => rfl⟩
    obtain ⟨e'⟩ := RankThree.Chevalley.nonempty_derivedCentralQuotient_equiv _ Nat.prime_two hf K
      hK _ hσ
    exact oddCore_centralizer_eq_bot_of_conjModel hnonab' (e.trans e')
      (graphFixedRootGroup_involution_centralizer_oddCore hE6 _ hf K hK σ' hσ) hz2

end CFSG.ComponentClassification.CatalogueU
