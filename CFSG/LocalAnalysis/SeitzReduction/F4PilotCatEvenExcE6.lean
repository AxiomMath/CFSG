module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEvenE6

public section

namespace CFSG.SeitzReduction.F4Pilot.EvenExc

open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.Assembly.LowTwoRank CFSG.ComponentClassification CFSG.ComponentClassification.CatLeaf
  CFSG.ComponentClassification.CatLeafProof
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.LieType.Chevalley.E6SecondGraphFixed
open CFSG.LieType.Chevalley.EvenE6AllInvolution (mem_inner_of_conj_mul_rootDiagAut)

theorem even_E6_outer_lieModel_exact
    {k : Type} [Field k] [Finite k] {f : ℕ} (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (β : MulAut (adjointGroup TwistTag.E6.tag k)) (hβ2 : β ^ 2 = 1)
    (hβo : β ∉ inner (adjointGroup TwistTag.E6.tag k)) {X : Type} [Group X] [Finite X]
    (Ψ : X ≃* fixedSubgroup β) {P : Subgroup X} (hP : IsPComponent 2 P) :
    LieModel (P ⧸ Open.fusionZStar P) .F4 0 2 f ∨
      ∃ e : ℕ, f = 2 * e ∧ 1 ≤ e ∧ (LieModel (P ⧸ Open.fusionZStar P) .E6 0 2 e ∨
        LieModel (P ⧸ Open.fusionZStar P) .twistedE6 0 2 e) := by
  have : CharP k 2 :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hf hk
  have : Finite (ModGL TwistTag.E6.tag k) := finite_modGL
  obtain ⟨-, -, hexist⟩ :=
    ordinary_E_exact_automorphism_normal_form TwistTag.E6.tag (Or.inl rfl) k
  obtain ⟨g, a, σ, ε, hexpr⟩ := hexist β
  by_cases hσ : σ = 1
  · subst hσ
    have hid : ∀ h : ModGL TwistTag.E6.tag k,
        Units.map (entrywiseHom (1 : k ≃+* k).toRingHom) h = h := fun h =>
      Units.ext (entrywise_id _)
    obtain ⟨ε, hε⟩ := ε
    have hε' : ε = 0 ∨ ε = 1 := by
      change ε < 2 at hε
      omega
    rcases hε' with rfl | rfl
    ·
      exfalso
      refine hβo (mem_inner_of_conj_mul_rootDiagAut hk hf g a ?_ hβ2)
      refine MulEquiv.ext fun h => Subtype.ext ?_
      have e := hexpr h
      have hQ0 : exactQ TwistTag.E6.tag k ((⟨0, hε⟩ : Fin (exactE TwistTag.E6.tag)) : ℕ) = 1 :=
        pow_zero _
      rw [hQ0, hid, mul_one, inv_one, mul_one] at e
      rw [e, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
        coe_rootDiagAut, Subgroup.coe_inv]
      simp only [mul_assoc]
    ·
      have hQ1 : exactQ TwistTag.E6.tag k ((⟨1, hε⟩ : Fin (exactE TwistTag.E6.tag)) : ℕ) =
          diagramMap TwistTag.E6 k := pow_one _
      set M := GaloisField 2 (2 * f)
      have hM : Nat.card M = (2 ^ f) ^ 2 := by
        rw [GaloisField.card 2 (2 * f) (by omega), ← pow_mul, mul_comm]
      obtain ⟨ι⟩ := E6GraphFullCoset.nonempty_ringHom_of_card hf hk hM
      let _ : Algebra k M := ι.toAlgebra
      have hσM : ∀ c : M, iterateFrobenius M 2 f c = c ^ 2 ^ f := fun c =>
        iterateFrobenius_def (p := 2) f c
      obtain ⟨ht, η, hη, hclass, -⟩ :=
        (even_E6_graph_full_inner_diagonal_coset_exhaustion f hf).1 k hk
      obtain ⟨⟨hcan, -, -⟩, -⟩ :=
        even_E6_twisted_E6_canonical_graph_fixed_subgroup f hf k M hk hM _ hσM
      obtain ⟨-, -, -, -, ⟨e, -, -, hsec⟩, -⟩ :=
        even_E6_twisted_E6_second_graph_fixed_subgroup f hf k M hk hM _ hσM
      have hgraph : E6GraphFullCoset.IsOrdinaryDiagGraph k β := ⟨g, a, g.2, fun h => by
        have e := hexpr h
        rw [hQ1, hid] at e
        refine e.trans ?_
        group⟩
      exact Or.inl (even_graph_lieModel hf hk hcan e hsec hη
        ((hclass β hgraph hβ2).imp id fun ⟨φ, hφ⟩ => ⟨ht, φ, hφ⟩) Ψ hP).2
  ·
    obtain ⟨-, -, -, -, hsq, hfacts⟩ :=
      ordinary_E_field_graph_quotient_and_involutions Tag.E6 (Or.inl rfl) k
    have hσ2 : σ ^ 2 = 1 := hsq β g a σ ε hexpr hβ2
    obtain ⟨hfe, hσc, -⟩ := hfacts 2 f Nat.prime_two hf hk σ hσ2 hσ
    obtain ⟨e, rfl⟩ : ∃ e, f = 2 * e := ⟨f / 2, (Nat.two_mul_div_two_of_even hfe).symm⟩
    have he : 1 ≤ e := by omega
    have hσe : ∀ c, σ c = c ^ 2 ^ e := fun c => by
      rw [hσc, Nat.mul_div_cancel_left e two_pos]
    have hββ : β * β = 1 := by rw [← sq]; exact hβ2
    obtain ⟨hD0, hD1⟩ :=
      even_exceptional_quadratic_field_graph_field_involution_descent he k hk σ.toRingHom hσe
    obtain ⟨hJ0, hJ1⟩ := even_E6_canonical_field_graph_field_derived_fixed_subgroups he k hk σ hσe
    obtain ⟨ε, hε⟩ := ε
    have hε' : ε = 0 ∨ ε = 1 := by
      change ε < 2 at hε
      omega
    rcases hε' with rfl | rfl
    ·
      have hQ0 : exactQ TwistTag.E6.tag k ((⟨0, hε⟩ : Fin (exactE TwistTag.E6.tag)) : ℕ) = 1 :=
        pow_zero _
      obtain ⟨β', hβ', hβα⟩ := hD0 TwistTag.E6.tag
      obtain ⟨ψ, -, hψ, -⟩ := (hβα g a).2 β (fun u => by
        have h := hexpr u
        rw [hQ0, mul_one, inv_one, mul_one] at h
        exact h) hββ
      obtain ⟨-, hJC, hder, -, -, -⟩ := hJ0
      have hβδ : diagramConjAut TwistTag.E6 k ^ 0 * entrywiseAdjointAut TwistTag.E6.tag σ = β' :=
        MulEquiv.ext fun u => Subtype.ext ((coe_entrywiseAdjointAut _ σ u).trans (hβ' u).symm)
      rw [← hβδ] at hψ
      have hk' := ExcSelector.card_fixSubfield_of_pow he hk hσe
      have : IsSimpleGroup ↥(adjointGroup TwistTag.E6.tag (fixSubfield σ)) :=
        (ExcSelector.adjointGroup_E6_even he hk').1
      obtain ⟨E⟩ := nonempty_fusionZStar_equiv_of_derived
        ((Ψ.trans ((fixedSubgroup β).equivMapOfInjective ψ.toMonoidHom ψ.injective)).trans
          (MulEquiv.subgroupCongr hψ))
        ((MulEquiv.subgroupCongr hder).trans
          ((Subgroup.subgroupOfEquivOfLe hJC).trans (fixedFieldImageEquiv σ).symm)) hP
      exact Or.inr ⟨e, rfl, he, Or.inl (lieModel_E6_of_mulEquiv he hk' E).2⟩
    ·
      have hQ1 : exactQ TwistTag.E6.tag k ((⟨1, hε⟩ : Fin (exactE TwistTag.E6.tag)) : ℕ) =
          diagramMap TwistTag.E6 k := pow_one _
      obtain ⟨β', hβ', hβα⟩ := hD1
      obtain ⟨ψ, -, hψ, -⟩ := (hβα g a).2 β (fun u => by
        have h := hexpr u
        rw [hQ1] at h
        exact h) hββ
      obtain ⟨-, hJC, hder, -, hsimp, -⟩ := hJ1
      have hβγδ : diagramConjAut TwistTag.E6 k ^ 1 * entrywiseAdjointAut TwistTag.E6.tag σ = β' :=
        MulEquiv.ext fun u => Subtype.ext (((coe_diagramConjAut TwistTag.E6 k
          (entrywiseAdjointAut TwistTag.E6.tag σ u)).trans
            (by rw [coe_entrywiseAdjointAut])).trans (hβ' u).symm)
      rw [← hβγδ] at hψ
      have hk' : Nat.card k = (2 ^ e) ^ 2 := by rw [hk, ← pow_mul, mul_comm]
      obtain ⟨E⟩ := nonempty_fusionZStar_equiv_of_derived
        ((Ψ.trans ((fixedSubgroup β).equivMapOfInjective ψ.toMonoidHom ψ.injective)).trans
          (MulEquiv.subgroupCongr hψ))
        ((MulEquiv.subgroupCongr hder).trans (Subgroup.subgroupOfEquivOfLe hJC)) hP
      exact Or.inr ⟨e, rfl, he, Or.inr (lieModel_twistedE6_of_mulEquiv he hk' σ hσe E).2⟩

end CFSG.SeitzReduction.F4Pilot.EvenExc
