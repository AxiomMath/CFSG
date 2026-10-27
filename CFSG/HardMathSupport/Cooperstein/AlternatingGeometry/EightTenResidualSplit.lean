module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.EightTenGivenNaturalOfResidual

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open Equiv Equiv.Perm MulAction CFSG.AGLEmbedding CFSG.Open CFSG.Quasithin
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.Offender

@[expose] def EightTenNodeSFour : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X S L : Subgroup G), CFSG.Open.IsKGroup ↥X →
    Asc81bHyp X S → IsWeakSBlock X S L → ∀ m : ℕ, 8 < m →
    ↥(barM (L ⊔ S) L) ⧸ Subgroup.center ↥(barM (L ⊔ S) L) ≃* alternatingGroup (Fin m) →
    NaturalSectionLSL S L m →
    ∀ θ : ↥(L ⊔ S) →* Perm (Fin m), NaturalSectionTheta S L m θ →
    (∀ m' : ↥(L ⊔ S), θ m' = 1 → (m' : G) ∈ S) →
    ∀ r : ℕ, 1 ≤ r → 2 * r + 4 = m → (r = 1 ∨ r = 3 ∨ 5 ≤ r) →
    ∀ e : Fin m ≃ OmegaE r 4,
      ((thompsonJ S).subgroupOf (L ⊔ S)).map (e.permCongrHom.toMonoidHom.comp θ) = Wr r 4 →
      EightTenOutcomes X S L

@[expose] def EightTenNodeFourOrbit : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X S L : Subgroup G), CFSG.Open.IsKGroup ↥X →
    Asc81bHyp X S → IsWeakSBlock X S L → ∀ m : ℕ, 8 < m →
    ↥(barM (L ⊔ S) L) ⧸ Subgroup.center ↥(barM (L ⊔ S) L) ≃* alternatingGroup (Fin m) →
    NaturalSectionLSL S L m →
    ∀ θ : ↥(L ⊔ S) →* Perm (Fin m), NaturalSectionTheta S L m θ →
    (∀ m' : ↥(L ⊔ S), θ m' = 1 → (m' : G) ∈ S) →
    ∀ A : Subgroup G, IsMaxElemAbelian S A → ∀ x : Fin m,
      Nat.card (orbit ((A.subgroupOf (L ⊔ S)).map θ) x) = 4 → EightTenOutcomes X S L

@[expose] def EightTenNodeColourFour : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X S L : Subgroup G), CFSG.Open.IsKGroup ↥X →
    Asc81bHyp X S → IsWeakSBlock X S L → ∀ m : ℕ, 8 < m →
    ↥(barM (L ⊔ S) L) ⧸ Subgroup.center ↥(barM (L ⊔ S) L) ≃* alternatingGroup (Fin m) →
    NaturalSectionLSL S L m →
    ∀ θ : ↥(L ⊔ S) →* Perm (Fin m), NaturalSectionTheta S L m θ →
    (∀ m' : ↥(L ⊔ S), θ m' = 1 → (m' : G) ∈ S) →
    ∀ (A : Subgroup G) (σ : Perm (Fin m)) (c : Fin m → Bool), IsMaxElemAbelian S A →
      BlockData ((A.subgroupOf (L ⊔ S)).map θ) σ c → ∀ x, (cls c x).card = 4 →
      EightTenOutcomes X S L

open scoped Classical in
@[expose] def EightTenNodeMatching : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X S L : Subgroup G), CFSG.Open.IsKGroup ↥X →
    Asc81bHyp X S → IsWeakSBlock X S L → ∀ m : ℕ, 8 < m →
    ↥(barM (L ⊔ S) L) ⧸ Subgroup.center ↥(barM (L ⊔ S) L) ≃* alternatingGroup (Fin m) →
    NaturalSectionLSL S L m →
    ∀ θ : ↥(L ⊔ S) →* Perm (Fin m), NaturalSectionTheta S L m θ →
    (∀ m' : ↥(L ⊔ S), θ m' = 1 → (m' : G) ∈ S) →
    ∀ σ : Perm (Fin m), ∀ (hσ1 : ∀ x, σ x ≠ x) (hσ2 : ∀ x, σ (σ x) = x),
      (((thompsonJ S).subgroupOf (L ⊔ S)).map θ : Subgroup (Perm (Fin m))) ≤
        pairPres σ hσ1 hσ2 →
      (∀ x y, y ≠ x → y ≠ σ x →
        swap x (σ x) ∉ (((thompsonJ S).subgroupOf (L ⊔ S)).map θ : Subgroup (Perm (Fin m))) →
        swap y (σ y) ∉ (((thompsonJ S).subgroupOf (L ⊔ S)).map θ : Subgroup (Perm (Fin m))) →
        swap x (σ x) * swap y (σ y) ∈
          (((thompsonJ S).subgroupOf (L ⊔ S)).map θ : Subgroup (Perm (Fin m)))) →
      (Finset.univ.filter fun x : Fin m => swap x (σ x) ∉
        (((thompsonJ S).subgroupOf (L ⊔ S)).map θ : Subgroup (Perm (Fin m)))).card ≠ 2 * 1 →
      ((Finset.univ.filter fun x : Fin m => swap x (σ x) ∉
        (((thompsonJ S).subgroupOf (L ⊔ S)).map θ : Subgroup (Perm (Fin m)))).card = 2 * 4 ∨
      (Finset.univ.filter fun x : Fin m => swap x (σ x) ∈
        (((thompsonJ S).subgroupOf (L ⊔ S)).map θ : Subgroup (Perm (Fin m)))).card = 2 * 4) →
      EightTenOutcomes X S L

theorem eightTenResidualOutcomes_of_nodes (h1 : EightTenNodeSFour) (h2 : EightTenNodeFourOrbit)
    (h3 : EightTenNodeColourFour) (h4 : EightTenNodeMatching) : EightTenResidualOutcomes := by
  intro G _ _ X S L hX hA hL m hm e hN hres
  obtain ⟨θ, hNS, hθS, h⟩ := hres
  rcases h with ⟨r, hr1, hrs, hgood, e4, he4⟩ | ⟨A, hA', x, hx⟩ | ⟨A, σ, c, hA', hbd, x, hx⟩ |
    ⟨σ, hσ1, hσ2, hle, hD, hN1, h8⟩
  · exact h1 G X S L hX hA hL m hm e hN θ hNS hθS r hr1 hrs hgood e4 he4
  · exact h2 G X S L hX hA hL m hm e hN θ hNS hθS A hA' x hx
  · exact h3 G X S L hX hA hL m hm e hN θ hNS hθS A σ c hA' hbd x hx
  · exact h4 G X S L hX hA hL m hm e hN θ hNS hθS σ hσ1 hσ2 hle hD hN1 h8

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
