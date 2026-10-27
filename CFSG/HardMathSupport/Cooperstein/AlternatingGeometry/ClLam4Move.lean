module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.ClLam4
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.ClTwo

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open Equiv Equiv.Perm MulAction CFSG.AGLEmbedding CFSG.Open CFSG.Quasithin CFSG.RankThree.PartTwo
  CFSG.QuasithinUnique


open scoped Classical in
@[expose] def EightTenNodeColourFourLam4SmallMove : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X S L : Subgroup G), CFSG.Open.IsKGroup ↥X →
    Asc81bHyp X S → IsWeakSBlock X S L → ∀ m : ℕ, 8 < m →
    ↥(barM (L ⊔ S) L) ⧸ Subgroup.center ↥(barM (L ⊔ S) L) ≃* alternatingGroup (Fin m) →
    NaturalSectionLSL S L m →
    ∀ θ : ↥(L ⊔ S) →* Perm (Fin m), NaturalSectionTheta S L m θ →
    (∀ m' : ↥(L ⊔ S), θ m' = 1 → (m' : G) ∈ S) →
    ∀ (A : Subgroup G) (σ : Perm (Fin m)) (c : Fin m → Bool), IsMaxElemAbelian S A →
      BlockData ((A.subgroupOf (L ⊔ S)).map θ) σ c → ∀ x, (cls c x).card = 4 →
      (∃ z : Fin m, ∀ y, z ≠ y →
        swap z y ∉ (((thompsonJ S).subgroupOf (L ⊔ S)).map θ : Subgroup (Perm (Fin m)))) →
      (Nat.card {x : Fin m // ∃ y, x < y ∧
          IsIsoPair (((thompsonJ S).subgroupOf (L ⊔ S)).map θ) x y} = 3 ∨
        5 ≤ Nat.card {x : Fin m // ∃ y, x < y ∧
          IsIsoPair (((thompsonJ S).subgroupOf (L ⊔ S)).map θ) x y}) →
      (∀ y : Fin m, (∀ z, y ≠ z →
          swap y z ∉ (((thompsonJ S).subgroupOf (L ⊔ S)).map θ : Subgroup (Perm (Fin m)))) ↔
        c y = true) →
      (Finset.univ.filter fun y : Fin m => c y = true).card = 4 →
      (∀ p q : Fin m, IsIsoPair (((thompsonJ S).subgroupOf (L ⊔ S)).map θ) p q →
        ∀ s : ↥(L ⊔ S), (s : G) ∈ S → θ s p = p ∨ θ s p = q) →
      (∀ z y : Fin m, c z = true → c y = true → y ≠ z → y ≠ σ z →
        swap z y * swap (σ z) (σ y) ∉ (S.subgroupOf (L ⊔ S)).map θ) →
      (∃ s : Perm (Fin m), s ∈ (S.subgroupOf (L ⊔ S)).map θ ∧ ∃ y, s y ≠ y ∧ s y ≠ σ y) →
      EightTenOutcomes X S L

theorem eightTenNodeColourFourLam4Small_of_move (hMove : EightTenNodeColourFourLam4SmallMove) :
    EightTenNodeColourFourLam4Small := by
  intro G _ _ X S L hX hA hL m hm e hN θ hNS hθS A σ c hAm hbd x hx hunm hcnt hiff' hT hfix hnoD
  classical
  by_cases hSF : ∀ s ∈ (S.subgroupOf (L ⊔ S)).map θ, ∀ y, s y = y ∨ s y = σ y
  swap
  · push Not at hSF
    obtain ⟨s, hs, y, hy1, hy2⟩ := hSF
    exact hMove G X S L hX hA hL m hm e hN θ hNS hθS A σ c hAm hbd x hx hunm hcnt hiff' hT hfix hnoD
      ⟨s, hs, y, hy1, hy2⟩
  exact eightTenOutcomes_of_blockFix hX hA hL hm e hN hNS hAm hbd hiff' hSF (by omega)

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
