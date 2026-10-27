module

public import CFSG.GH74.GLS.Stage1.Main.Closed
public import CFSG.LieType.Chevalley.ExceptionalG2F4ModelSchreier
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.GH74.GLS
  CFSG.Assembly.LowTwoRank

namespace CFSG.GH74.GLS.Stage1.Main

theorem isElementaryAbelian_of_mulEquiv_rankG2 {p : ℕ} {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : IsElementaryAbelian p A) : IsElementaryAbelian p B :=
  CFSG.IsElementaryAbelian.of_mulEquiv e h

theorem rankG2_of_elemTwo
    (h : ∀ (K : Type) [Field K] [Finite K], Odd (Nat.card K) → ∀ (R : Subgroup (ModGL .G2 K)), R ≤
        adjointGroup .G2 K → ∀ [Finite R] [IsElementaryAbelian 2 R], Nat.card R ≤ 8) : RankG2 := by
  intro G _ _ z S hT
  obtain ⟨p, f, hp, hp2, ⟨Gs, iGs, fGs, hL, S', hS'⟩, -, -⟩ := hT
  have hm : ChevalleyExceptionalModel Gs .G2 p f := by
    rcases hL with ⟨ht, -⟩ | ⟨-, -, hm⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
    · exact absurd ht (by decide)
    · exact hm
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
  obtain ⟨K, _, _, hcard, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .G2 hm.2
  obtain ⟨eS⟩ := hS'
  have hodd : Odd (Nat.card K) := by
    rw [hcard]; exact (hp.odd_of_ne_two hp2).pow
  let φ : ↥S →* ModGL .G2 K :=
    ((adjointGroup .G2 K).subtype.comp e.toMonoidHom).comp
      ((S' : Subgroup Gs).subtype.comp eS.toMonoidHom)
  have hφ : Function.Injective φ := by
    intro a b hab
    have h1 : e ((eS a : ↥(S' : Subgroup Gs)) : Gs) = e ((eS b : ↥(S' : Subgroup Gs)) : Gs) :=
      Subtype.ext hab
    exact eS.injective (Subtype.ext (e.injective h1))
  unfold CFSG.pRank
  apply csSup_le'
  rintro r ⟨A, hA, hcardA⟩
  have hR : A.map φ ≤ adjointGroup .G2 K := by
    rintro _ ⟨a, -, rfl⟩
    exact (e ((eS a : ↥(S' : Subgroup Gs)) : Gs)).2
  have eA : ↥A ≃* ↥(A.map φ) := A.equivMapOfInjective φ hφ
  have : Finite ↥(A.map φ) := Finite.of_equiv A eA.toEquiv
  have : IsElementaryAbelian 2 ↥(A.map φ) := isElementaryAbelian_of_mulEquiv_rankG2 eA hA
  have h8 := h K hodd (A.map φ) hR
  have hc : Nat.card ↥(A.map φ) = 2 ^ r := by
    rw [← Nat.card_congr eA.toEquiv, hcardA]
  rw [hc] at h8
  by_contra hr
  have : 2 ^ 4 ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

end CFSG.GH74.GLS.Stage1.Main
