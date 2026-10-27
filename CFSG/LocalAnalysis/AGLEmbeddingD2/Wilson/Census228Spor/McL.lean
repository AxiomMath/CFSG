module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census228Spor.Normalizer
public import CFSG.RankThree.PartTwo.Sec4.Item423Res3ProofMcL
public import CFSG.LargeExtraspecial.AS35WRCore

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Census228Spor

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec21 CFSG.Blueprint
open CFSG.Sporadic.Schreier (mclP)
open CFSG.RankThree.PartTwo.Sec6.ThreeLocalSporProof

theorem card_centralizer_five_mclP
    (u : mclP) (hu : orderOf u = 5) :
    Nat.card (Subgroup.centralizer ({u} : Set mclP)) = 750 ∨
      Nat.card (Subgroup.centralizer ({u} : Set mclP)) = 25 := by
  obtain ⟨hf₁, hf₂, -, -, c₁, c₂, -, -, -, hall⟩ :=
    CFSG.Sporadic.Recognition.McLAS.mclP_order_five_classes
      CFSG.Sporadic.Recognition.McLAS.fiveOuterCheck_eq_true
  have hu5 : orderOf (u : Equiv.Perm (Fin 275)) = 5 := by rw [Subgroup.orderOf_coe, hu]
  rcases hall u u.2 hu5 with ⟨g, hg, hug⟩ | ⟨g, hg, hug⟩
  · left
    rw [card_centralizer_of_isConj (isConj_of_eq_conj (t := ⟨_, hf₁⟩) hg hug),
      card_centralizer_singleton (⟨_, hf₁⟩ : mclP), c₁]
  · right
    rw [card_centralizer_of_isConj (isConj_of_eq_conj (t := ⟨_, hf₂⟩) hg hug),
      card_centralizer_singleton (⟨_, hf₂⟩ : mclP), c₂]

theorem threeFiveData228_of_equiv_McL
    {X : Type} [Group X] [Finite X] (e : X ≃* mclP) : ThreeFiveData228 X := by
  refine threeFiveData228_of_centralizer_cards (a := 29160) (m := 750) ?_ ?_ (by norm_num)
  · intro x hx
    have hx' : orderOf (e x) = 3 := by rw [MulEquiv.orderOf_eq]; exact hx
    rw [← CFSG.LargeExtraspecial.AS35W.card_centralizer_map e x]
    rcases Sec4.Res423Three.card_centralizer_mclP (e x) hx' with h | h
    · exact Or.inl h
    · right; rw [h]; norm_num
  · intro k hk
    have hk' : orderOf (e k) = 5 := by rw [MulEquiv.orderOf_eq]; exact hk
    rw [← CFSG.LargeExtraspecial.AS35W.card_centralizer_map e k]
    rcases card_centralizer_five_mclP (e k) hk' with h | h
    · rw [h]
    · rw [h]; norm_num

theorem threeFiveData228_McL :
    ThreeFiveData228 (NativeSporadic.Carrier .McL) := by
  have eM : NativeSporadic.Carrier .McL ≃* mclP := CFSG.Sporadic.Schreier.mclPermEquiv
  have : Finite (NativeSporadic.Carrier .McL) := Finite.of_equiv _ eM.symm.toEquiv
  exact threeFiveData228_of_equiv_McL eM

end CFSG.AGLEmbeddingD2.Wilson.Census228Spor
