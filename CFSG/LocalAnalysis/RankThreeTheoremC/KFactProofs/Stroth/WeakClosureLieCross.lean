module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieDefChar
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieTorus

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.Blueprint

@[expose] def CrossCharLines (t : StatedLieTag) : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    ∀ (n ℓ f : ℕ), StatedLieAdmissible t n ℓ f → LieModel K t n ℓ f →
      ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ ℓ → ∀ P : Sylow p K,
        IsMulCommutative (P : Subgroup K) → 2 ≤ CFSG.Open.pRank p (P : Subgroup K) →
          NormalizerMovesLines p (P : Subgroup K)

theorem wcLie_of_crossChar
    (h : ∀ t : StatedLieTag, CrossCharLines t) : WCLie := by
  intro K _ _ hs hnab t n ℓ f hadm hmodel p hp hp2
  by_cases hpℓ : p = ℓ
  · exact wcLie_defChar hadm hmodel hp hp2 hpℓ
  · haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨P₀⟩ : Nonempty (Sylow p K) := inferInstance
    exact WCOn.of_normalizerMovesLines P₀ fun hab hrank =>
      h t K hs hnab n ℓ f hadm hmodel p hp hp2 hpℓ P₀ hab hrank

@[expose] def WCLieCrossAt (t : StatedLieTag) : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    ∀ (n ℓ f : ℕ), StatedLieAdmissible t n ℓ f → LieModel K t n ℓ f →
      ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ ℓ → WCOn p K

@[expose] def WCLieCross : Prop := ∀ t : StatedLieTag, WCLieCrossAt t

theorem crossCharLines_iff (t : StatedLieTag) : CrossCharLines t ↔ WCLieCrossAt t := by
  constructor
  · intro h K _ _ hs hnab n ℓ f hadm hmodel p hp hp2 hpℓ
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨P₀⟩ : Nonempty (Sylow p K) := inferInstance
    exact WCOn.of_normalizerMovesLines P₀ fun hab hrank =>
      h K hs hnab n ℓ f hadm hmodel p hp hp2 hpℓ P₀ hab hrank
  · intro h K _ _ hs hnab n ℓ f hadm hmodel p hp hp2 hpℓ P hab hrank
    haveI : Fact p.Prime := ⟨hp⟩
    exact normalizerMovesLines_of_wcOn (h K hs hnab n ℓ f hadm hmodel p hp hp2 hpℓ) P hab hrank

theorem crossCharResidue_iff : (∀ t : StatedLieTag, CrossCharLines t) ↔ WCLieCross :=
  forall_congr' crossCharLines_iff

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure
