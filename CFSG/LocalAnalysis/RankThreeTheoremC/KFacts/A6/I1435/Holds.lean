module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.A6.I1435.AltCase
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.A6.I1435.PSp43Case

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.A6

open Subgroup CFSG.Open CFSG.GH74.Exceptional CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

@[expose] def KFact1435ChevTwo : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K : Subgroup X) (P : Sylow 3 X) (x : X),
    K.Normal → IsSimpleGroup ↥K → (∃ a b : ↥K, a * b ≠ b * a) →
    centralizer (K : Set X) = ⊥ →
    IsChevTwo ↥K → (¬ ∃ n : ℕ, Nonempty (↥K ≃* alternatingGroup (Fin n))) →
    Nonempty (↥(P : Subgroup X) ≃* (Multiplicative (ZMod 3) ≀ᵣ Multiplicative (ZMod 3))) →
    x ∈ CFSG.thompsonSubgroup (P : Subgroup X) → x ≠ 1 →
    conjLinesIn (CFSG.thompsonSubgroup (P : Subgroup X)) x = 3 →
    (∀ D : Subgroup X, D ≤ CFSG.thompsonSubgroup (P : Subgroup X) →
      (∀ g ∈ normalizer (CFSG.thompsonSubgroup (P : Subgroup X) : Set X), ∀ d ∈ D,
        g * d * g⁻¹ ∈ D) →
        D = ⊥ ∨ D = CFSG.thompsonSubgroup (P : Subgroup X)) →
    (∀ S : Subgroup X,
      CFSG.ABGLocalTools.IsSylowOf 2 S
        (normalizer (CFSG.thompsonSubgroup (P : Subgroup X) : Set X)) →
        ∃ a ∈ S, ∃ b ∈ S,
          a * b * a⁻¹ * b⁻¹ ∉ centralizer (CFSG.thompsonSubgroup (P : Subgroup X) : Set X)) →
    CFSG.HallHigman.IsPSolvable 3 ↥(centralizer ({x} : Set X)) →
    Nonempty (↥K ≃* PSp43)

theorem kFact1435_of_chevTwo (h : KFact1435ChevTwo) : KFact1435 := by
  intro X _ _ K P x hKn hKs hnab hCK hcat hPW hxJ hx1 hlines hd1 hd2 hsolv
  obtain ⟨e⟩ := hPW
  have e' : ↥(P : Subgroup X) ≃* I1435.W3 := e
  by_cases halt : ∃ n : ℕ, Nonempty (↥K ≃* alternatingGroup (Fin n))
  · obtain ⟨n, ⟨ψ⟩⟩ := halt
    exact (I1435.false_of_alternating hKn hnab e' ψ hxJ hx1 hlines hd1 hsolv).elim
  · obtain ⟨ψ⟩ := h X K P x hKn hKs hnab hCK (hcat.resolve_right halt) halt ⟨e⟩ hxJ hx1 hlines
      hd1 hd2 hsolv
    obtain ⟨hxK, hc⟩ := I1435.psp43_case hKn e' ψ hxJ hx1 hlines hd1
    exact ⟨hxK, ⟨ψ⟩, hc⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.A6
