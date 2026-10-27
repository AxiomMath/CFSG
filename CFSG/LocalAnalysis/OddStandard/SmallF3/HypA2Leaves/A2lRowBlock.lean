module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lDescent

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open Subgroup CFSG.ComponentClassification
open CFSG.OddStandard.SmallF3.HypA2 (TypU coreInvariant_typU)

theorem a2lDatum_of_block_normal {P S : Type} [Group P] [Finite P] [Group S] (π : P →* S)
    (hπ : Function.Surjective π) (hker : π.ker ≤ center P) {q₀ : ℕ} (hodd : Odd q₀)
    (h5 : 5 ≤ q₀) {t : P} (ht : t * t = 1) (ht1 : π t ≠ 1) {J N : Subgroup P} (hNJ : N ≤ J)
    (htN : t ∈ N) (hJc : J ≤ centralizer ({t} : Set P))
    (hJn : ∀ g ∈ centralizer ({t} : Set P), ∀ x ∈ J, g * x * g⁻¹ ∈ J)
    (hJq : CFSG.IsQuasisimple ↥J) (hinj : ∀ x ∈ J, π x = 1 → x = 1)
    (hN : HarrisLit.IsSLTwoOver q₀ ↥N) (hTU : TypU ↥J) : a2lDatum S :=
  a2lDatum_of_block π hπ hker hodd h5 ht ht1 hNJ htN hJc
    (CFSG.Assembly.IsSubnormal.step hJc ⟨fun x hx g => hJn g g.2 x hx⟩
      (CFSG.Assembly.IsSubnormal.refl _))
    hJq hinj hN hTU

theorem a2l_typU_of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B) (h : TypU A) :
    TypU B :=
  coreInvariant_typU A B ⟨QuotientGroup.congr _ _ e (CFSG.pPrimeCore_map_iso 2 e)⟩ h

theorem a2l_typU_of_isSLTwoOver {A : Type} [Group A] {q : ℕ} (hodd : Odd q) (h9 : 9 ≤ q)
    (h : HarrisLit.IsSLTwoOver q A) : TypU A :=
  Or.inl ⟨q, hodd, h9, a2l_isSLTwoOver_quotient hodd (by omega) h⟩

end CFSG.OddStandard.SmallF3.HypA2Leaves
