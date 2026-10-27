module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1SporLie
public import CFSG.LocalAnalysis.OddStandard.SporadicRow.ThreeDvd
public import CFSG.LocalAnalysis.OddStandard.SporadicRow.SixtyOrder

public section

namespace CFSG.ComponentClassification.HarrisLit.T1.SporRow

open CFSG Subgroup Assembly.LowTwoRank CatLeaf

@[expose] def SporOddComps (s : TauCeti.SporadicName) : Prop :=
  ∀ (S : Type) [Group S] [Finite S] [IsSimpleGroup S], (∃ a b : S, a * b ≠ b * a) →
    (S ≃* Blueprint.NativeSporadic.Carrier s) → ∀ t : S, orderOf t = 2 →
    ∀ B : Subgroup ↥(centralizer ({t} : Set S)), IsComponent B → selfCent t ∈ B →
      ¬ OddLieOrder (Nat.card (↥B ⧸ center ↥B))

theorem not_oddLieOrder_card_quotient_center_of_not_three_dvd {B : Type*} [Group B] [Finite B]
    (h : ¬ 3 ∣ Nat.card B) : ¬ OddLieOrder (Nat.card (B ⧸ center B)) := fun hi =>
  h (hi.three_dvd.trans (Subgroup.card_quotient_dvd_card _))

theorem not_oddLieOrder_card_quotient_center_of_card_dvd {B : Type*} [Group B] [Finite B] {a : ℕ}
    (h : Nat.card B ∣ 2 ^ a * 3) : ¬ OddLieOrder (Nat.card (B ⧸ center B)) :=
  not_oddLieOrder_of_dvd_two_pow_mul_three ((Subgroup.card_quotient_dvd_card _).trans h)

theorem not_oddLieOrder_card_quotient_fusionZStar {S : Type} [Group S] [Finite S] {t : S}
    (hO : pPrimeCore 2 ↥(centralizer ({t} : Set S)) = ⊥) {L : Subgroup S}
    (hL : IsTwoComponentIn L (centralizer {t})) (htL : t ∈ L)
    (hcomp : ∀ B : Subgroup ↥(centralizer ({t} : Set S)), IsComponent B → selfCent t ∈ B →
      ¬ OddLieOrder (Nat.card (↥B ⧸ center ↥B))) :
    ¬ OddLieOrder (Nat.card (↥L ⧸ Open.fusionZStar ↥L)) := by
  obtain ⟨hJC, hJs, hJq⟩ := hL
  set C := centralizer ({t} : Set S)
  set B := L.subgroupOf C
  let eB : ↥B ≃* ↥L := Subgroup.subgroupOfEquivOfLe hJC
  have hOB : pPrimeCore 2 ↥B = ⊥ := pPrimeCore_eq_bot_of_isSubnormal hO hJs
  have hOJ : pPrimeCore 2 ↥L = ⊥ := by
    rw [← pPrimeCore_map_iso 2 eB, hOB, Subgroup.map_bot]
  have hBq : IsTwoQuasisimple ↥B := isTwoQuasisimple_of_mulEquiv eB.symm hJq
  have hBq' : IsQuasisimple ↥B := LocalCores.isQuasisimple_of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq hOB).trans QuotientGroup.quotientBot) hBq.2
  have hB : IsComponent B := ⟨hBq', hJs⟩
  have htB : selfCent t ∈ B := mem_subgroupOf.2 htL
  have hcJ : Nat.card (↥L ⧸ Open.fusionZStar ↥L) = Nat.card (↥B ⧸ center ↥B) := by
    rw [card_quotient_fusionZStar_of_bot hOJ]
    exact (Nat.card_congr (QuotientGroup.congr _ _ eB (Subgroup.map_center_eq eB)).toEquiv).symm
  rw [hcJ]
  exact hcomp B hB htB

end CFSG.ComponentClassification.HarrisLit.T1.SporRow
