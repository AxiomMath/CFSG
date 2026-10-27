module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixToNineStmt
import CFSG.LieType.PSp43Local.Transport

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

private theorem card_pow_three_not_comm_of_isThreeOnePlusTwo {D : Subgroup G}
    (hD : IsThreeOnePlusTwo ↥D) :
    Nat.card D = 27 ∧ (∀ x ∈ D, x ^ 3 = 1) ∧ ¬ IsMulCommutative D := by
  obtain ⟨⟨-, -, -, hZ⟩, h27, h3⟩ := hD
  refine ⟨h27, fun x hx => by simpa using congrArg Subtype.val (h3 ⟨x, hx⟩), fun hc => ?_⟩
  have htop : center ↥D = ⊤ :=
    eq_top_iff.mpr fun g _ => mem_center_iff.mpr fun h => hc.is_comm.comm h g
  rw [htop, card_top, h27] at hZ
  omega

theorem not_inf_normalizer_le_of_isThreeOnePlusTwo {K Q D M : Subgroup G}
    (hK : CFSG.Blueprint.LieModel (modTwoCore K) .PSp 2 3 1)
    (hQ : CFSG.ABGLocalTools.IsSylowOf 3 Q K) (hDQ : D ≤ Q) (hD : IsThreeOnePlusTwo ↥D)
    (hKM : K ⊓ M ≤ (K ⊓ normalizer (thompsonSubgroup Q : Set G)) ⊔ pCoreOf 2 K) :
    ¬ K ⊓ normalizer (D : Set G) ≤ M := by
  obtain ⟨h27, h3, hnc⟩ := card_pow_three_not_comm_of_isThreeOnePlusTwo hD
  exact CFSG.LieType.PSp43Local.not_inf_normalizer_le_of_quotient_pCore_two hK hQ hDQ h27 h3 hnc
    hKM

theorem thompsonSubgroup_sup_map_conj_eq_of_isThreeOnePlusTwo {K Q D B : Subgroup G} {x : G}
    (hK : CFSG.Blueprint.LieModel (modTwoCore K) .PSp 2 3 1)
    (hQ : CFSG.ABGLocalTools.IsSylowOf 3 Q K) (hDQ : D ≤ Q) (hD : IsThreeOnePlusTwo ↥D)
    (hB : B ≤ thompsonSubgroup Q ⊓ D) (hBZ : ¬ B ≤ CFSG.centerIn D)
    (hx : x ∈ K ⊓ normalizer (D : Set G))
    (hxA : x ∉ (K ⊓ normalizer (thompsonSubgroup Q : Set G)) ⊔ pCoreOf 2 K) :
    thompsonSubgroup Q ⊔ B.map (MulAut.conj x).toMonoidHom = Q := by
  obtain ⟨h27, h3, hnc⟩ := card_pow_three_not_comm_of_isThreeOnePlusTwo hD
  exact CFSG.LieType.PSp43Local.thompsonSubgroup_sup_map_conj_eq_of_quotient_pCore_two hK hQ
    hDQ h27 h3 hnc hB hBZ hx hxA

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12
