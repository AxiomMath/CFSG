module

public import CFSG.LocalAnalysis.ComponentClassification.Sp4RecSmall
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorOddE6
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorOddTriality

public noncomputable section

namespace CFSG.ComponentClassification.Sp4Rec

open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.Assembly.LowTwoRank
  CFSG.LieType.AlgebraicGroups
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

namespace Config

variable {H : Type} [Group H] [Finite H] (c : Sp4Rec.Config H)

include c in
theorem false_of_fixed {M : Type} [Group M] [Finite M] (θ : ↥(generalizedFitting H) ≃* M)
    (hQ : ∀ α : MulAut M, α ^ 2 = 1 → ∀ L : Subgroup (fixedSubgroup α), IsPComponent 2 L →
      IsQuasisimple L)
    (hN : ∀ α : MulAut M, α ^ 2 = 1 → ∀ L : Subgroup M,
      Assembly.IsComponentOf L (fixedSubgroup α) → ¬ ExcSelector.SmallType L) : False := by
  obtain ⟨α, hα2, -, L, hLF, hLpc, ⟨eL⟩⟩ := c.exists_fixed_component θ
  have hq := hQ α hα2 _ hLpc
  obtain ⟨-, -, hs, -, -⟩ := id hLpc
  have hcomp : Assembly.IsComponentOf L (fixedSubgroup α) :=
    (LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hLF).mpr ⟨hq, hs⟩
  have hqL : IsQuasisimple L :=
    (LocalAnalysis.ComponentInitial.isQuasisimple_congr (subgroupOfEquivOfLe hLF)).1 hq
  have hsm : GSThmB.IsSmallAltOrL2 (L ⧸ pPrimeCore 2 L) :=
    GSThmB.isSmallAltOrL2_of_mulEquiv
      (UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2 eL).symm c.type_J
  exact hN α hα2 L hcomp (smallType_of_isQuasisimple hqL hsm)

include c in
theorem false_of_exceptional {t : StatedLieTag} {p f : ℕ} (hp2 : p ≠ 2)
    (hG : ChevalleyExceptionalModel ↥(generalizedFitting H) t p f) : False := by
  obtain ⟨⟨hp, hf, -⟩, hm⟩ := hG
  have hodd : Odd (p ^ f) := (hp.eq_two_or_odd'.resolve_left hp2).pow
  cases t
  case G2 =>
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .G2 hm
    rw [← hK] at hodd
    exact c.false_of_fixed e
      (fun α hα L hL => odd_G2_F4_E8_all_involution_fixed_p_components .G2 (Or.inl rfl) K hodd
        α hα 2 Nat.prime_two L hL)
      (fun α hα L hL => ExcSelector.odd_GFE_not_smallType (Or.inl rfl) hodd α hα hL)
  case F4 =>
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .F4 hm
    rw [← hK] at hodd
    exact c.false_of_fixed e
      (fun α hα L hL => odd_G2_F4_E8_all_involution_fixed_p_components .F4
        (Or.inr (Or.inl rfl)) K hodd α hα 2 Nat.prime_two L hL)
      (fun α hα L hL => ExcSelector.odd_GFE_not_smallType (Or.inr (Or.inl rfl)) hodd α hα hL)
  case E6 =>
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .E6 hm
    rw [← hK] at hodd
    exact c.false_of_fixed e
      (fun α hα L hL => odd_E6_all_involution_fixed_p_components K hodd α hα 2 Nat.prime_two L hL)
      (fun α hα L hL => ExcSelector.odd_E6_not_smallType hodd α hα hL)
  case E7 =>
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .E7 hm
    rw [← hK] at hodd
    exact c.false_of_fixed e
      (fun α hα L hL => odd_E7_all_involution_fixed_p_components K hodd α hα 2 Nat.prime_two L hL)
      (fun α hα L hL => ExcSelector.odd_E7_not_smallType hodd α hα hL)
  case E8 =>
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .E8 hm
    rw [← hK] at hodd
    exact c.false_of_fixed e
      (fun α hα L hL => odd_G2_F4_E8_all_involution_fixed_p_components .E8
        (Or.inr (Or.inr rfl)) K hodd α hα 2 Nat.prime_two L hL)
      (fun α hα L hL => ExcSelector.odd_GFE_not_smallType (Or.inr (Or.inr rfl)) hodd α hα hL)
  case twistedE6 =>
    obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ := exists_mulEquiv_graphFixedRootGroup_card .E6 hp hf hm
    exact c.false_of_fixed e
      (fun α hα L hL => odd_twisted_E6_all_involution_fixed_p_components hp hf hodd K hK σ hσ α
        hα 2 Nat.prime_two L hL)
      (fun α hα L hL => ExcSelector.odd_twistedE6_not_smallType hp hp2 hf hK σ hσ α hα hL)
  case trialityD4 =>
    obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ := exists_mulEquiv_graphFixedRootGroup_card .D4 hp hf hm
    exact c.false_of_fixed e
      (fun α hα L hL => odd_triality_all_involution_fixed_p_components hp hp2 hf K hK σ hσ α hα 2
        Nat.prime_two L hL)
      (fun α hα L hL => ExcSelector.odd_triality_not_smallType hp hp2 hf hK σ hσ α hα hL)
  all_goals exact hm.elim

end Config

end CFSG.ComponentClassification.Sp4Rec
