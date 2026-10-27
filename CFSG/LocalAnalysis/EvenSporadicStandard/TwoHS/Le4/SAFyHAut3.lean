module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFyHAut2
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG.EvenSporadicStandard.TwoHS

namespace SAFyHAut

noncomputable def mulAutAlternatingFiveEquivPerm :
    MulAut (alternatingGroup (Fin 5)) ≃* Equiv.Perm (Fin 5) :=
  (MulEquiv.ofBijective
    (MulAut.conjNormal : Equiv.Perm (Fin 5) →* MulAut (alternatingGroup (Fin 5)))
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5 le_rfl (by decide))).symm

end SAFyHAut

theorem mulAut_A5A5_equiv_wreath :
    Nonempty (MulAut (alternatingGroup (Fin 5) × alternatingGroup (Fin 5)) ≃*
      RegularWreathProduct (Equiv.Perm (Fin 5)) (Multiplicative (ZMod 2))) := by
  have : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  exact ⟨(SAFyHAut.mulAutProdEquivWreath (alternatingGroup.center_eq_bot (by simp))).trans
    (RegularWreathProduct.congr SAFyHAut.mulAutAlternatingFiveEquivPerm (MulEquiv.refl _))⟩

theorem card_mulAut_A5A5 :
    Nat.card (MulAut (alternatingGroup (Fin 5) × alternatingGroup (Fin 5))) = 28800 := by
  obtain ⟨e⟩ := mulAut_A5A5_equiv_wreath
  have h1 : Nat.card (Equiv.Perm (Fin 5)) = 120 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm]
    simp [Nat.factorial]
  have h2 : Nat.card (Multiplicative (ZMod 2)) = 2 := by
    rw [Nat.card_eq_fintype_card]
    decide
  rw [Nat.card_congr e.toEquiv, RegularWreathProduct.card, h1, h2]
  norm_num

end CFSG.EvenSporadicStandard.TwoHS
