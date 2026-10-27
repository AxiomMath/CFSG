module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BDefs
public import CFSG.RankThree.PartOne.SPOR.OuterM
public import CFSG.YGroups.Y443.Tri.Finiteness
public import CFSG.Sporadic.Bridge.MonsterModels
public import CFSG.Sporadic.Presentation.Fi24PrimeExact
public import CFSG.Sporadic.Presentation.HN

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H301B

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA

section Monster


private theorem monsterOrder_le_card (hf : Finite TauCeti.SporadicName.M.Group) :
    monsterOrder ≤ Nat.card TauCeti.SporadicName.M.Group := by
  obtain ⟨b⟩ := CFSG.Blueprint.NativeSporadic.MonsterModel.iso_y443Derived_tauCeti
  have c : MonsterY443Derived ≃* TauCeti.SporadicName.M.Group :=
    CFSG.Blueprint.NativeSporadic.MonsterModel.y443DerivedEquivOpen.symm.trans b
  haveI : Finite MonsterY443Derived := @Finite.of_equiv _ _ hf c.symm.toEquiv
  have h := Nat.card_le_card_of_surjective _ CFSG.RankThree.PartOne.SPOR.fM_surjective
  rw [CFSG.YGroups.Y443.natCard_Gmat_eq_monsterOrder] at h
  exact h.trans (Nat.card_congr c.toEquiv).le

section M3


theorem distM3_holds : I301BDistinct .m3 := by
  intro H _ hS hI
  obtain ⟨i, hi, ⟨e1⟩⟩ := hS
  obtain ⟨j, hj, ⟨e2⟩⟩ := hI
  simp only [S8.Row.name, S8.Row.Iq, S8.sporIs] at hi hj
  subst hi hj
  obtain ⟨hfin, hle⟩ := CFSG.Sporadic.Presentation.Fi24Prime.finite_card_le_exact
  have e : TauCeti.SporadicName.Fi24Prime.Group ≃* TauCeti.SporadicName.M.Group :=
    e2.symm.trans e1
  have h := (monsterOrder_le_card (@Finite.of_equiv _ _ hfin e.toEquiv)).trans
    ((Nat.card_congr e.toEquiv).symm.trans_le hle)
  norm_num [monsterOrder] at h

end M3

section M5


theorem distM5_holds : I301BDistinct .m5 := by
  intro H _ hS hI
  obtain ⟨i, hi, ⟨e1⟩⟩ := hS
  obtain ⟨j, hj, ⟨e2⟩⟩ := hI
  simp only [S8.Row.name, S8.Row.Iq, S8.sporIs] at hi hj
  subst hi hj
  obtain ⟨hfin, hle⟩ := CFSG.Sporadic.Presentation.HN.finite_card_le
  have e : TauCeti.SporadicName.HN.Group ≃* TauCeti.SporadicName.M.Group := e2.symm.trans e1
  have h := (monsterOrder_le_card (@Finite.of_equiv _ _ hfin e.toEquiv)).trans
    ((Nat.card_congr e.toEquiv).symm.trans_le hle)
  norm_num [monsterOrder] at h

end M5

end Monster

end CFSG.LocalAnalysis.GLTheoremA.H301B

end
