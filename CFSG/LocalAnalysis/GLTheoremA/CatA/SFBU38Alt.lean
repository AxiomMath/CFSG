module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2018Facts
public import CFSG.LocalAnalysis.GLTheoremA.S10.CatSingle
public import CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridgeHolds

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I2018

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S10


theorem I2018U38NotAlt_holds : I2018U38NotAlt := by
  intro X _ _ hX m hm hiso
  obtain ⟨e⟩ := hiso
  have hcard : Nat.card X = 5515776 :=
    CFSG.LocalAnalysis.GLTheoremA.CatSingle.card_isU3eight
      CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds hX
  haveI : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.2 (by omega)
  have hA : Nat.card (alternatingGroup (Fin m)) = m.factorial / 2 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  rw [Nat.card_congr e.toEquiv, hA] at hcard
  rcases Nat.lt_or_ge m 11 with h | h
  · have h1 : m.factorial ≤ Nat.factorial 10 := Nat.factorial_le (by omega)
    have h2 : Nat.factorial 10 = 3628800 := by norm_num [Nat.factorial]
    omega
  · have h1 : Nat.factorial 11 ≤ m.factorial := Nat.factorial_le h
    have h2 : Nat.factorial 11 = 39916800 := by norm_num [Nat.factorial]
    omega

end CFSG.LocalAnalysis.GLTheoremA.I2018

end
