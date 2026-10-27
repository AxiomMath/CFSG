module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.R3SpModel
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutProp21
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutResidue

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup CFSG.Open CFSG.Blueprint CFSG.EvenSporadicStandard.M24Std
  CFSG.EvenSporadicStandard.M23Std

theorem fin77aOuterResidue₃_sp44 :
    Fin77aOuterSit fun X _ _ z => ¬ (LieModel (egaLayer X) .PSp 2 2 2 ∧
      z ∉ egaLayer X ⊔ centralizer (egaLayer X : Set X) ∧
      Nonempty (↥(egaLayer X ⊓ centralizer ({z} : Set X)) ≃* Equiv.Perm (Fin 6))) := by
  intro G _ _ _ L z t T₁ F tb Q x L1 hS hz hC ⟨hLie, hzE, hC6⟩
  obtain ⟨N, Sup⟩ := OutSetup.of_kStructure hS.one hS.transitive hS.K
  have hz2 : (QuotientGroup.mk ⟨z, hz⟩ : Xbar L1) * QuotientGroup.mk ⟨z, hz⟩ = 1 := by
    have := pow_orderOf_eq_one (QuotientGroup.mk Sup.zX : Xbar L1)
    rwa [Sup.orderOf_zbar, sq] at this
  have hCcard : Nat.card (centralizer
      ({(QuotientGroup.mk ⟨z, hz⟩ : Xbar L1)} : Set (Xbar L1))) = 1440 := by
    obtain ⟨φ⟩ := hC
    rw [Nat.card_congr φ.toEquiv, Nat.card_prod, Nat.card_eq_fintype_card (α := Equiv.Perm (Fin 6)),
      Fintype.card_perm, Fintype.card_fin]
    have h2 : Nat.card (Multiplicative (ZMod 2)) = 2 := by
      rw [Nat.card_eq_fintype_card]
      simp
    rw [h2]
    decide
  obtain ⟨Eh, hWr⟩ := exists_outerWr1 hz2 hCcard hLie hzE hC6
  exact hS.false_of_outerWr1 hz hWr

end CFSG.EvenSporadicStandard.M22Std
