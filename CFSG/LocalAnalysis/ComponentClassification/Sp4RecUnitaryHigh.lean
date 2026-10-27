module

public import CFSG.LocalAnalysis.ComponentClassification.Sp4RecSmall
public import CFSG.LocalAnalysis.ComponentClassification.OddClassSelectorU

public noncomputable section

namespace CFSG.ComponentClassification.Sp4Rec

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.UnitaryFlag

namespace Config

variable {H : Type} [Group H] [Finite H] (c : Sp4Rec.Config H)

include c in
theorem exists_ne_commute_G :
    ∃ u v : ↥(generalizedFitting H), u * v ≠ v * u := by
  by_contra hc
  push Not at hc
  have hsimple := c.simple
  have hle : generalizedFitting H ≤ centralizer (generalizedFitting H : Set H) := by
    intro x hx
    rw [mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (hc ⟨y, hy⟩ ⟨x, hx⟩)
  rw [c.centralizer_eq_bot] at hle
  obtain ⟨u, v, huv⟩ := hsimple.toNontrivial
  apply huv
  exact Subtype.ext ((mem_bot.mp (hle u.2)).trans (mem_bot.mp (hle v.2)).symm)

include c in
theorem false_of_unitary_high {m p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hm : 5 ≤ m)
    (hG : StatedClassicalModel ↥(generalizedFitting H) .PSU m p f) : False := by
  have hGn : (generalizedFitting H).Normal := LocalCores.generalized_fitting_characteristic.2
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨⟨-, hf, -, -⟩, ⟨θ⟩⟩ := ClassicalModelStatedBridge.classicalModel_psu_of_stated hG
  let hd := CatalogueBUnitaryB.galoisField_unitaryFieldData p f hf
  let psi : ↥(generalizedFitting H) ≃* unitaryPSU hd m :=
    (θ.trans (ClassicalModelStatedBridge.psuModelEquiv m p f)).trans
      (unitaryPSUEquiv hd (by omega : 1 ≤ m)).symm
  have : Finite (unitaryPSU hd m) := Finite.of_equiv _ psi.toEquiv
  have hq := c.isQuasisimple_J_of_fixed psi fun α hα2 hα1 L hL =>
    CatalogueBUnitaryB.odd_unitary_involution_fixed_p_components hd hp2 (by omega) α
      (orderOf_eq_prime hα2 hα1) 2 Nat.prime_two L hL
  have hM : LieModel ↥(generalizedFitting H) .PSU m p f := Or.inl ⟨by decide, hG⟩
  exact OddClassSelector.su_family_false (W := generalizedFitting H) c.simple c.exists_ne_commute_G
    c.centralizer_eq_bot c.orderOf_a c.J_le_G (c.isComponentOf_J hq) (c.smallType_J hq) hp hp2
    hf hm hM

end Config

end CFSG.ComponentClassification.Sp4Rec
