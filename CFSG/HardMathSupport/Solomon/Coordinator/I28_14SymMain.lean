module

public import CFSG.HardMathSupport.Solomon.Coordinator.I28_14SymC
public import CFSG.HardMathSupport.Solomon.Coordinator.I28_14SymN

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.ComponentClassification.OutcomeLocal CFSG.Open Module Submodule

theorem tvC_symOdd {m : ℕ} (hm : 5 ≤ m) (hmo : Odd m) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {A : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) (sumZero m))}
    (hA : IsMaxElemAbelianIn (U := sumZero m) p (sumZeroRep m).range A)
    {t : LinearMap.GeneralLinearGroup (ZMod 2) (sumZero m)} (htG : t ∈ (sumZeroRep m).range)
    (ht : IsF2Transvection t) : HasCentralizedConj (U := sumZero m) p (sumZeroRep m).range A t :=
  i28_14_symModel_C (SymModel.full hm) hm hp hp2 hA htG ht

theorem tvC_symEven {m : ℕ} (hm : 5 ≤ m) (hme : Even m) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {A : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) (sumZero m ⧸ onesLine m))}
    (hA : IsMaxElemAbelianIn (U := sumZero m ⧸ onesLine m) p (heartRep m).range A)
    {t : LinearMap.GeneralLinearGroup (ZMod 2) (sumZero m ⧸ onesLine m)}
    (htG : t ∈ (heartRep m).range)
    (ht : IsF2Transvection t) :
    HasCentralizedConj (U := sumZero m ⧸ onesLine m) p (heartRep m).range A t :=
  i28_14_symModel_C (SymModel.heart hm) hm hp hp2 hA htG ht

theorem tvN_symOdd {m : ℕ} (hm : 5 ≤ m) (hmo : Odd m)
    (haut : ∀ α : MulAut (Equiv.Perm (Fin m)),
      (∀ i j : Fin m, i ≠ j → ∃ a b : Fin m, a ≠ b ∧ α (Equiv.swap i j) = Equiv.swap a b) →
        ∃ π : Equiv.Perm (Fin m), α = MulAut.conj π)
    {g : LinearMap.GeneralLinearGroup (ZMod 2) (sumZero m)}
    (hg : ∀ x ∈ (sumZeroRep m).range, g * x * g⁻¹ ∈ (sumZeroRep m).range) :
    g ∈ (sumZeroRep m).range :=
  i28_14_symModel_N (SymModel.full hm) hm haut hg

theorem tvN_symEven {m : ℕ} (hm : 5 ≤ m) (hme : Even m)
    (haut : ∀ α : MulAut (Equiv.Perm (Fin m)),
      (∀ i j : Fin m, i ≠ j → ∃ a b : Fin m, a ≠ b ∧ α (Equiv.swap i j) = Equiv.swap a b) →
        ∃ π : Equiv.Perm (Fin m), α = MulAut.conj π)
    {g : LinearMap.GeneralLinearGroup (ZMod 2) (sumZero m ⧸ onesLine m)}
    (hg : ∀ x ∈ (heartRep m).range, g * x * g⁻¹ ∈ (heartRep m).range) :
    g ∈ (heartRep m).range :=
  i28_14_symModel_N (SymModel.heart hm) hm haut hg

end CFSG.HardMathSupport.Solomon.Coordinator
