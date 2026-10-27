module

public import CFSG.HardMathSupport.Malle.E27Lie.Outer.Transport
public import CFSG.RankThree.Classical.SteinbergBTUnitarySubfield
public import CFSG.Quasithin.Background.F918V3T3A
public import CFSG.LocalAnalysis.SteinbergBNUnitaryThreeOuterInvolutionRigidity
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderPSUDescent
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.HardMathSupport.Malle.E27Lie

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.RankThree.Classical CFSG.RankThree.UnitaryDescent CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LieType.Chevalley (fixSubfield)
open CFSG.HardMathSupport.Lang.Coordinator
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)

theorem exists_fixed_perfect_three_PSU {ℓ f n : ℕ} {F : Type} [Field F]
    (h : UnitaryFieldData ℓ f F) (hn : 3 ≤ n) (hne : ¬(n = 3 ∧ ℓ ^ f = 2))
    (hq0 : ¬(n = 3 ∧ ℓ ^ (f / 3) = 2))
    (β : MulAut (primeFormP h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)))
    (hβ3 : β ^ 3 = 1)
    (hσ1 : primeFormFieldFactor h isPrimeFormGram_one hn hne β ≠ 1) :
    ∃ D : Subgroup (primeFormP h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)),
      (∀ x ∈ D, β x = x) ∧ ⁅D, D⁆ = D ∧ 3 ∣ Nat.card D := by
  classical
  have : Finite F := h.finite
  have hp : Nat.Prime 3 := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have hβ1 : β ≠ 1 := fun h1 => hσ1 (by rw [h1, map_one])
  have hβord : orderOf β = 3 := orderOf_eq_prime hβ3 hβ1
  set σ := primeFormFieldFactor h isPrimeFormGram_one hn hne β with hσdef
  have hσp : σ ^ 3 = 1 := by rw [hσdef, ← map_pow, hβ3, map_one]
  have hσord : orderOf σ = 3 := orderOf_eq_prime hσp hσ1
  obtain ⟨hpf, -, -, -, -, M, hM⟩ :=
    unitary_prime_semilinear_field_descent' h hn hne hp hp2 β hβord σ hσdef.symm hσord
  set u := primeFormConjHom h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) M with hu
  set fσ := primeFormFieldHom h (isPrimeFormGram_one (n := n)) σ with hfσ
  have hβu : β * u = u * fσ := by
    rw [← hM]
    group
  set h₀ := fixSubfield_unitaryFieldData h hp hp2 hσord with hh₀
  have hbar := fixSubfield_unitaryFieldData_bar h hp hp2 hσord
  have hinj := subfieldPSU_injective h h₀ hbar n (by omega)
  have hle := range_subfieldPSU_le h n h₀ hbar
  have hq0' : ¬(n = 3 ∧ ℓ ^ (f / 3) = 2) := hq0
  have hperfSU : Group.IsPerfect (gramSU h₀ ((1 : GL (Fin n) (fixSubfield σ)) :
      Matrix (Fin n) (Fin n) (fixSubfield σ))) := isPerfect_gramSU_one h₀ hn hq0'
  have hperf : Group.IsPerfect (primeFormP h₀ ((1 : GL (Fin n) (fixSubfield σ)) :
      Matrix (Fin n) (Fin n) (fixSubfield σ))) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
  let D0 := (subfieldPSU h h₀ hbar n).range
  let D := D0.map (u : MulAut _).toMonoidHom
  let eD : ↥D ≃* primeFormP h₀ ((1 : GL (Fin n) (fixSubfield σ)) :
      Matrix (Fin n) (Fin n) (fixSubfield σ)) :=
    (D0.equivMapOfInjective (u : MulAut _).toMonoidHom (u : MulAut _).injective).symm.trans
      (MonoidHom.ofInjective hinj).symm
  refine ⟨D, ?_, commutator_eq_self_of_equiv_perfect D eD, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    have hy' : fσ y = y := hle hy
    have := congrArg (fun g : MulAut _ => g y) hβu
    simp only [MulAut.mul_apply] at this
    show β (u y) = u y
    rw [this]
    exact congrArg _ hy'
  · rw [Nat.card_congr eD.toEquiv,
      ← Nat.card_congr (CFSG.LocalAnalysis.unitaryPSUEquivPrimeFormOne h₀ n).toEquiv,
      Nat.card_congr (unitaryPSUEquiv h₀ (by omega : 1 ≤ n)).toEquiv]
    exact CFSG.Quasithin.F918V3T3.three_dvd_card_PSU_of_three_le hn (pow_pos h₀.prime.pos _).ne'

end CFSG.HardMathSupport.Malle.E27Lie
