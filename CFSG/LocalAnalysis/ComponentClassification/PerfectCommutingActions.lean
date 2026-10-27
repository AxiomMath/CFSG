module

public import CFSG.LocalAnalysis.ComponentClassification.SolvableKernelContainment
public import CFSG.LocalAnalysis.ComponentClassification.ThompsonAB

public section

namespace CFSG.ComponentClassification.PerfectCommutingActions

@[expose] def fixedKernel {V B : Type*} [Group V] [Group B] (action : B →* MulAut V) :
    Subgroup (MulAut V) where
  carrier := {automorphism | (∀ element : B, Commute automorphism (action element)) ∧
    ∀ member : V, (∀ element : B, action element member = member) → automorphism member = member}
  one_mem' := ⟨fun _ => Commute.one_left _, fun _ _ => rfl⟩
  mul_mem' := by
    intro left right hleft hright
    refine ⟨fun element => (hleft.1 element).mul_left (hright.1 element), ?_⟩
    intro member hfixed
    rw [MulAut.mul_apply, hright.2 member hfixed, hleft.2 member hfixed]
  inv_mem' := by
    intro automorphism hmem
    refine ⟨fun element => (hmem.1 element).inv_left, ?_⟩
    intro member hfixed
    have heq := hmem.2 member hfixed
    have hinverse := congrArg (fun value : V => automorphism⁻¹ value) heq
    rw [MulAut.inv_apply_self] at hinverse
    exact hinverse.symm

theorem fixedKernel_isPGroup {V B : Type*} [Group V] [Finite V] [Group B] [Finite B]
    (prime : ℕ) [Fact prime.Prime] (hV : IsPGroup prime V) (hB : IsPGroup prime B)
    (action : B →* MulAut V) : IsPGroup prime (fixedKernel action) := by
  let kernel := fixedKernel action
  let : Finite kernel := Finite.of_injective
    (fun automorphism : kernel => (automorphism.val : V → V)) (by
      intro left right heq
      apply Subtype.ext
      apply MulEquiv.ext
      exact fun member => congrFun heq member)
  have hcard : Nat.card kernel = prime ^ (Nat.card kernel).primeFactorsList.length := by
    apply Nat.eq_prime_pow_of_unique_prime_dvd (Nat.ne_of_gt Nat.card_pos)
    intro divisor hprime hdivides
    by_contra hne
    let : Fact divisor.Prime := ⟨hprime⟩
    obtain ⟨automorphism, horder⟩ := exists_prime_orderOf_dvd_card' divisor hdivides
    have hcoprime : divisor.Coprime prime := by
      apply hprime.coprime_iff_not_dvd.mpr
      intro hdivisor
      exact hne ((Nat.dvd_prime (Fact.out : prime.Prime)).mp hdivisor |>.resolve_left hprime.ne_one)
    have hpower : automorphism.val ^ divisor = 1 := by
      have heq := pow_orderOf_eq_one automorphism
      rw [horder] at heq
      exact congrArg Subtype.val heq
    have hone := ThompsonAB.coprime_eq_one prime hV hB action automorphism.val
      automorphism.property.1 automorphism.property.2 divisor hpower hcoprime
    have hsubtypeOne : automorphism = 1 := Subtype.ext hone
    simp [hsubtypeOne] at horder
    exact hprime.ne_one horder.symm
  exact IsPGroup.of_card hcard

theorem action_eq_one {X V B : Type*} [Group X] [Group.IsPerfect X]
    [Group V] [Finite V] [Group B] [Finite B]
    (prime : ℕ) [Fact prime.Prime] (hV : IsPGroup prime V) (hB : IsPGroup prime B)
    (leftAction : X →* MulAut V) (rightAction : B →* MulAut V)
    (hcommutes : ∀ left : X, ∀ right : B, Commute (leftAction left) (rightAction right))
    (hfixed : ∀ left : X, ∀ member : V,
      (∀ right : B, rightAction right member = member) → leftAction left member = member) :
    leftAction = 1 := by
  let kernel := fixedKernel rightAction
  let restriction : X →* kernel := leftAction.codRestrict kernel
    fun element => ⟨hcommutes element, hfixed element⟩
  let : Finite kernel := Finite.of_injective
    (fun automorphism : kernel => (automorphism.val : V → V)) (by
      intro left right heq
      apply Subtype.ext
      apply MulEquiv.ext
      exact fun member => congrFun heq member)
  let : Group.IsNilpotent kernel := (fixedKernel_isPGroup prime hV hB rightAction).isNilpotent
  let : Group.IsPerfect restriction.range := Group.IsPerfect.range restriction
  have hsubsingleton : Subsingleton restriction.range :=
    SolvableKernelContainment.perfect_solvable_subsingleton
  apply MonoidHom.ext
  intro element
  have hone : (⟨restriction element, ⟨element, rfl⟩⟩ : restriction.range) = 1 :=
    hsubsingleton.elim _ _
  exact congrArg (fun member : restriction.range => member.val.val) hone

end CFSG.ComponentClassification.PerfectCommutingActions
