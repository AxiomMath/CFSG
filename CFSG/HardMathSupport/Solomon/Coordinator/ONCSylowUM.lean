module

public import CFSG.HardMathSupport.Solomon.Coordinator.ONCSylow
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FDefs

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open scoped commutatorElement

theorem isThreeOnePlusFour_of_clauses {X : Type} [Group X] [Finite X]
    (hZ : Nat.card (Subgroup.center X) = 3) (P : Sylow 3 X)
    (h5 : Nat.card (P : Subgroup X) = 3 ^ 5) (hexp : ∀ g ∈ (P : Subgroup X), g ^ 3 = 1)
    (hc : ∀ x ∈ (P : Subgroup X), ∀ y ∈ (P : Subgroup X), ⁅x, y⁆ ∈ Subgroup.center X)
    (hcen : ∀ x ∈ (P : Subgroup X), (∀ g ∈ (P : Subgroup X), g * x = x * g) →
      x ∈ Subgroup.center X) :
    UniquenessMaximal.IsThreeOnePlusFour (↥(P : Subgroup X)) := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have hZp : IsPGroup 3 (Subgroup.center X) := IsPGroup.of_card (n := 1) (by rw [hZ, pow_one])
  have hZle : Subgroup.center X ≤ (P : Subgroup X) := IsPGroup.le_sylow_of_normal hZp P
  have hcP : Subgroup.center ↥(P : Subgroup X) = (Subgroup.center X).subgroupOf (P : Subgroup X) := by
    ext ⟨g, hg⟩
    rw [Subgroup.mem_center_iff, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      exact hcen g hg fun k hk => by
        have := h ⟨k, hk⟩
        exact congrArg Subtype.val this
    · intro h k
      exact Subtype.ext (Subgroup.mem_center_iff.1 h k.1)
  refine ⟨h5, fun g => Subtype.ext (hexp g g.2), ?_, fun a b => ?_⟩
  · rw [hcP]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZle).toEquiv).trans hZ
  · rw [hcP, Subgroup.mem_subgroupOf]
    exact hc a a.2 b b.2

theorem inputSylowON_holds_of_hatON :
    ∀ (X : Type) [Group X] [Finite X], LocalBalance.IsHatON X → ∀ P : Sylow 3 X,
      UniquenessMaximal.IsThreeOnePlusFour (↥(P : Subgroup X)) := by
  intro X _ _ hX P
  obtain ⟨h5, hexp, hc, hcen⟩ := inputONSylow_holds X hX P
  exact isThreeOnePlusFour_of_clauses hX.2.1 P h5 hexp hc hcen

end CFSG.HardMathSupport.Solomon.Coordinator
