module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieFix
public import CFSG.LieType.Chevalley.RootLocalComponentFree

public section

namespace CFSG.QuasithinUnique.Id2519

open CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley

theorem rootWeightDatum_involution_centralizer_component_free
    {F : Type} [Field F] [Finite F]
    [CharP F 2] (D : RootWeightDatum F) (y : ↥D.group) (hy : orderOf y = 2)
    (B : Subgroup ↥(Subgroup.centralizer ({y} : Set ↥D.group))) : ¬ CFSG.IsComponent B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQp : IsPGroup 2 (Subgroup.zpowers y) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy, pow_one])
  have hQ : Subgroup.zpowers y ≠ ⊥ := by
    intro h
    rw [Subgroup.zpowers_eq_bot] at h
    rw [h, orderOf_one] at hy
    omega
  obtain ⟨-, hfree⟩ := D.defining_characteristic_root_local_groups_component_free 2
    (Subgroup.zpowers y) hQp hQ (Subgroup.centralizer ({y} : Set ↥D.group))
    (Or.inr (centralizer_zpowers_eq y).symm)
  exact hfree B

end CFSG.QuasithinUnique.Id2519
