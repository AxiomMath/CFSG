module

public import CFSG.Assembly.Reduction
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Classification

public section

namespace CFSG.Assembly

@[expose] def InCatalog : GroupProp := fun G _ => ∃ i : TauCeti.CFSGIndex, Nonempty (G ≃* i.Group)

theorem abelian_simple (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hcomm : ∀ a b : G, a * b = b * a) : InCatalog G := by
  let _ : CommGroup G := { ‹Group G› with mul_comm := hcomm }
  have hp : (Nat.card G).Prime := IsSimpleGroup.prime_card
  have : Fact (Nat.card G).Prime := ⟨hp⟩
  refine ⟨.cyclic _ hp, ⟨mulEquivOfPrimeCardEq rfl ?_⟩⟩
  have : NeZero (Nat.card G) := ⟨hp.ne_zero⟩
  change Nat.card (Multiplicative (ZMod (Nat.card G))) = Nat.card G
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]

theorem inCatalog_isoInvariant : KCore.IsoInvariant InCatalog := fun e ⟨i, ⟨e'⟩⟩ =>
  ⟨i, ⟨e.trans e'⟩⟩

theorem inCatalog_containsAbelianSimple : KCore.ContainsAbelianSimple InCatalog :=
  fun S _ _ _ hcomm => abelian_simple S hcomm

end CFSG.Assembly
