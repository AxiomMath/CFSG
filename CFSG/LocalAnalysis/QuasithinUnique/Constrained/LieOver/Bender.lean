module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.LieOver.Tags
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113OverBender
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113CentBender
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113CentSmall
public import CFSG.Adapters.StatedClassicalUnitaryOrders

public section

namespace CFSG.Quasithin.LieOver

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

private theorem lo3_exists_noncomm {X : Type} [Group X] (hS : IsSimpleGroup X)
    (hp : ¬ (Nat.card X).Prime) : ∃ a b : X, a * b ≠ b * a := by
  by_contra h
  have hc : ∀ a b : X, a * b = b * a := fun a b => by
    by_contra hab
    exact h ⟨a, b, hab⟩
  have : IsMulCommutative X := ⟨⟨hc⟩⟩
  exact hp ((Group.is_simple_iff_prime_card (α := X)).1 hS)

theorem asLieTwoAt_twistedB2 : AsLieTwoAt .twistedB2 := by
  intro n f X _ _ _ _ hmod
  rcases hmod with ⟨hcl, -⟩ | ⟨-, hce, -⟩ | ⟨-, hrt, -⟩ | ⟨-, -, hsz⟩
  · exact absurd hcl (by decide)
  · exact absurd hce (by decide)
  · exact absurd hrt (by decide)
  · exact And.intro (CFSG.QuasithinUnique.Bridge.Over.overgroups_isSz hsz)
      (CFSG.QuasithinUnique.Bridge.sylowAutTrivial_isSz hsz)

theorem asLieTwoPSU33_holds :
    AsLieTwoPSU33 := by
  intro X _ _ hS hU
  have hc : Nat.card X = 6048 :=
    CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_three_three hU
  have hnc : ∃ a b : X, a * b ≠ b * a := lo3_exists_noncomm hS (by rw [hc]; norm_num)
  exact And.intro (CFSG.QuasithinUnique.Bridge.Over.overgroups_psu_three_three hU)
    (CFSG.QuasithinUnique.Bridge.sylowAutTrivial_psu_three_three hS hnc hU)

end CFSG.Quasithin.LieOver
