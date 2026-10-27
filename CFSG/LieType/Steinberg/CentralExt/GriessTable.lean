module

public import CFSG.LieType.Steinberg.CentralExt.GriessGTwoThree
public import CFSG.LieType.Steinberg.CentralExt.GriessGTwoFour
public import CFSG.LieType.Steinberg.CentralExt.GriessFFourTwo
public import CFSG.LieType.Steinberg.CentralExt.GriessNativeModels

public section

open CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Blueprint.Multiplier

namespace CFSG.LieType.Steinberg.CentralExt.GriessTable

theorem griess_all_models_of_one
    (h2E62 : ∀ (Y : Type) [Group Y], CFSG.Models.LieModel Y .twistedE6 0 2 1 →
      GriessAll.GriessRow Y .twistedE6 0 2 1)
    {X : Type} [Group X] (t : StatedLieTag) (n p f : ℕ)
    (hmodel : CFSG.Models.LieModel X t n p f) : GriessAll.GriessRow X t n p f :=
  GriessAll.griess_all_models_of_remaining
    (fun _ _ h => GriessExceptional.g2_three_row h) (fun _ _ h => GriessExceptional.g2_four_row h)
    (fun _ _ h => GriessExceptional.f4_two_row h) h2E62 t n p f hmodel

theorem griess_native_models_of_one
    (h2E62 : ∀ (Y : Type) [Group Y], CFSG.Blueprint.LieModel Y .twistedE6 0 2 1 →
      GriessAll.GriessRow Y .twistedE6 0 2 1)
    {X : Type} [Group X] (t : StatedLieTag) (n p f : ℕ)
    (hmodel : CFSG.Blueprint.LieModel X t n p f) : GriessAll.GriessRow X t n p f :=
  GriessNative.griess_native_models_of_remaining
    (fun _ _ h => GriessExceptional.g2_three_native_row
      (GriessNative.chevalley_of_lieModel h (by decide)).2)
    (fun _ _ h => GriessExceptional.g2_four_native_row
      (GriessNative.chevalley_of_lieModel h (by decide)).2)
    (fun _ _ h => GriessExceptional.f4_two_native_row
      (GriessNative.chevalley_of_lieModel h (by decide)).2) h2E62 t n p f hmodel

end CFSG.LieType.Steinberg.CentralExt.GriessTable
