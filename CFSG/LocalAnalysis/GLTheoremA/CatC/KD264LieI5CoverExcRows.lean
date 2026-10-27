module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieI5CoverExcMult
public import CFSG.LieType.Steinberg.CentralExt.GriessTwistedE6
public import CFSG.Adapters.TauCetiLieModels
public import CFSG.LieType.Steinberg.CentralExt.GriessExceptional

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open CFSG.Blueprint.Multiplier CFSG.LieType.Steinberg.CentralExt.GriessExceptional

section Certificates

theorem kd264I5CoverLift_E6 (q : TauCeti.PrimePower) (hd : (TauCeti.LieTypeIndex.E6 q).Valid)
    {K : Type} [Group K] [Finite K] (hK : CFSG.Open.IsQuasisimple K)
    (eK : K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie ⟨.E6 q, hd⟩).Group)
    (β : MulAut K) (hβ3 : β ^ 3 = 1) :
    ∃ (L : Type) (_ : Group L) (_ : Finite L) (π : L →* K) (βL : MulAut L),
      Function.Surjective π ∧ (∀ x : L, π x = 1 → x ∈ Subgroup.center L) ∧
        IsI5UniversalCover ⟨.E6 q, hd⟩ L ∧ βL ^ 3 = 1 ∧ ∀ x : L, π (βL x) = β (π x) := by
  have hmodel : CFSG.Models.LieModel (K ⧸ Subgroup.center K) .E6 0 q.p q.exponent :=
    CFSG.Models.lieModel_of_namesTag (t := .E6) (p := q.p) (f := q.exponent)
      ⟨q.prime_p, q.exponent_pos, rfl⟩ ⟨_, hd⟩ ⟨rfl, rfl⟩ eK
  obtain ⟨-, ⟨eM⟩⟩ := e6_row hmodel
  haveI : NeZero (Nat.gcd 3 (q.p ^ q.exponent - 1)) :=
    ⟨(Nat.gcd_pos_of_pos_left _ (by norm_num)).ne'⟩
  exact kd264I5CoverLift_of_multiplier ⟨.E6 q, hd⟩ hK eK
    (a := Nat.gcd 3 (q.p ^ q.exponent - 1))
    (by show _ = Nat.gcd 3 (q.card - 1); rw [TauCeti.PrimePower.card_def]) ⟨eM⟩ β hβ3

theorem kd264I5CoverLift_twistedE6 (q : TauCeti.PrimePower) (hd : (TauCeti.LieTypeIndex.twistedE6 q).Valid)
    (hq : 3 ≤ q.card)
    {K : Type} [Group K] [Finite K] (hK : CFSG.Open.IsQuasisimple K)
    (eK : K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie ⟨.twistedE6 q, hd⟩).Group)
    (β : MulAut K) (hβ3 : β ^ 3 = 1) :
    ∃ (L : Type) (_ : Group L) (_ : Finite L) (π : L →* K) (βL : MulAut L),
      Function.Surjective π ∧ (∀ x : L, π x = 1 → x ∈ Subgroup.center L) ∧
        IsI5UniversalCover ⟨.twistedE6 q, hd⟩ L ∧ βL ^ 3 = 1 ∧ ∀ x : L, π (βL x) = β (π x) := by
  have hmodel : CFSG.Models.LieModel (K ⧸ Subgroup.center K) .twistedE6 0 q.p q.exponent :=
    CFSG.Models.lieModel_of_namesTag (t := .twistedE6) (p := q.p) (f := q.exponent)
      ⟨q.prime_p, q.exponent_pos, rfl⟩ ⟨_, hd⟩ ⟨rfl, rfl⟩ eK
  have hq' : 3 ≤ q.p ^ q.exponent := by rw [← TauCeti.PrimePower.card_def]; exact hq
  obtain ⟨-, ⟨eM⟩⟩ := twistedE6_row hmodel hq'
  have hex : exceptionalOrders .twistedE6 0 q.p q.exponent = (1, 1) := by
    unfold exceptionalOrders
    split <;> first | rfl | (exfalso; simp_all)
  have hgen : genericOrders .twistedE6 0 q.p q.exponent = (Nat.gcd 3 (q.p ^ q.exponent + 1), 1) := rfl
  haveI : NeZero (Nat.gcd 3 (q.p ^ q.exponent + 1)) :=
    ⟨(Nat.gcd_pos_of_pos_left _ (by norm_num)).ne'⟩
  unfold generic exceptional at eM
  rw [hex, hgen] at eM
  exact kd264I5CoverLift_of_multiplier ⟨.twistedE6 q, hd⟩ hK eK
    (a := Nat.gcd 3 (q.p ^ q.exponent + 1))
    (by show _ = Nat.gcd 3 (q.card + 1); rw [TauCeti.PrimePower.card_def]) ⟨eM⟩ β hβ3

end Certificates

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie
