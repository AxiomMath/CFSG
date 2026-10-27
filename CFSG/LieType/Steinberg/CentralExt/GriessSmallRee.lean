module

public import CFSG.LieType.Steinberg.CentralExt.GriessExceptional
public import CFSG.LieType.Steinberg.CentralExt.SmallReeMultiplier
public import CFSG.Adapters.TauCetiExceptional.ReeBridge

public section

open CFSG.Assembly.LowTwoRank CFSG.Blueprint.Multiplier CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
  CFSG.Blueprint CFSG.Blueprint.Chevalley

namespace CFSG.LieType.Steinberg.CentralExt.GriessExceptional

variable {X : Type} [Group X]

theorem twistedG2_row
    {n p f : ℕ} (hmodel : CFSG.Models.LieModel X .twistedG2 n p f) :
    commutator X = ⊤ ∧
      Nonempty (CFSG.Open.griessHopfMultiplier X ≃*
        generic .twistedG2 n p f × exceptional .twistedG2 n p f) := by
  obtain ⟨-, hcl | ⟨-, ⟨d, hv⟩, hd, ⟨e⟩⟩⟩ := hmodel
  · exact hcl.2.elim
  · cases d with
    | reeG2 m =>
      obtain ⟨rfl, rfl⟩ := hd
      have hm1 : 1 ≤ m :=
        (TauCeti.LieTypeIndex.inStandardRange_iff _).1 ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have hK : Nat.card (GaloisField 3 (2 * m + 1)) = 3 ^ (2 * m + 1) :=
        GaloisField.card 3 (2 * m + 1) (by omega)
      have : CharP (GaloisField 3 (2 * m + 1)) G2.prime :=
        (inferInstance : CharP (GaloisField 3 (2 * m + 1)) 3)
      obtain ⟨b⟩ := CFSG.TauCetiBridge.reeG2Bridge m hv (GaloisField 3 (2 * m + 1)) hK
      have e1 : DerivedCentralQuotient (reeFixedGroup .G2 (GaloisField 3 (2 * m + 1)) reeG2Perm
          fun i => if i ∈ reeG2Long then 3 ^ m else 3 ^ (m + 1)) ≃*
            DerivedCentralQuotient (G2.reeGamma (GaloisField 3 (2 * m + 1)) m) := by
        rw [reeGamma_eq_reeFixedGroup]
        exact MulEquiv.refl _
      obtain ⟨E⟩ := nonempty_derivedCentralQuotient_mulEquiv_reeGamma_G2
        (K := GaloisField 3 (2 * m + 1)) hm1 hK
      obtain ⟨h1, h2⟩ := SmallReeClosed.smallRee_hopfMultiplier hK hm1
      let eZ : G2.reeGamma (GaloisField 3 (2 * m + 1)) m ⧸
          Subgroup.center (G2.reeGamma (GaloisField 3 (2 * m + 1)) m) ≃* X :=
        ((QuotientGroup.quotientMulEquivOfEq (center_reeGamma_G2_eq_bot hK)).trans
          QuotientGroup.quotientBot).trans (((e.trans b.symm).trans e1).trans E).symm
      have : Group.IsPerfect (G2.reeGamma (GaloisField 3 (2 * m + 1)) m ⧸
          Subgroup.center (G2.reeGamma (GaloisField 3 (2 * m + 1)) m)) := ⟨h1⟩
      have : Group.IsPerfect X := Group.IsPerfect.ofSurjective (f := eZ.toMonoidHom) eZ.surjective
      refine row_of_subsingleton rfl ?_ ⟨Group.IsPerfect.commutator_eq_top,
        (griessHopfMultiplierCongr eZ.symm).toEquiv.subsingleton⟩
      unfold exceptionalOrders
      split <;> first | rfl | omega
    | _ => simp [CFSG.Models.NamesTag] at hd

end CFSG.LieType.Steinberg.CentralExt.GriessExceptional
