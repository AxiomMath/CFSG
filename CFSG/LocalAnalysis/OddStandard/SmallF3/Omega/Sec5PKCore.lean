module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec79BA
public import CFSG.Assembly.Subnormal

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G] [Finite G]

private theorem sec5pk_oddCoreIn_le_of_open_isSubnormal {X K : Subgroup G}
    (h : CFSG.Open.IsSubnormal K X) : oddCoreIn K ≤ oddCoreIn X := by
  induction h with
  | refl => exact le_rfl
  | step hKM hN _ ih => exact (oddCoreIn_le_of_normal hKM hN).trans ih

theorem sec5pk_oddCoreIn_le_of_subnormal {X K : Subgroup G} (hKX : K ≤ X)
    (hK : (K.subgroupOf X).IsSubnormal) : oddCoreIn K ≤ oddCoreIn X := by
  exact sec5pk_oddCoreIn_le_of_open_isSubnormal
    ((CFSG.Open.IsSubnormal.iff_subgroupOf hKX).2 hK)

private theorem sec5pk_twoCoreIn_le_of_normal {H M : Subgroup G} (hHM : H ≤ M)
    (hN : (H.subgroupOf M).Normal) : twoCoreIn H ≤ twoCoreIn M := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : M ≤ Subgroup.normalizer (H : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hHM).mp hN
  have h2 : M ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 H : Set G) :=
    h1.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 H)
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 H).trans hHM) h2
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H)

private theorem sec5pk_twoCoreIn_le_of_open_isSubnormal {X K : Subgroup G}
    (h : CFSG.Open.IsSubnormal K X) : twoCoreIn K ≤ twoCoreIn X := by
  induction h with
  | refl => exact le_rfl
  | step hKM hN _ ih => exact (sec5pk_twoCoreIn_le_of_normal hKM hN).trans ih

theorem sec5pk_twoCoreIn_le_of_subnormal {X K : Subgroup G} (hKX : K ≤ X)
    (hK : (K.subgroupOf X).IsSubnormal) : twoCoreIn K ≤ twoCoreIn X := by
  exact sec5pk_twoCoreIn_le_of_open_isSubnormal
    ((CFSG.Open.IsSubnormal.iff_subgroupOf hKX).2 hK)

theorem sec5pk_comm_oddCoreIn_twoCoreIn (X : Subgroup G) :
    ∀ u ∈ oddCoreIn X, ∀ q ∈ twoCoreIn X, u * q = q * u := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro u hu q hq
  have hPK : twoCoreIn X ≤ X := CFSG.LieType.BorelTits.pCoreOf_le 2 X
  have hOK : oddCoreIn X ≤ X := (oddCoreIn_normal X).1
  have hPn : ((twoCoreIn X).subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPK).mpr
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X)
  have hOn : ((oddCoreIn X).subgroupOf X).Normal := (oddCoreIn_normal X).2
  have hP : IsPGroup 2 (twoCoreIn X) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X
  have hO : Odd (Nat.card (oddCoreIn X)) := odd_card_oddCoreIn X
  exact (commute_of_normal_two_odd hPK hOK hPn hOn hP hO q hq u hu).symm

end CFSG.OddStandard.SmallF3.Omega
