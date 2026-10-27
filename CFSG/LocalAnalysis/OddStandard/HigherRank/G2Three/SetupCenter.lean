module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.Leaves
public import CFSG.LieType.Steinberg.CentralExt.G2ThreeMultiplier

public section

namespace CFSG.OddStandard.HigherRank.G2Three

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley

namespace Setup

section Multiplier

theorem card_center_dvd_three {L : Type} [Group L] [Finite L] (hperf : Group.IsPerfect L)
    (hL : HRG23 (L ⧸ center L)) : Nat.card (center L) ∣ 3 := by
  have hCE : ChevalleyExceptionalModel (L ⧸ center L) .G2 3 1 :=
    CFSG.Blueprint.LieModel.chevalleyExceptionalModel hL (by decide)
  obtain ⟨K, hfield, hfinite, hKpow, ⟨e⟩⟩ := hCE.2
  letI : Field K := hfield
  letI : Finite K := hfinite
  have hK : Nat.card K = 3 := by simpa using hKpow
  let eAdj : AdjointQuotient .G2 K ≃* adjointGroup .G2 K :=
    (QuotientGroup.quotientMulEquivOfEq
      (CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (τ := .G2) (K := K))).trans
        QuotientGroup.quotientBot
  let η : L ⧸ center L ≃* adjointGroup .G2 K := e.trans eAdj
  let π : L →* adjointGroup .G2 K := η.toMonoidHom.comp (QuotientGroup.mk' (center L))
  have hπ : Function.Surjective π := η.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker = center L := by
    dsimp only [π]
    rw [MonoidHom.ker_comp_of_injective _ _ η.injective, QuotientGroup.ker_mk']
  haveI : Group.IsPerfect L := hperf
  obtain ⟨c, hc3, hle⟩ :=
    CFSG.LieType.Steinberg.CentralExt.FieldThree.g2_three_ker_le_zpowers
      hK hπ (by rw [hker])
  have hle' : center L ≤ Subgroup.zpowers c := hker ▸ hle
  have hdvd : Nat.card (center L) ∣ Nat.card (Subgroup.zpowers c) :=
    Subgroup.card_dvd_of_le hle'
  rw [Nat.card_zpowers] at hdvd
  exact hdvd.trans (orderOf_dvd_of_pow_eq_one hc3)

end Multiplier

theorem inf_center_eq_bot {L : Type} [Group L] [Finite L] (hZ : Odd (Nat.card (center L)))
    (S : Sylow 2 L) : (S : Subgroup L) ⊓ center L = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
  rw [Subgroup.mem_inf] at hx
  obtain ⟨hxS, hxZ⟩ := hx
  have hodd : Odd (orderOf x) := by
    have hdvdZ : orderOf (⟨x, hxZ⟩ : center L) ∣ Nat.card (center L) :=
      orderOf_dvd_natCard _
    rw [← Subgroup.orderOf_coe (⟨x, hxZ⟩ : center L)] at hdvdZ
    exact Odd.of_dvd_nat hZ hdvdZ
  obtain ⟨k, hk⟩ := S.isPGroup'.exists_pow_pow_eq_one ⟨x, hxS⟩
  have hxpow : x ^ 2 ^ k = 1 := by
    simpa using congrArg (Subtype.val) hk
  have hdvd : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hxpow
  rw [← orderOf_eq_one_iff]
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  cases j with
  | zero => simpa using hj
  | succ j =>
      exfalso
      exact (Nat.not_even_iff_odd.mpr hodd)
        (by rw [hj]; exact Even.pow_of_ne_zero even_two (Nat.succ_ne_zero j))

end Setup

end CFSG.OddStandard.HigherRank.G2Three
