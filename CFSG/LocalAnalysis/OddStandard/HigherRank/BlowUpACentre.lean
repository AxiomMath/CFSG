module

public import CFSG.GH74.GLS.TwoThin.DPair
public import CFSG.GH74.GLS.C3.Layer1.Defs
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafAlt
public import CFSG.LieType.Multipliers.L34Upper
import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeKFixed
import CFSG.RankThree.PerfectCover.HopfCentralCoversSetup

public section

namespace CFSG.OddStandard.HigherRank

open CFSG Subgroup
open CFSG.GH74.GLS CFSG.GH74.GLS.TwoThin CFSG.ComponentClassification

theorem exists_surjective_center_of_isL34Quotient
    {Q : Type} [Group Q] [Finite Q] (hQ : Group.IsPerfect Q)
    (hL : IsL34Quotient Q) :
    ∃ ψ : Multiplicative (ZMod 3 × ZMod 4 × ZMod 4) →* ↥(center Q), Function.Surjective ψ := by
  have := hQ
  obtain ⟨-, ⟨μ⟩⟩ := LieType.Multipliers.L34Upper.multiplier_PSL_three_four (Q ⧸ center Q) hL
  let q : Q →* Q ⧸ center Q := QuotientGroup.mk' (center Q)
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hker : q.ker = center Q := QuotientGroup.ker_mk' _
  refine ⟨(MulEquiv.subgroupCongr hker).toMonoidHom.comp
    ((RankThree.PerfectCover.hopfMultiplierToKer q hq hker.le).comp
      ((RankThree.PerfectCover.hopfMultiplierEquivGriess (Q ⧸ center Q)).toMonoidHom.comp
        μ.symm.toMonoidHom)), ?_⟩
  exact (MulEquiv.subgroupCongr hker).surjective.comp
    ((RankThree.PerfectCover.hopfMultiplierToKer_surjective q hq hker.le).comp
      ((RankThree.PerfectCover.hopfMultiplierEquivGriess (Q ⧸ center Q)).surjective.comp
        μ.symm.surjective))

theorem card_multiplier_L34 :
    Nat.card (Multiplicative (ZMod 3 × ZMod 4 × ZMod 4)) = 48 := by
  rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod 3 × ZMod 4 × ZMod 4) ≃ _),
    Nat.card_prod, Nat.card_prod, Nat.card_zmod, Nat.card_zmod]

theorem card_center_le_sixteen_of_isL34Quotient
    {Q : Type} [Group Q] [Finite Q] (hQ : Group.IsPerfect Q)
    (hL : IsL34Quotient Q) (h2 : IsPGroup 2 ↥(center Q)) : Nat.card ↥(center Q) ≤ 16 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ψ, hψ⟩ := exists_surjective_center_of_isL34Quotient hQ hL
  have hdvd : Nat.card ↥(center Q) ∣ 48 :=
    card_multiplier_L34 ▸ Subgroup.card_dvd_of_surjective hψ
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp h2
  rw [hn] at hdvd ⊢
  have hn4 : n ≤ 4 := by
    by_contra h
    have h5 : 2 ^ 5 ∣ 2 ^ n := pow_dvd_pow 2 (by omega)
    exact absurd (h5.trans hdvd) (by norm_num)
  calc 2 ^ n ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) hn4
    _ = 16 := by norm_num

theorem not_isElementaryAbelian_center_of_isL34Quotient
    {Q : Type} [Group Q] [Finite Q] (hQ : Group.IsPerfect Q)
    (hL : IsL34Quotient Q) (h16 : Nat.card ↥(center Q) = 16) :
    ¬ IsElementaryAbelian 2 ↥(center Q) := by
  intro hE
  obtain ⟨ψ, hψ⟩ := exists_surjective_center_of_isL34Quotient hQ hL
  have hk : Nat.card ψ.ker = 3 := by
    have h := Subgroup.card_ker_mul_card_of_surjective hψ
    rw [h16, card_multiplier_L34] at h
    omega
  set m : Multiplicative (ZMod 3 × ZMod 4 × ZMod 4) := Multiplicative.ofAdd (0, 1, 0) with hm
  have hm2 : m ^ 2 ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, map_pow]
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p (self := hE) 2 ↥(center Q)) (ψ m)
  have h3 : (⟨m ^ 2, hm2⟩ : ψ.ker) ^ Nat.card ψ.ker = 1 := pow_card_eq_one'
  rw [hk] at h3
  have h3' : (m ^ 2) ^ 3 = 1 := congrArg Subtype.val h3
  revert h3'
  rw [hm]
  decide

theorem card_eq_of_isL34Quotient {Q : Type} [Group Q]
    (hL : IsL34Quotient Q) : Nat.card Q = Nat.card ↥(center Q) * 20160 := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center Q), CatLeaf.card_of_isL34Type hL,
    mul_comm]

theorem hatCard_le_of_isL34Quotient
    {X : Type} [Group X]
    [Finite X] {H K : Subgroup X} (hK : IsPCompIn 2 H K) (hL : IsL34Quotient (kBar K)) :
    hatCard K ≤ 16 * 20160 := by
  have h16 := card_center_le_sixteen_of_isL34Quotient (isQuasisimple_hat hK).1 hL
    (GrSLit.HeK.isPGroup_center_quotient ↥K)
  show Nat.card (kBar K) ≤ 16 * 20160
  rw [card_eq_of_isL34Quotient hL]
  exact Nat.mul_le_mul_right _ h16

end CFSG.OddStandard.HigherRank
