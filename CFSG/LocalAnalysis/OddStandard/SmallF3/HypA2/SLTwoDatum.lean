module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.LeavesV
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1NoSLTwo

public section

namespace CFSG.OddStandard.SmallF3.HypA2

open Subgroup CFSG.Blueprint CFSG.ComponentClassification

private theorem two_dvd_card_of_isPGroup_two_center {X : Type} [Group X] [Finite X]
    (h2 : IsPGroup 2 ↥(center X)) (hZ : center X ≠ ⊥) : 2 ∣ Nat.card ↥(center X) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := h2.exists_card_eq
  have hn0 : n ≠ 0 := by
    intro hn0
    apply hZ
    rw [← Subgroup.card_eq_one, hn, hn0, pow_zero]
  rw [hn]
  exact dvd_pow_self 2 hn0

private theorem pPrimeCore_eq_bot_of_isQuasisimple_of_isPGroup_center {X : Type} [Group X]
    [Finite X] (hq : IsQuasisimple X) (h2 : IsPGroup 2 ↥(center X)) (hZ : center X ≠ ⊥) :
    pPrimeCore 2 X = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN : (pPrimeCore 2 X).Normal := inferInstance
  have hcop : Nat.Coprime 2 (Nat.card ↥(pPrimeCore 2 X)) := CFSG.pPrimeCore_coprime_card
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hN with htop | hle
  · exfalso
    have h2dvd : 2 ∣ Nat.card ↥(center X) := two_dvd_card_of_isPGroup_two_center h2 hZ
    have hdvdX : Nat.card ↥(center X) ∣ Nat.card X := by
      simpa only [Subgroup.card_top] using
        Subgroup.card_dvd_of_le (le_top : Subgroup.center X ≤ ⊤)
    have h2X : 2 ∣ Nat.card X := h2dvd.trans hdvdX
    have hcopX : Nat.Coprime 2 (Nat.card X) := by
      rw [htop, Subgroup.card_top] at hcop
      exact hcop
    exact absurd (hcopX.eq_one_of_dvd h2X) (by norm_num)
  · have hpg : IsPGroup 2 ↥(pPrimeCore 2 X) :=
      (h2.to_subgroup ((pPrimeCore 2 X).subgroupOf (Subgroup.center X))).of_equiv
        (Subgroup.subgroupOfEquivOfLe hle)
    rcases hpg.card_eq_or_dvd with h1 | h2dvd
    · exact Subgroup.eq_bot_of_card_eq _ h1
    · exact absurd (hcop.eq_one_of_dvd h2dvd) (by norm_num)

theorem centralDatum_of_psl_two (hGr : TBLit.GriessMultipliersOdd) {K : Type} [Group K]
    [Finite K] (hK : IsQuasisimple K) (h2 : IsPGroup 2 ↥(center K)) (hZ : center K ≠ ⊥)
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h9 : 9 ≤ p ^ f)
    (hm : LieModel (K ⧸ center K) .PSL 2 p f) : CentralDatum K := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have h5 : 5 ≤ p ^ f := by omega
  have hSL : HarrisLit.IsSLTwoOver (p ^ f) K :=
    HarrisLit.T1.isSLTwoOver_of_psl2Cover hGr hp hp2 hK h2 hZ hm
  have hObot : pPrimeCore 2 K = ⊥ :=
    pPrimeCore_eq_bot_of_isQuasisimple_of_isPGroup_center hK h2 hZ
  have hquot : HarrisLit.IsSLTwoOver (p ^ f) (K ⧸ pPrimeCore 2 K) := by
    obtain ⟨F, i1, i2, hF, ⟨e⟩⟩ := hSL
    exact ⟨F, i1, i2, hF,
      ⟨(QuotientGroup.quotientMulEquivOfEq hObot).trans
        ((QuotientGroup.quotientBot).trans e)⟩⟩
  obtain ⟨zc, hzc⟩ :=
    exists_prime_orderOf_dvd_card' 2 (two_dvd_card_of_isPGroup_two_center h2 hZ)
  refine ⟨p ^ f, ⊤, (zc : K), hodd, h5, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe]; exact hzc
  · exact zc.2
  · exact Subgroup.mem_top _
  · obtain ⟨F, i1, i2, hF, ⟨e⟩⟩ := hSL
    exact ⟨F, i1, i2, hF, ⟨Subgroup.topEquiv.trans e⟩⟩
  · exact Or.inl ⟨p ^ f, hodd, h9, hquot⟩

end CFSG.OddStandard.SmallF3.HypA2
