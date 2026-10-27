module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.Split
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.G2Aux.Orders
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.ExcInnerBase
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.ExcInnerFamG2
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcFieldG2Eight
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcFieldEvenF4G2
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcFieldG2Three
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcFieldOdd
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma32
public import CFSG.HardMathSupport.Solomon.LocalBalance.Prop22
public import CFSG.HardMathSupport.Timmesfeld.Balance.Alt.Setup
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.IG1114
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremB
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremC
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.ZJTheorem
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.GW1965RemarkDGroup
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29Helpers

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.G2Aux

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.DefChar
  CFSG.HardMathSupport.Timmesfeld.LocalTwo CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.LieType.SeitzGeneration CFSG.TauCetiBridge
  CFSG.LieType.Ree CFSG.RankThree.Chevalley CFSG.RankThree.Chevalley.SteinbergBT
open CFSG.LocalAnalysis.ComponentInitial (finite_field_prime_power_characteristic)

set_option linter.unusedSectionVars false


theorem localTwoCrossFamCat_G2_of_inner {p : ℕ} (hp : p.Prime) (hp35 : p = 3 ∨ p = 5)
    (hin : ∀ (K : Type) [Field K] [Finite K], 3 ≤ Nat.card K → ¬ p ∣ Nat.card K →
      InnerPlaneBalance p (adjointGroup Tag.G2 K)) : LocalTwoCrossFamCat p .G2 := by
  rintro ⟨d, hv⟩ ⟨q, hd⟩ hc -
  change d = _ at hd
  subst hd
  have hpq : p ≠ q.p := fun h => hc (by simp [h])
  have : Fact p.Prime := ⟨hp⟩
  have hq3 : 3 ≤ q.card := (TauCeti.LieTypeIndex.inStandardRange_iff (.G2 q)).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  obtain ⟨K, _, _, hK, hKc, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.g2 q hv
  have := hKc
  have hK' : Nat.card K = q.p ^ q.exponent := hK.trans (TauCeti.PrimePower.card_def q)
  have hpK : ¬ p ∣ Nat.card K := by
    rw [hK]
    exact not_dvd_card_of_ne hp hpq
  have hinj := mulAut_conj_injective_adjointGroup (τ := Tag.G2) (K := K)
  have hin' : InnerPlaneBalance p (adjointGroup Tag.G2 K) := hin K (hK ▸ hq3) hpK
  have hout : OuterFields p (adjointGroup Tag.G2 K) := by
    obtain ⟨Q, _, _, Θ, -, hker⟩ := exists_hom_cyclic_G2 q hq3 K hK
    refine outerFields_of_hom Θ hp hinj (fun x hx _ => by rw [hker] at hx; exact hx) ?_
    by_cases hd6 : p ∣ Nat.card K ^ 6 - 1
    · refine Or.inr fun x hxp hxo => ?_
      have hxord := orderOf_eq_of_pow_eq_one_of_not_mem hp hxp hxo
      have hK1 : 1 ≤ Nat.card K := Nat.card_pos
      have hdf : ∀ σ : K ≃+* K, orderOf σ = p → p ∣ Nat.card (fixSubfield σ) ^ 6 - 1 :=
        fun σ hσp => dvd_pow_sub_one_of_cast_eq hK1 Nat.card_pos
          (card_fixSubfield_cast q.prime_p q.exponent_pos hK' hp hσp).symm hd6
      have hdvd : ∀ σ : K ≃+* K, orderOf σ = p →
          ¬ Nat.Coprime p (Nat.card (adjointGroup Tag.G2 (fixSubfield σ))) :=
        fun σ hσp => not_coprime_card_adjointG2_of_dvd_pow_six (fixSubfield σ) hp (hdf σ hσp)
      by_cases h2 : q.p = 2
      · have hK2 : Nat.card K = 2 ^ q.exponent := by rw [hK', h2]
        have hf2 : 2 ≤ q.exponent := by
          by_contra hlt
          have h1 : q.exponent = 1 := by have := q.exponent_pos; omega
          rw [TauCeti.PrimePower.card_def, h2, h1] at hq3
          omega
        by_cases hq8 : p = 3 ∧ q.exponent = 3
        · obtain ⟨rfl, hf3⟩ := hq8
          exact g2EightFieldCore K (by rw [hK2, hf3]; norm_num) x hxord hxo
        · have hk3 : ∀ σ : K ≃+* K, orderOf σ = p → 3 ≤ Nat.card (fixSubfield σ) := by
            intro σ hσp
            obtain ⟨hdvdf, hcard⟩ := SteinbergBT.card_fixSubfield Nat.prime_two (by omega) hK2 σ
            rw [hσp] at hdvdf hcard
            obtain ⟨m, hm⟩ := hdvdf
            have hm0 : 0 < m := by
              rcases Nat.eq_zero_or_pos m with rfl | h
              · omega
              · exact h
            rw [hm, Nat.mul_div_cancel_left _ hp.pos] at hcard
            by_cases hm1 : m = 1
            · exfalso
              have h63 := hdf σ hσp
              rw [hcard, hm1] at h63
              norm_num at h63
              rcases hp35 with rfl | rfl
              · exact hq8 ⟨rfl, by omega⟩
              · omega
            · rw [hcard]
              calc 3 ≤ 2 ^ 2 := by norm_num
                _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
          exact fieldCoreAt_G2_even hf2 K hK2 hp hk3 hdvd hxord hxo
      · by_cases h3 : q.p = 3
        · have hK3 : Nat.card K = 3 ^ q.exponent := by rw [hK', h3]
          have : CharP K ReeTag.G2.prime := by
            rw [show ReeTag.G2.prime = 3 from rfl]
            exact finite_field_prime_power_characteristic Nat.prime_three q.exponent_pos hK3
          exact fieldCoreAt_G2_three q.exponent_pos K hK3 hp (by omega) hdvd hxord hxo
        · have hNF := conj_normalForm_of_pointwise
            (odd_F4_and_nonexceptional_G2_automorphism_normal_form q.prime_p h2 q.exponent_pos K
              hK' .G2 (Or.inr ⟨rfl, h3⟩)).1
          exact fieldCoreAt_of_oddInnerField q.prime_p h2 q.exponent_pos K hK' hNF hp hdvd
            hxord hxo
    · exact Or.inl (elemAbelian_card_eq_one_of_not_dvd hp (not_dvd_card_adjointG2 K hp hpK hd6))
  exact isLocallyBalancedAbs_two_of_model e hp hinj hin' hout

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.G2Aux
