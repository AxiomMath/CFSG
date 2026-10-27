module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I107X2TwF4
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I107X2F4
public import CFSG.LocalAnalysis.SectionRank.DerivedQuotient

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I107X2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Ree CFSG.LieType.Chevalley CFSG.Open CFSG.SectionRank
  CFSG.Assembly CFSG.GH74.Filter.Lie CFSG.LieType.BorelTits


theorem twoRankLow_twF4_holds (S : Type) [Group S] [Finite S] (lab : GLALabel) (hS : IsSimpleGroup S)
    (hrk : Rk2IsLabel S lab) (ht : lab.tag = .twF4) :
    twoRankLow107 lab ≤ CFSG.Open.pRank 2 (⊤ : Subgroup S) := by
  obtain ⟨tag, rank, n⟩ := lab
  obtain rfl : tag = .twF4 := ht
  have hlab := rk2IsLabel_inLambda2 hrk
  have hraw := rk2IsLabel_rawDatum hrk
  have hodd : Odd n := hlab.2.2.1
  have h3 : 3 ≤ n := hlab.2.2.2
  obtain ⟨k, hk⟩ := hodd
  subst hk
  have hk1 : (2 * k + 1 - 1) / 2 = k := by omega
  dsimp only [GLARawDatum, CFSG.Assembly.LargeEvenRawDatum,
    CFSG.Assembly.LargeEvenRecipeTwF4Inherited] at hraw
  rw [hk1] at hraw
  obtain ⟨K, hf, hfin, hK, hQ⟩ := hraw
  obtain ⟨-, hna, ⟨θ⟩⟩ := hQ
  have ha : 1 ≤ k := by omega
  haveI : CharP K 2 := charP_two_of_card' hK
  haveI : CharP K ReeTag.F4.prime := inferInstanceAs (CharP K 2)
  have e0 : LargeEvenCenterQuot (LargeEvenTwF4H k K) ≃*
      DerivedCentralQuotient (reeFixedGroup Tag.F4 K reeF4Perm
        (fun i => if i ∈ reeF4Long then 2 ^ k else 2 ^ (k + 1))) :=
    (CFSG.StandardType.centerQuot_twF4H_equiv K k).some
  have hH : reeFixedGroup Tag.F4 K reeF4Perm (fun i => if i ∈ reeF4Long then 2 ^ k else 2 ^ (k + 1)) =
      (reeFixed ReeTag.F4 K k).map (adjointGroup Tag.F4 K).subtype :=
    reeFixedGroup_eq_map_reeFixed (t := ReeTag.F4) (K := K) (a := k)
  let eH := (MulEquiv.subgroupCongr hH).trans
    (((reeFixed ReeTag.F4 K k).equivMapOfInjective _ (adjointGroup Tag.F4 K).subtype_injective).symm)
  haveI : Finite (LargeEvenCenterQuot (LargeEvenTwF4H k K)) := Finite.of_equiv _ θ.toEquiv
  haveI : Finite (DerivedCentralQuotient (reeFixedGroup Tag.F4 K reeF4Perm
      (fun i => if i ∈ reeF4Long then 2 ^ k else 2 ^ (k + 1)))) := Finite.of_equiv _ e0.toEquiv
  have hholds : Holds (reeFixed ReeTag.F4 K k) 2 :=
    holds_reeFixed (t := ReeTag.F4) (K := K) (a := k)
  obtain ⟨Sy, hSy⟩ := exists_sylow_reeFixed (t := ReeTag.F4) (K := K) (a := k)
  have hSy_le : (Sy : Subgroup (reeFixed ReeTag.F4 K k)) ≤ commutator (reeFixed ReeTag.F4 K k) := by
    intro x hx
    have hx' : x ∈ (nativeData ReeTag.F4.tag K).U.comap (reeFixed ReeTag.F4 K k).subtype := by
      rw [← hSy]
      exact hx
    have hU : (x : adjointGroup ReeTag.F4.tag K) ∈ (nativeData ReeTag.F4.tag K).U := hx'
    have hD := reeFixed_U_le_derived ReeTag.F4 K k ha hK x hU x.2
    obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.1 hD
    have hzx' : z = x := Subtype.ext hzx
    rw [← hzx']
    exact hz
  have hpR := pRank_derivedCentralQuotient_eq (p := 2)
    (reeFixedGroup Tag.F4 K reeF4Perm (fun i => if i ∈ reeF4Long then 2 ^ k else 2 ^ (k + 1))) eH
    hholds Sy hSy_le
  rw [CFSG.LocalAnalysis.GLTheoremA.I107L.pRank_eq_of_quotient θ hna,
    CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 2) e0, hpR]
  exact twF4_pRank_ge ha hK

end CFSG.LocalAnalysis.GLTheoremA.I107X2

end
