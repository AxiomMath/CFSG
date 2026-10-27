module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cLieOutCharTwo
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.OrthOuterThreeAux.SympPrimeSubfieldOdd
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.Split
public import CFSG.RankThree.PartOne.KC.SymplecticSubfieldOuter

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1431c

open CFSG CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.Yardstones.Md0ec50421ce4
  CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
  CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.RankThree.PartTwo.KFacts CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.Sec66T CFSG.RankThree.PartOne.KCSpComm
  CFSG.RankThree.CASymplecticSubfield CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.ComponentClassification.CatLeaf CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Solomon.UniquenessMaximal
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross
  (symplectic_prime_subfield_fixed_group_and_full_centralizer_odd)
open CFSG.HardMathSupport.Dickson.Sec6.I923
open CFSG.HardMathSupport.Dickson.Sec6 (FamTits)
open CFSG.Sporadic.Schreier.Tits (titsD titsModelEquiv AT_Tits_derived_group_Schreier)
open scoped commutatorElement

variable {T Pc : TauCeti.CFSGIndex → Prop}

theorem typeLayer_fieldAut_psp_two_eight_card {N : ℕ} (hT : TypeOrd T N) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = 8) {σ : K ≃+* K} (hσ : orderOf σ = 3) :
    TypeLayer T (fieldAut 2 K σ) (N = 360) := by
  have hK' : Nat.card K = 2 ^ 3 := by rw [hK]; norm_num
  obtain ⟨-, -, -, -, -, hfixiff, -, -, hA6, -⟩ :=
    symplectic_prime_subfield_fixed_group_and_full_centralizer_odd
      (K := K) (r := 2) Nat.prime_two Nat.prime_three (by norm_num) (by norm_num) (by norm_num)
      le_rfl hK' σ hσ
  obtain ⟨-, ⟨eA⟩, -⟩ := hA6 ⟨rfl, by norm_num⟩
  have hD' : fixSubgroup (fieldAut 2 K σ) = subfieldFixedGroup K 2 σ :=
    Subgroup.ext fun x => (hfixiff x).symm
  have h5 : 5 ≤ Nat.card (Fin 6) := by rw [Nat.card_fin]; norm_num
  haveI hsA : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup h5
  have hcardA : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]
    decide
  set S : Subgroup (StatedProj (StatedSp 2 K)) :=
    ⁅subfieldFixedGroup K 2 σ, subfieldFixedGroup K 2 σ⁆ with hS
  haveI hs : IsSimpleGroup ↥S := eA.isSimpleGroup
  have hcardS : Nat.card ↥S = 360 := by rw [Nat.card_congr eA.toEquiv, hcardA]
  have hnab : ∃ a b : ↥S, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    letI : CommGroup ↥S := { (inferInstance : Group ↥S) with mul_comm := fun a b => hcon a b }
    have hprime : (Nat.card ↥S).Prime := IsSimpleGroup.prime_card
    rw [hcardS] at hprime
    exact absurd hprime (by norm_num)
  refine typeLayer_of_simple_commutator _ S (by rw [hD']) hs hnab fun hST => ?_
  rw [← hT hST, hcardS]

section Tits


theorem lieSOut_tits_of_inner : TypeOuterAt T Pc FamTits := by
  intro S _ _ _ _ ⟨d, hv⟩ hF _ ⟨e⟩ α hα hp
  cases d with
  | tits =>
    exfalso
    obtain ⟨e'⟩ := titsModelEquiv S 2 1 (CFSG.Blueprint.LieModel.reeTitsModel
      (CFSG.HardMathSupport.Dickson.Sec6.blueprintLieModel_tits hv e) (by decide)).2
    have hβ3 : MulAut.congr e' α ^ 3 = 1 := by rw [← map_pow, hp.1, map_one]
    obtain ⟨hO, -⟩ := AT_Tits_derived_group_Schreier
    obtain ⟨k, hk⟩ := hO (QuotientGroup.mk' (inner titsD) (MulAut.congr e' α))
    have h1 : orderOf (QuotientGroup.mk' (inner titsD) (MulAut.congr e' α)) ∣ 3 :=
      orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hβ3, map_one])
    have h2 : orderOf (QuotientGroup.mk' (inner titsD) (MulAut.congr e' α)) ∣ 2 ^ k :=
      orderOf_dvd_of_pow_eq_one hk
    have h3 := Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_right k (by norm_num)) h1 h2
    have hin : MulAut.congr e' α ∈ inner titsD :=
      (QuotientGroup.eq_one_iff _).1 (orderOf_eq_one_iff.1 h3)
    exact hα ((mem_innAutDerived_congr e').mp (inner_le_innAutDerived _ hin))
  | _ => exact hF.elim

end Tits

end CFSG.LocalAnalysis.GLTheoremA.H1431c

end
