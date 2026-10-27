module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Thm54Reach.Inputs

public section

namespace CFSG.EvenSporadicStandard.Induction.Thm54Reach

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Assembly.LowTwoRank
  CFSG.EvenSporadicStandard.Solomon78 CFSG.EvenSporadicStandard.Induction
  CFSG.ComponentClassification.CatLeaf CFSG.ComponentClassification.CatFC
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.GSThmB.QPUSpor (sporOrder)

theorem sporOrder_ru : sporOrder .Ru = 145926144000 := by
  decide +kernel

theorem reach_of_catalog (I : CatInputs) {Y : Type} [Group Y] [Finite Y] {N' : Subgroup Y}
    (hN : FStarSimple N') (hidx : N'.index ≤ 2) (hcat : CFSG.Blueprint.Catalog ↥N')
    {P : Subgroup Y} (hP : SolStd P) (hq : CFSG.IsQuasisimple ↥P)
    (hT : Sol78Thm54Types (↥P ⧸ center ↥P)) (h29 : ¬ 29 ∣ Nat.card (↥P ⧸ center ↥P)) :
    (Sol78Thm54Types ↥N' ∧ ¬ 29 ∣ Nat.card ↥N') ∨ (SuzukiModel ↥P 2 3 ∧ IsSporadic ↥N' .Ru) := by
  have hNn := hN.normal
  have hSimple := hN.isSimpleGroup
  have hna := hN.nonabelian
  have hO := I.arm.order
  have hPN : P ≤ N' := Hyp.le_of_perfect_of_index_le_two hidx hq.1
  obtain ⟨t, ht2, hcomp⟩ := hP.exists_involution
  obtain ⟨σ, D, hσ, hD, hin, ⟨e⟩, hDP⟩ := exists_fixedComponent_conjNormal' hN ht2 hcomp hPN
  have eQ : ↥D ⧸ center ↥D ≃* ↥P ⧸ center ↥P := centerQuotientEquiv e
  have hc : Thm54Order (Nat.card (↥P ⧸ center ↥P)) := thm54Order_of_types hO hT
  have hcD : Nat.card (↥D ⧸ center ↥D) = Nat.card (↥P ⧸ center ↥P) :=
    Nat.card_congr eQ.toEquiv
  rcases catalog_fixed_component I.arm.gls I.arm.evenInner I.arm.evenOuter hna hcat hσ hD with
    ⟨n, k, -, hk5, -, -, -, ⟨eA⟩⟩ | ⟨hodd, hOddD⟩ | ⟨heven, hout, -⟩ | ⟨s, ⟨es⟩⟩
  ·
    exfalso
    haveI : Nontrivial (Fin k) := Fin.nontrivial_iff_two_le.2 (by omega)
    have hk : Nat.card (↥D ⧸ center ↥D) = k.factorial / 2 := by
      rw [Nat.card_congr eA.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    exact hc.ne_factorial_div_two hk5 (hk.symm.trans hcD)
  ·
    exfalso
    rcases odd_arm I.arm.gls hodd hσ hD with hOddD' | hL
    · exact not_oddLieType_of_thm54Types hO (thm54Types_of_mulEquiv eQ.symm hT) hOddD'
    · have hadmL : StatedLieAdmissible .PSL 2 2 3 :=
        ⟨Nat.prime_two, by norm_num, le_rfl, by decide, by decide⟩
      obtain ⟨-, h1, -⟩ := hO _ .PSL 2 2 3 hadmL hL
      have h504 : Nat.card ↥D = 504 := by
        simp only [lieOrderDivisor, lieOrderNumerator] at h1
        norm_num [Finset.Icc_self] at h1
        omega
      have hle : Nat.card (↥D ⧸ center ↥D) ≤ Nat.card ↥D :=
        Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _)
      have hge := hc.ge
      omega
  ·
    left
    exact evenArm_result I.even hO hSimple hna heven hσ hout hD
      (fixedCentralizerTwoFree_of_component I.arm.evenInner heven hP hq hPN hDP) e hq
      (odd_card_center_of_evenLie I.arm.evenInner heven hP hq hPN) hT h29
  ·
    obtain ⟨hdvd, hrowIn, hrowOut⟩ := I.arm.table hSimple hna es hσ hD
    rw [hcD] at hdvd hrowIn hrowOut
    rw [← sporOrder_eq_sporOrd] at hdvd
    by_cases hsM : s = .M
    · subst hsM
      exfalso
      have hinner : σ ∈ (MulAut.conj : ↥N' →* MulAut ↥N').range := by
        by_contra hnot
        exact hrowOut hnot
      exact hc.not_monster_row (hrowIn hinner)
    · have hrow : SporadicInnerRow s (Nat.card (↥P ⧸ center ↥P)) ∨
          SporadicOuterRow s (Nat.card (↥P ⧸ center ↥P)) := by
        by_cases hinner : σ ∈ (MulAut.conj : ↥N' →* MulAut ↥N').range
        · exact Or.inl (hrowIn hinner)
        · exact Or.inr (hrowOut hinner)
      obtain rfl := hc.spor hsM hdvd hrow
      right
      have hinner : σ ∈ (MulAut.conj : ↥N' →* MulAut ↥N').range := by
        by_contra hnot
        exact hrowOut hnot
      have htN : t ∈ N' := hin.1 hinner
      have hNcard : Nat.card ↥N' = 145926144000 := by
        rw [Nat.card_congr es.toEquiv, I.cardAll .Ru, sporOrder_ru]
      have hPcard : Nat.card (↥P ⧸ center ↥P) ∣ Nat.card ↥P :=
        Subgroup.card_quotient_dvd_card _
      have hc29 : Nat.card (↥P ⧸ center ↥P) = 29120 :=
        hc.ru (hPcard.trans (hNcard ▸ Subgroup.card_dvd_of_le hPN)) h29
      have hSz : SuzukiModel (↥P ⧸ center ↥P) 2 3 := suzukiModel_of_types_of_card_eq hO hT hc29
      let u : ↥N' := ⟨t, htN⟩
      have hu : orderOf u = 2 := by
        rw [Subgroup.orderOf_mk]
        exact ht2
      have hXperf : Group.IsPerfect ↥(P.subgroupOf N') := by
        haveI : Group.IsPerfect ↥P := hq.1
        exact Group.IsPerfect.ofSurjective
          (f := (Subgroup.subgroupOfEquivOfLe hPN).symm.toMonoidHom)
          (Subgroup.subgroupOfEquivOfLe hPN).symm.surjective
      have hXu : ∀ x ∈ P.subgroupOf N', x * u = u * x := by
        intro x hx
        have hxP : (x : Y) ∈ P := hx
        have := mem_centralizer_singleton_iff.1 (hcomp.1 hxP)
        exact Subtype.ext this
      have hXcard : Nat.card ↥(P.subgroupOf N') = Nat.card ↥P :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPN).toEquiv
      have hdvdP : 29120 ∣ Nat.card ↥(P.subgroupOf N') := by
        rw [hXcard, ← hc29]
        exact hPcard
      have hPeq : Nat.card ↥P = 29120 := by
        rw [← hXcard]
        exact I.ru ⟨es⟩ hu hXperf hXu hdvdP
      have hZ : Nat.card ↥(center ↥P) = 1 := by
        have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (center ↥P)
        rw [hPeq, hc29] at h
        omega
      have hZbot : center ↥P = ⊥ := Subgroup.eq_bot_of_card_eq _ hZ
      exact ⟨suzukiModel_of_mulEquiv'
        ((QuotientGroup.quotientMulEquivOfEq hZbot).trans QuotientGroup.quotientBot) hSz, ⟨es⟩⟩

end CFSG.EvenSporadicStandard.Induction.Thm54Reach
