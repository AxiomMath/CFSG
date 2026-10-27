module

public import CFSG.CGT.PushingUpLit.SixThreeShort
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerOddAvg
public import CFSG.CGT.PushingUp.CampbellPair
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.CGT.PushingUpLit

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp
open scoped commutatorElement Pointwise

namespace SixThree

variable {G : Type} [Group G]

theorem exists_orderOf_two_of_ne_bot [Finite G] {Z : Subgroup G} (hZ : IsPGroup 2 Z)
    (hne : Z ≠ ⊥) : ∃ z ∈ Z, orderOf z = 2 := by
  have : Nontrivial Z := (Subgroup.nontrivial_iff_ne_bot Z).mpr hne
  obtain ⟨n, hn, hcard⟩ := hZ.nontrivial_iff_card.mp inferInstance
  have h2 : 2 ∣ Nat.card Z := by
    rw [hcard]
    exact dvd_pow_self 2 (Nat.pos_iff_ne_zero.mp hn)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Z) 2 h2
  exact ⟨x, x.2, by rw [← hx, Subgroup.orderOf_coe]⟩

theorem normal_omegaOneCenterIn (Q : Subgroup G) [Q.Normal] : (omegaOneCenterIn Q).Normal := by
  refine ⟨fun z hz g => ?_⟩
  obtain ⟨hzQ, hzc, hz2⟩ := CFSG.CGT.PushingUp.mem_omegaOneCenterIn_iff.mp hz
  refine CFSG.CGT.PushingUp.mem_omegaOneCenterIn_iff.mpr ⟨?_, fun k hk => ?_, ?_⟩
  · exact (inferInstance : Q.Normal).conj_mem z hzQ g
  · have hk' : g⁻¹ * k * g ∈ Q := by
      simpa using (inferInstance : Q.Normal).conj_mem k hk g⁻¹
    have h1 := hzc _ hk'
    calc k * (g * z * g⁻¹) = g * ((g⁻¹ * k * g) * z) * g⁻¹ := by group
      _ = g * (z * (g⁻¹ * k * g)) * g⁻¹ := by rw [h1]
      _ = g * z * g⁻¹ * k := by group
  · calc (g * z * g⁻¹) ^ 2 = g * z ^ 2 * g⁻¹ := conj_pow
      _ = 1 := by rw [hz2]; group

theorem exists_odd_orderOf_not_mem_centralizer [Finite G] {Y Q : Subgroup G} [Q.Normal]
    (hY : IsShortGroup ↥Y) (hQ2 : IsPGroup 2 Q) (hchar : Subgroup.centralizer (Q : Set G) ≤ Q) :
    ∃ a ∈ Y, Odd (orderOf a) ∧ a ∉ Subgroup.centralizer (Q : Set G) := by
  by_contra hcon
  push Not at hcon
  have hNo := SubTwo.noTwoQuotient_of_oResidualTwo hY.residual_eq
  have hK : Y ⊓ Subgroup.centralizer (Q : Set G) = Y := by
    refine eq_of_odd_orderOf_mem (K := Y ⊓ Subgroup.centralizer (Q : Set G)) hNo inf_le_left ?_ ?_
    · refine le_trans (le_inf Subgroup.le_normalizer ?_) Subgroup.inf_normalizer_le_normalizer_inf
      rw [Subgroup.normalizer_eq_top (Subgroup.centralizer (Q : Set G))]
      exact le_top
    · intro y hy hodd
      exact ⟨hy, hcon y hy hodd⟩
  have hYQ : Y ≤ Q := fun y hy => hchar (hK.ge hy).2
  have hY2 : IsPGroup 2 Y := hQ2.to_le hYQ
  have hbot : (⊥ : Subgroup G) = Y := by
    refine hNo ⊥ bot_le ?_ fun y hy => ?_
    · rw [Subgroup.normalizer_eq_top (⊥ : Subgroup G)]
      exact le_top
    · obtain ⟨k, hk⟩ := hY2 ⟨y, hy⟩
      refine ⟨k, ?_⟩
      have := congrArg Subtype.val hk
      simpa using this
  have hsub : Subsingleton ↥Y := by
    have : ¬ Nontrivial ↥Y := by
      rw [Subgroup.nontrivial_iff_ne_bot]
      exact not_not.mpr hbot.symm
    exact not_nontrivial_iff_subsingleton.mp this
  have h1 := hY.nonzero
  rw [Subgroup.eq_bot_of_subsingleton (shortC ↥Y), Subgroup.eq_bot_of_subsingleton (shortU ↥Y)]
    at h1
  exact lt_irrefl _ h1

theorem not_le_centralizer_omegaOneCenterIn [Finite G] {Y Q : Subgroup G} [Q.Normal]
    (hY : IsShortGroup ↥Y) (hQ2 : IsPGroup 2 Q) (hQU : ⁅Q, Y⁆ ≤ ⁅oTwoIn Y, Y⁆) {a : G}
    (haY : a ∈ Y) (hao : Odd (orderOf a)) (hane : a ∉ Subgroup.centralizer (Q : Set G)) :
    ¬ Y ≤ Subgroup.centralizer (omegaOneCenterIn Q : Set G) := by
  intro hYV
  set A := Subgroup.zpowers a with hA
  set U₁ : Subgroup G := ⁅Q, A⁆ with hU₁
  have hAY : A ≤ Y := Subgroup.zpowers_le.mpr haY
  have hAQ : A ≤ Subgroup.normalizer (Q : Set G) := by
    rw [Subgroup.normalizer_eq_top Q]
    exact le_top
  have hU₁A : A ≤ Subgroup.normalizer (U₁ : Set G) := Subgroup.normalizer_commutator_ge_right Q A
  have hU₁Q : U₁ ≤ Q := Subgroup.commutator_le_left Q A
  have hU₁U : U₁ ≤ ⁅oTwoIn Y, Y⁆ := (Subgroup.commutator_mono le_rfl hAY).trans hQU
  have hU₁2 : IsPGroup 2 U₁ := hQ2.to_le hU₁Q
  have hU₁comm : ∀ x ∈ U₁, ∀ y ∈ U₁, x * y = y * x := fun x hx y hy =>
    U_comm hY x (hU₁U hx) y (hU₁U hy)
  have hU₁ne : U₁ ≠ ⊥ := by
    intro h
    apply hane
    have hQA : Q ≤ Subgroup.centralizer (A : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact ((Subgroup.mem_centralizer_iff.mp (hQA hq)) a (Subgroup.mem_zpowers a)).symm
  have hcop1 : U₁ ≤ ⁅U₁, A⁆ :=
    commutator_le_commutator_commutator_of_odd hQ2 hao (hAQ (Subgroup.mem_zpowers a))
  have hcop2 : ⁅U₁, A⁆ ≤ U₁ := Subgroup.le_normalizer_iff_commutator_le_left.mp hU₁A
  have hU₁A_eq : ⁅U₁, A⁆ = U₁ := le_antisymm hcop2 hcop1
  have hdecomp := CFSG.QuasithinUnique.Setup.Layer.coprime_abelian_decomp U₁ A hU₁A
    (fun x y => Subtype.ext (hU₁comm x x.2 y y.2)) (coprime_card_zpowers_of_odd hao hU₁2)
  have hCbot : U₁ ⊓ Subgroup.centralizer (A : Set G) = ⊥ := by
    have hd := disjoint_iff.mp hdecomp.2
    rwa [hU₁A_eq, inf_eq_left.mpr inf_le_left] at hd
  have hZne : U₁ ⊓ Subgroup.centralizer (Q : Set G) ≠ ⊥ := by
    have : Group.IsNilpotent ↥Q := hQ2.isNilpotent
    have hnorm : (U₁.subgroupOf Q).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer (Subgroup.normalizer_commutator_ge_left Q A)
    have hne' : U₁.subgroupOf Q ≠ ⊥ := by
      intro h
      apply hU₁ne
      refine (Subgroup.eq_bot_iff_forall _).mpr fun x hx => ?_
      have hxQ : x ∈ Q := hU₁Q hx
      have hmem : (⟨x, hxQ⟩ : ↥Q) ∈ U₁.subgroupOf Q := hx
      rw [h, Subgroup.mem_bot] at hmem
      exact congrArg Subtype.val hmem
    obtain ⟨x, hx⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
      (Group.IsNilpotent.inf_center_ne_bot_of_normal hne')
    intro hbot
    apply hx
    have hxU : (x : ↥Q).1 ∈ U₁ := (Subgroup.mem_inf.mp x.2).1
    have hxc : (x : ↥Q).1 ∈ Subgroup.centralizer (Q : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have := Subgroup.mem_center_iff.mp (Subgroup.mem_inf.mp x.2).2 ⟨k, hk⟩
      exact congrArg Subtype.val this
    have : (x : ↥Q).1 ∈ U₁ ⊓ Subgroup.centralizer (Q : Set G) := ⟨hxU, hxc⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact Subtype.ext (Subtype.ext this)
  obtain ⟨z, hzmem, hz2⟩ := exists_orderOf_two_of_ne_bot (hQ2.to_le ((inf_le_left).trans hU₁Q))
    hZne
  have hzU : z ∈ U₁ := (Subgroup.mem_inf.mp hzmem).1
  have hzc : z ∈ Subgroup.centralizer (Q : Set G) := (Subgroup.mem_inf.mp hzmem).2
  have hzV : z ∈ omegaOneCenterIn Q := by
    refine CFSG.CGT.PushingUp.mem_omegaOneCenterIn_iff.mpr ⟨hU₁Q hzU, ?_, ?_⟩
    · exact fun k hk => Subgroup.mem_centralizer_iff.mp hzc k hk
    · rw [← hz2]
      exact pow_orderOf_eq_one z
  have hacomm : z * a = a * z := Subgroup.mem_centralizer_iff.mp (hYV haY) z hzV
  have hzA : z ∈ Subgroup.centralizer (A : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    exact ((Commute.zpow_left (show Commute a z from hacomm.symm) n).eq)
  have hz1 : z ∈ U₁ ⊓ Subgroup.centralizer (A : Set G) := ⟨hzU, hzA⟩
  rw [hCbot, Subgroup.mem_bot] at hz1
  rw [hz1, orderOf_one] at hz2
  exact absurd hz2 (by norm_num)

theorem step_two [Finite G] {Y Q : Subgroup G} [Q.Normal] (hY : IsShortGroup ↥Y)
    (hQ2 : IsPGroup 2 Q) (hchar : Subgroup.centralizer (Q : Set G) ≤ Q)
    (hQC : Q ≤ centralizerModCore Y) :
    ⁅Q, Y⁆ = ⁅oTwoIn Y, Y⁆ ∧ ⁅omegaOneCenterIn Q, Y⁆ = ⁅oTwoIn Y, Y⁆ ∧
      ⁅oTwoIn Y, Y⁆ ≤ omegaOneCenterIn Q ∧
      ¬ Y ≤ Subgroup.centralizer (omegaOneCenterIn Q : Set G) := by
  obtain ⟨a, haY, hao, hane⟩ := exists_odd_orderOf_not_mem_centralizer hY hQ2 hchar
  have hYQ : Y ≤ Subgroup.normalizer (Q : Set G) := by
    rw [Subgroup.normalizer_eq_top Q]
    exact le_top
  have hQle : ⁅Q, Y⁆ ≤ oTwoIn Y :=
    Subgroup.commutator_le.mpr fun q hq y hy => (hQC hq).2 y hy
  have hne : ⁅Q, Y⁆ ≠ ⊥ := by
    intro h
    apply hane
    have hQA : Q ≤ Subgroup.centralizer (Y : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact ((Subgroup.mem_centralizer_iff.mp (hQA hq)) a haY).symm
  have hQU : ⁅Q, Y⁆ = ⁅oTwoIn Y, Y⁆ := commutator_eq_U hY hQ2 hYQ hQle hne
  have hnot : ¬ Y ≤ Subgroup.centralizer (omegaOneCenterIn Q : Set G) :=
    not_le_centralizer_omegaOneCenterIn hY hQ2 hQU.le haY hao hane
  have hVnorm : (omegaOneCenterIn Q).Normal := normal_omegaOneCenterIn Q
  have hVQ : omegaOneCenterIn Q ≤ Q := CFSG.CGT.PushingUp.omegaOneCenterIn_le Q
  have hVY : Y ≤ Subgroup.normalizer (omegaOneCenterIn Q : Set G) := by
    rw [Subgroup.normalizer_eq_top (omegaOneCenterIn Q)]
    exact le_top
  have hVle : ⁅omegaOneCenterIn Q, Y⁆ ≤ oTwoIn Y :=
    ((Subgroup.commutator_mono hVQ le_rfl).trans hQU.le).trans (U_le_oTwoIn Y)
  have hVne : ⁅omegaOneCenterIn Q, Y⁆ ≠ ⊥ := by
    intro h
    apply hnot
    rw [Subgroup.commutator_comm] at h
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
  have hVU : ⁅omegaOneCenterIn Q, Y⁆ = ⁅oTwoIn Y, Y⁆ :=
    commutator_eq_U hY ((hQ2.to_le hVQ)) hVY hVle hVne
  refine ⟨hQU, hVU, ?_, hnot⟩
  rw [← hVU]
  exact Subgroup.commutator_le_left _ _

end SixThree

end CFSG.CGT.PushingUpLit
