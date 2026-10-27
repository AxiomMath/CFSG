module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census424Rest.Simple168
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census424Rest.TypeL3Two
public import CFSG.RankThree.PartTwo.Sec11.FieldCentRigid82
public import CFSG.RankThree.PartTwo.Sec4.Item424ProofBasic
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Census424Rest

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projSL)

theorem isSimpleGroup_of_quasisimple_center_bot {X : Type} [Group X] (hq : CFSG.IsQuasisimple X)
    (hZ : Subgroup.center X = ⊥) : IsSimpleGroup X := by
  obtain ⟨-, hs, -⟩ := hq
  have e : X ≃* X ⧸ Subgroup.center X :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm
  exact MulEquiv.isSimpleGroup e

theorem exists_mul_ne_of_quasisimple {X : Type} [Group X] (hq : CFSG.IsQuasisimple X) :
    ∃ a b : X, a * b ≠ b * a := by
  obtain ⟨-, -, a, b, hab⟩ := hq
  by_contra h
  push Not at h
  apply hab
  obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h a' b']

theorem nonempty_equiv_projSL_three_two_of_card_504 {C : Type} [Group C] [Finite C]
    (hcard : Nat.card C = 504) {c : C} (hc : c ∈ Subgroup.center C) (hc3 : orderOf c = 3)
    {K : Subgroup C} (hK : K ∈ thetaComponents 3 C)
    (hT : Sec11.IsType424 (K ⧸ aschbacherSolvableCore 3 K)) :
    Nonempty (K ⧸ aschbacherSolvableCore 3 K ≃* projSL 3 (GaloisField 2 1)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, -, hq⟩ := hK
  have hZQ : Subgroup.center (K ⧸ aschbacherSolvableCore 3 K) = ⊥ :=
    Sec11.FieldCentRigid82.center_eq_bot_of_isType424 hT
  have hc3' : c ^ 3 = 1 := by rw [← hc3]; exact pow_orderOf_eq_one c
  have hcomm : ∀ k : C, c * k = k * c := fun k => (Subgroup.mem_center_iff.mp hc k).symm
  have hcK : c ∉ K := by
    intro hcK
    have := Item424Proof.eq_one_of_mem_of_commute (K := K) hZQ hcK (fun k _ => hcomm k) hc3'
    rw [this, orderOf_one] at hc3
    omega
  have hinf : K ⊓ Subgroup.zpowers c = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxK, hxc⟩
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxc
    rw [Subgroup.mem_bot]
    have h3 : c ^ (3 : ℤ) = 1 := by rw [zpow_ofNat]; exact hc3'
    have hmod : c ^ j = c ^ (j % 3) := zpow_eq_zpow_emod j h3
    have hr : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2 := by omega
    rcases hr with h0 | h1 | h2
    · rw [hmod, h0, zpow_zero]
    · exfalso
      rw [hmod, h1, zpow_one] at hxK
      exact hcK hxK
    · exfalso
      rw [hmod, h2] at hxK
      apply hcK
      have : c = (c ^ (2 : ℤ)) ^ (2 : ℤ) := by
        rw [← zpow_mul, show (2 : ℤ) * 2 = 1 + 3 by norm_num, zpow_add, h3, mul_one, zpow_one]
      rw [this]
      exact Subgroup.zpow_mem _ hxK _
  have hnorm : (Subgroup.zpowers c).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    have : g * c ^ j * g⁻¹ = c ^ j := by
      have hcg : Commute g c := (hcomm g).symm
      rw [(Commute.zpow_right hcg j).eq]
      group
    rw [this]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers c) _
  let f : K →* C ⧸ Subgroup.zpowers c := (QuotientGroup.mk' (Subgroup.zpowers c)).comp K.subtype
  have hinj : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hx' : (x : C) ∈ Subgroup.zpowers c := by
      have : QuotientGroup.mk' (Subgroup.zpowers c) (x : C) = 1 := hx
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
    have : (x : C) ∈ K ⊓ Subgroup.zpowers c := ⟨x.2, hx'⟩
    rw [hinf, Subgroup.mem_bot] at this
    exact Subtype.ext this
  have hKd : Nat.card K ∣ 168 := by
    have h1 := Subgroup.card_dvd_of_injective f hinj
    have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.zpowers c)
    rw [hcard, Nat.card_zpowers, hc3] at h2
    have : Nat.card (C ⧸ Subgroup.zpowers c) = 168 := by omega
    rwa [this] at h1
  have hQd : Nat.card (K ⧸ aschbacherSolvableCore 3 K) ∣ 168 :=
    (Subgroup.card_quotient_dvd_card _).trans hKd
  have hsimple := isSimpleGroup_of_quasisimple_center_bot hq hZQ
  have hnab := exists_mul_ne_of_quasisimple hq
  have h3 : 3 ∣ Nat.card (K ⧸ aschbacherSolvableCore 3 K) :=
    Item424Proof.three_dvd_card_of_isType424 hT
  have h168 := card_eq_168_of_simple hnab hQd h3
  exact nonempty_equiv_projSL_three_two_of_type424 hT h168

end CFSG.AGLEmbeddingD2.Wilson.Census424Rest
