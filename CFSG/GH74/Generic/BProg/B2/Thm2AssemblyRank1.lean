module

public import CFSG.GH74.Generic.BProg.B2.Thm2AssemblyList
import CFSG.GH74.Generic.BProg.B2.Thm2Comp
public import CFSG.LocalAnalysis.ComponentInitial.QuasisimpleRankOne

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup

namespace Thm2AssemblyRank1

open CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification

theorem rankOne_data {Y : Type} [Group Y] [Finite Y] {J : Subgroup Y} (hJ : IsQuasisimple ↥J)
    (hr : pRank 2 ↥J ≤ 1) :
    ∃ z a : Y, z ∈ J ∧ a ∈ J ∧ orderOf z = 2 ∧ orderOf a = 4 ∧ (∀ g ∈ J, g * z = z * g) ∧
      (∀ y ∈ J, orderOf y = 2 → y = z) ∧
      (∀ c ∈ J, (∀ g ∈ J, g * c = c * g) → orderOf c ≠ 4) := by
  obtain ⟨-, ⟨z, hz, hzu⟩, hzc, hquat⟩ := quasisimple_rank_one_unique_central_involution hJ hr
  have hJ' : Open.IsQuasisimple ↥J := (CatalogueBAlternating.quasisimple_iff_native).1 hJ
  have hr' : Open.pRank 2 (⊤ : Subgroup ↥J) ≤ 1 := by
    rw [← SectionRank.pRank_eq_open_pRank_top]; exact hr
  obtain ⟨-, hfac⟩ := AschbacherKnownGroup.rankOne_quotient_center hJ' hr'
  obtain ⟨r, hr3, ⟨e⟩⟩ := hquat default
  have : NeZero (2 ^ (r - 2)) := ⟨(Nat.two_pow_pos _).ne'⟩
  let a₀ : ↥J := (e.symm (QuaternionGroup.xa 0)).1
  have ha₀ : orderOf a₀ = 4 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact QuaternionGroup.orderOf_xa 0
  refine ⟨z, a₀, z.2, a₀.2, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe]; exact hz
  · rw [Subgroup.orderOf_coe]; exact ha₀
  · intro g hg
    have := Subgroup.mem_center_iff.1 (hzc z hz) ⟨g, hg⟩
    exact congrArg Subtype.val this
  · intro y hy hy2
    have : (⟨y, hy⟩ : ↥J) = z := hzu ⟨y, hy⟩ (by
      show orderOf (⟨y, hy⟩ : ↥J) = 2
      rw [Subgroup.orderOf_mk]; exact hy2)
    exact congrArg Subtype.val this
  · intro c hc hcc hc4
    have hcen : (⟨c, hc⟩ : ↥J) ∈ center ↥J := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hcc g g.2)
    have hdvd : orderOf (⟨(⟨c, hc⟩ : ↥J), hcen⟩ : center ↥J) ∣ Nat.card (center ↥J) :=
      orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk, hc4] at hdvd
    have hpos : Nat.card (center ↥J) ≠ 0 := Nat.card_pos.ne'
    have h2 : 2 ≤ (Nat.card (center ↥J)).factorization 2 :=
      (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hpos).1 (by simpa using hdvd)
    omega

theorem two_le_pRank_of_involutions {Y : Type} [Group Y] [Finite Y] (R : Subgroup Y) {e₁ e₂ : Y}
    (h₁ : e₁ ∈ R) (h₂ : e₂ ∈ R) (h11 : e₁ * e₁ = 1) (h22 : e₂ * e₂ = 1) (hne1 : e₁ ≠ 1)
    (hne2 : e₂ ≠ 1) (hne : e₁ ≠ e₂) (hc : e₁ * e₂ = e₂ * e₁) : 2 ≤ pRank 2 ↥R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let a : ↥R := ⟨e₁, h₁⟩
  let b : ↥R := ⟨e₂, h₂⟩
  have hV := GorensteinWalter.isKleinFour_kleinFourOfCommutingInvolutions a b
    (Subtype.ext h11) (Subtype.ext h22) (fun h => hne1 (congrArg Subtype.val h))
    (fun h => hne2 (congrArg Subtype.val h)) (fun h => hne (congrArg Subtype.val h))
    (Subtype.ext hc)
  set V := GorensteinWalter.kleinFourOfCommutingInvolutions a b (Subtype.ext h11) (Subtype.ext h22)
    (Subtype.ext hc) with hVdef
  have hel : IsElementaryAbelian 2 ↥V :=
    { toIsMulCommutative := hV.isMulCommutative
      exponent_dvd_p := by rw [hV.exponent_two] }
  exact B2.Thm2Comp.le_pRank_of_isElementaryAbelian hel (by rw [hV.card_four]; norm_num)

end Thm2AssemblyRank1

open Thm2AssemblyRank1
open CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification

theorem two_le_pRank_sup_of_rankOne {Y : Type} [Group Y] [Finite Y] {J₁ J₂ : Subgroup Y}
    (h₁ : IsComponent J₁) (h₂ : IsComponent J₂) (hne : J₁ ≠ J₂) (hr₁ : pRank 2 ↥J₁ ≤ 1)
    (hr₂ : pRank 2 ↥J₂ ≤ 1) : 2 ≤ pRank 2 ↥(J₁ ⊔ J₂) := by
  have hc : ∀ a ∈ J₁, ∀ b ∈ J₂, a * b = b * a := by
    intro a ha b hb
    have hle : J₁ ≤ centralizer (J₂ : Set Y) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.1
        ((CFSG.LocalCores.distinct_components_commute h₁ h₂).resolve_left hne)
    exact (Subgroup.mem_centralizer_iff.1 (hle ha) b hb).symm
  obtain ⟨z₁, a₁, hz₁, ha₁, hz₁o, ha₁o, hz₁c, hz₁u, hc₁⟩ := rankOne_data h₁.1 hr₁
  obtain ⟨z₂, a₂, hz₂, ha₂, hz₂o, ha₂o, hz₂c, hz₂u, hc₂⟩ := rankOne_data h₂.1 hr₂
  have hsq : ∀ {z : Y}, orderOf z = 2 → z * z = 1 := by
    intro z hz
    have := pow_orderOf_eq_one z
    rwa [hz, pow_two] at this
  have hne1 : ∀ {z : Y}, orderOf z = 2 → z ≠ 1 := by
    intro z hz h
    rw [h, orderOf_one] at hz
    omega
  have hJ₁ : J₁ ≤ J₁ ⊔ J₂ := le_sup_left
  have hJ₂ : J₂ ≤ J₁ ⊔ J₂ := le_sup_right
  by_cases hzz : z₁ = z₂
  ·
    subst hzz
    have ha₁sq : a₁ * a₁ = z₁ := by
      refine hz₁u (a₁ * a₁) (J₁.mul_mem ha₁ ha₁) ?_
      rw [← pow_two, orderOf_pow_of_dvd (by norm_num) (by rw [ha₁o]; norm_num), ha₁o]
    have ha₂sq : a₂ * a₂ = z₁ := by
      refine hz₂u (a₂ * a₂) (J₂.mul_mem ha₂ ha₂) ?_
      rw [← pow_two, orderOf_pow_of_dvd (by norm_num) (by rw [ha₂o]; norm_num), ha₂o]
    have hcomm12 : a₁ * a₂ = a₂ * a₁ := hc a₁ ha₁ a₂ ha₂
    have hu2 : (a₁ * a₂) * (a₁ * a₂) = 1 := by
      calc (a₁ * a₂) * (a₁ * a₂) = a₁ * (a₂ * a₁) * a₂ := by group
        _ = a₁ * (a₁ * a₂) * a₂ := by rw [← hcomm12]
        _ = (a₁ * a₁) * (a₂ * a₂) := by group
        _ = z₁ * z₁ := by rw [ha₁sq, ha₂sq]
        _ = 1 := hsq hz₁o
    have ha₁J₂ : a₁ ∉ J₂ := by
      intro hmem
      exact hc₁ a₁ ha₁ (fun g hg => hc g hg a₁ hmem) ha₁o
    have hu1 : a₁ * a₂ ≠ 1 := by
      intro h
      apply ha₁J₂
      have : a₁ = a₂⁻¹ := eq_inv_of_mul_eq_one_left h
      rw [this]; exact J₂.inv_mem ha₂
    have huz : a₁ * a₂ ≠ z₁ := by
      intro h
      apply ha₁J₂
      have h' : a₁ * a₂ = a₂ * a₂ := by rw [h, ha₂sq]
      have : a₁ = a₂ := mul_right_cancel h'
      rw [this]; exact ha₂
    refine two_le_pRank_of_involutions _ (e₁ := z₁) (e₂ := a₁ * a₂) (hJ₁ hz₁)
      ((J₁ ⊔ J₂).mul_mem (hJ₁ ha₁) (hJ₂ ha₂)) (hsq hz₁o) hu2 (hne1 hz₁o) hu1
      (fun h => huz h.symm) ?_
    calc z₁ * (a₁ * a₂) = (z₁ * a₁) * a₂ := by group
      _ = (a₁ * z₁) * a₂ := by rw [hz₁c a₁ ha₁]
      _ = a₁ * (z₁ * a₂) := by group
      _ = a₁ * (a₂ * z₁) := by rw [hc z₁ hz₁ a₂ ha₂]
      _ = (a₁ * a₂) * z₁ := by group
  · exact two_le_pRank_of_involutions _ (e₁ := z₁) (e₂ := z₂) (hJ₁ hz₁) (hJ₂ hz₂) (hsq hz₁o)
      (hsq hz₂o) (hne1 hz₁o) (hne1 hz₂o) hzz (hc z₁ hz₁ z₂ hz₂)

theorem rankOneRecog :
    RankOneRecog := by
  intro J _ _ hq hr
  have hJ' : Open.IsQuasisimple J := (CatalogueBAlternating.quasisimple_iff_native).1 hq
  have hr' : Open.pRank 2 (⊤ : Subgroup J) ≤ 1 := by
    rw [← SectionRank.pRank_eq_open_pRank_top]; exact hr
  obtain ⟨⟨S, n, hn, hS⟩, -⟩ := AschbacherKnownGroup.rankOne_quotient_center hJ' hr'
  obtain ⟨-, ⟨z, hz, -⟩, hzc, -⟩ := quasisimple_rank_one_unique_central_involution hq hr
  have : IsSimpleGroup (J ⧸ center J) := hq.2.1
  rcases CFSG.Milestones.lr_dihedral_simple_recognition (J ⧸ center J) hq.2.2 S n hn hS with
    ⟨p, f, hp, hp2, hf, hmodel⟩ | hA7
  · exact Or.inl ⟨p, f, hp, hp2, hf, Or.inl ⟨by decide, hmodel⟩⟩
  · refine Or.inr ⟨hA7, ?_⟩
    intro hbot
    have hzbot := hzc z hz
    rw [hbot, Subgroup.mem_bot] at hzbot
    rw [hzbot, orderOf_one] at hz
    omega

end CFSG.GH74.Generic.BProg.B2
