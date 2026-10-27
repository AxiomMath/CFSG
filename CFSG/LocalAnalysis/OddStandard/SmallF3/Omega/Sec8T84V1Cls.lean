module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84Defs
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFCenter
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Basic

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem sec8t84v_inf_centralizer_eq_bot {G : Type} [Group G] [Finite G] {K U : Subgroup G}
    (hK : IsQuasisimple K) (hs : SmallF3StarQuotient (↥K ⧸ oddCore ↥K)) (hUK : U ≤ K)
    (hU : ∀ x ∈ U, x ^ 2 = 1) : U ⊓ centralizer (K : Set G) = ⊥ := by
  have hsimple : IsSimpleGroup (↥K ⧸ oddCore ↥K) := by
    rcases hs with h | h | h | h
    · exact (CFSG.LieType.Simplicity.fam_classical_converse (↥K ⧸ oddCore ↥K)
        ⟨.PSL, 2, 3, 2, h.statedClassicalModel_of_ne_zero (by norm_num)⟩).2.2
    · exact (CFSG.LieType.Simplicity.fam_classical_converse (↥K ⧸ oddCore ↥K)
        ⟨.PSL, 2, 3, 4, h.statedClassicalModel_of_ne_zero (by norm_num)⟩).2.2
    · exact (CFSG.LieType.Simplicity.fam_classical_converse (↥K ⧸ oddCore ↥K)
        ⟨.PSL, 3, 3, 1, h.statedClassicalModel_of_ne_zero (by norm_num)⟩).2.2
    · exact (CFSG.LieType.Simplicity.fam_classical_converse (↥K ⧸ oddCore ↥K)
        ⟨.PSU, 3, 3, 1, h.statedClassicalModel_of_ne_zero (by norm_num)⟩).2.2
  have hcen : Subgroup.center ↥K = oddCore ↥K := center_eq_oddCore_of_simple hK hsimple
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  obtain ⟨hxU, hxC⟩ := hx
  have hxK : x ∈ K := hUK hxU
  have hz : (⟨x, hxK⟩ : ↥K) ∈ Subgroup.center ↥K := by
    rw [Subgroup.mem_center_iff]
    intro a
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxC (a : G) a.2)
  rw [hcen] at hz
  have hdvd : orderOf (⟨x, hxK⟩ : ↥K) ∣ Nat.card (oddCore ↥K) :=
    (oddCore ↥K).orderOf_dvd_natCard hz
  have hodd : Odd (orderOf (⟨x, hxK⟩ : ↥K)) := (ff_odd_card_oddCore ↥K).of_dvd_nat hdvd
  rw [Subgroup.orderOf_mk x hxK] at hodd
  have hx2 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (hU x hxU)
  have h1 : orderOf x = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hx2 with h | h
    · exact h
    · rw [h] at hodd
      exact absurd hodd (by decide)
  exact orderOf_eq_one_iff.mp h1

theorem sec8t84v_cls (F : Sec8T84Base) {G : Type} [Group G] [Finite G] {t : G}
    {L S : Subgroup G} {z g : G} {B : Subgroup G} {γ : G} {K U : Subgroup G}
    (h : Sec8Gamma G t L S z g B γ K U) : IsOm5Q K ∨ IsOm6M K := by
  have hq : IsQuasisimple K := h.comp.isQuasisimple
  by_cases hF : InF K
  · have hS' : Sec3SettingLB G γ K :=
      sec3SettingLB_of_component h.ctx.toSec3SettingLB h.inv h.comp hF
    rcases F.hShapes G γ K hS' with h5 | h6 | h6m
    · exact Or.inl ⟨hq, h5⟩
    · exact (F.h6p G γ K hS' h6).elim
    · exact Or.inr ⟨hq, h6m⟩
  · exfalso
    have hs : SmallF3StarQuotient (↥K ⧸ oddCore ↥K) := by
      have h' := h.inFStar
      unfold InFStar IsFStarGroup at h'
      rcases h' with h' | ⟨-, h'⟩
      · exact absurd h' hF
      · exact h'
    have hshape : IsL29 K ∨ IsL281 K ∨ IsL3Eps3 K := by
      rcases hs with h' | h' | h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr (Or.inl h'))
      · exact Or.inr (Or.inr (Or.inr h'))
    have hbot : U ⊓ centralizer (K : Set G) = ⊥ :=
      sec8t84v_inf_centralizer_eq_bot hq hs h.U_le (fun x hx => h.U_e16.1.2 x hx)
    have hUN : U ≤ normalizer (K : Set G) := h.U_le.trans Subgroup.le_normalizer
    have hrank := (F.hAutF.rank_aut G K U hq hUN h.U_e16.1).1 hshape
    have h4 : 4 ≤ CFSG.Open.pRank 2 U :=
      CFSG.SectionRank.le_pRank (by norm_num) le_rfl h.U_e16.1 h.U_e16.2
    have h0 : CFSG.Open.pRank 2 (U ⊓ centralizer (K : Set G)) ≤ 0 := by
      rw [hbot]
      refine CFSG.SectionRank.pRank_le (by norm_num) fun E hE _ => ?_
      have : E = ⊥ := le_bot_iff.mp hE
      subst this
      simp
    omega

end CFSG.OddStandard.SmallF3.Omega
