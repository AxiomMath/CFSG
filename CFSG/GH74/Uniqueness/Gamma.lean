module

public import CFSG.GH74.Uniqueness.Statements
public import CFSG.GH74.KGH
public import CFSG.LocalAnalysis.SectionRank.Framework.SylowRank

public section

namespace CFSG.GH74.Uniqueness

open Subgroup Blueprint

section Embedded

variable {X : Type*} [Group X]

theorem isStronglyEmbeddedOrder_of_isStronglyEmbedded {M : Subgroup X}
    (h : IsStronglyEmbedded M) : CFSG.BenderSuzuki.IsStronglyEmbeddedOrder M := by
  refine ⟨h.1, h.2.1, fun g hg => ?_⟩
  have := h.2.2 g⁻¹ (fun hginv => hg (M.inv_mem_iff.mp hginv))
  simpa only [CFSG.conjugate, inv_inv] using this

theorem isStronglyEmbedded_of_isStronglyEmbeddedOrder {M : Subgroup X}
    (h : CFSG.BenderSuzuki.IsStronglyEmbeddedOrder M) : IsStronglyEmbedded M := by
  refine ⟨h.1, h.2.1, fun g hg => ?_⟩
  have := h.2.2 g⁻¹ (fun hginv => hg (M.inv_mem_iff.mp hginv))
  simpa only [CFSG.conjugate, inv_inv] using this

end Embedded

section Gamma

variable {G : Type*} [Group G] [Finite G]

theorem gammaElem_le_gammaZero (S : Subgroup G) : gammaElem S ≤ gammaZero S := by
  refine iSup_le fun E => iSup_le fun hES => iSup_le fun _ => iSup_le fun h2 =>
    iSup_le fun h3 => ?_
  refine le_iSup_of_le E (le_iSup_of_le hES (le_iSup_of_le h2 ?_))
  refine le_iSup_of_le ?_ le_rfl
  exact h3.trans (CFSG.RankThreeCoreUniqueness.Helpers.pRank_mono 2 (by decide)
    (le_sup_right : centralizer (E : Set G) ⊓ S ≤ E ⊔ (centralizer (E : Set G) ⊓ S)))

theorem gammaZero_le_gamma_two (S : Subgroup G) :
    gammaZero S ≤ Open.properTwoGenCoreGamma S 2 := by
  refine iSup_le fun Q => iSup_le fun hQS => iSup_le fun h2 => iSup_le fun _ => ?_
  exact le_iSup_of_le Q (le_iSup_of_le hQS (le_iSup_of_le h2 le_rfl))

theorem odd_card_of_pRank_two_eq_zero (H : Subgroup G) (h : Open.pRank 2 H = 0) :
    Odd (Nat.card H) := by
  by_contra hne
  have hev : 2 ∣ Nat.card H := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hne)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 hev
  have ht2 : orderOf (t : G) = 2 := (Subgroup.orderOf_coe t).trans ht
  have ht2' : (t : G) ^ 2 = 1 := by rw [← ht2]; exact pow_orderOf_eq_one _
  have hle : Subgroup.zpowers (t : G) ≤ H := by
    rw [Subgroup.zpowers_le]
    exact t.2
  have hE : Open.IsElemAbelian 2 (Subgroup.zpowers (t : G)) := by
    refine ⟨inferInstance, fun x hx => ?_⟩
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ht2', one_zpow]
  have hcard : Nat.card (Subgroup.zpowers (t : G)) = 2 ^ 1 := by
    rw [Nat.card_zpowers, ht2, pow_one]
  have := CFSG.SectionRank.le_pRank (p := 2) (by decide) hle hE hcard
  omega

theorem isStronglyEmbedded_gamma_one (S : Sylow 2 G) (h1 : 1 ≤ Open.pRank 2 (S : Subgroup G))
    (hne : Open.properTwoGenCoreGamma (S : Subgroup G) 1 ≠ ⊤) :
    IsStronglyEmbedded (Open.properTwoGenCoreGamma (S : Subgroup G) 1) := by
  set Γ := Open.properTwoGenCoreGamma (S : Subgroup G) 1 with hΓ
  have hSΓ : (S : Subgroup G) ≤ Γ := CFSG.ProperTwoGeneratedCore.sylow_le_gamma S h1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨hne, ?_, fun g hg => ?_⟩
  · have hGeven : 2 ∣ Nat.card G :=
      CFSG.RankThreeCoreUniqueness.Helpers.prime_dvd_card_of_pRank_pos 2 (S : Subgroup G)
        (by omega)
    exact even_iff_two_dvd.mpr
      ((S.dvd_card_of_dvd_card hGeven).trans (Subgroup.card_dvd_of_le hSΓ))
  · have hlt := (CFSG.ProperTwoGeneratedCore.gamma_le_iff_conjugate_intersection_rank_lt S Γ
      (by decide) hSΓ).mp le_rfl g hg
    have hlt' : Open.pRank 2 (Γ ⊓ conjugate Γ g) < 1 := hlt
    exact odd_card_of_pRank_two_eq_zero _ (by omega)

theorem S_SU_of_S_Thm182
    (h : S_Thm182) : S_SU := by
  intro G _ _ hs hnonab hK ⟨M, hMtop, S, h3, h2⟩
  have hrk : 2 ≤ Open.twoRank G :=
    CFSG.Milestones.lr_nonabelian_simple_two_rank_lower_bound G hnonab
      (even_card_of_nonabelian_simple hnonab)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSrk : Open.pRank 2 (S : Subgroup G) = Open.twoRank G :=
    (CFSG.SectionRank.pRank_sylow S).1
  by_cases hge : 3 ≤ Open.pRank 2 (S : Subgroup G)
  · have hle : gammaElem (S : Subgroup G) ≤ M := (gammaElem_le_gammaZero _).trans (h3 hge)
    exact h G hs hnonab hK S hge (fun htop => hMtop (top_unique (htop ▸ hle)))
  · have h2eq : Open.pRank 2 (S : Subgroup G) = 2 := by omega
    have hΓM := h2 h2eq
    have hΓtop : Open.properTwoGenCoreGamma (S : Subgroup G) 1 ≠ ⊤ :=
      fun htop => hMtop (top_unique (htop ▸ hΓM))
    exact Or.inr (CFSG.Milestones.bender_suzuki _ (isStronglyEmbeddedOrder_of_isStronglyEmbedded
      (isStronglyEmbedded_gamma_one S (by omega) hΓtop)))

end Gamma

end CFSG.GH74.Uniqueness
