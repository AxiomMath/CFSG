module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7NAs3
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] [Finite G] {t g : G} {Lam P S U P1 : Subgroup G}

namespace NtAbs

theorem case2 (h : NtAbs t g Lam P S U P1)
    (hc : Nat.card ↥(conjSub t (centIn P1 Lam)) = 2 ^ 6) :
    conjSub t (centIn P1 Lam) = U ∧ normIn P1 Lam = P ⊔ zpowers g := by
  have hg_ne : g ≠ 1 := by
    intro hg1
    exact h.g_not_S (by rw [hg1]; exact S.one_mem)
  have hg_sq : g * g = 1 := by simpa [pow_two] using h.g_sq
  have horder : orderOf g = 2 := orderOf_eq_prime (by simpa [pow_two] using h.g_sq) hg_ne
  have hcardz : Nat.card (zpowers g) = 2 := by rw [Nat.card_zpowers, horder]
  have hg_notP : g ∉ P := by
    intro hgP
    apply h.g_not_S
    rw [← h.cent]
    exact ⟨hgP, Subgroup.mem_centralizer_singleton_iff.mpr h.tg.symm⟩
  have hdisj : Disjoint P (zpowers g) := by
    rw [Subgroup.disjoint_def]
    intro x hxP hxZ
    haveI : Fact (Nat.card (zpowers g)).Prime := ⟨by rw [hcardz]; norm_num⟩
    rcases Subgroup.eq_bot_or_eq_top_of_prime_card
      ((P ⊓ zpowers g).subgroupOf (zpowers g)) with hbot | htop
    · have hx : (⟨x, hxZ⟩ : zpowers g) ∈ (P ⊓ zpowers g).subgroupOf (zpowers g) :=
        Subgroup.mem_subgroupOf.mpr ⟨hxP, hxZ⟩
      rw [hbot] at hx
      simpa using congrArg Subtype.val (Subgroup.mem_bot.1 hx)
    · exfalso
      have hgm : (⟨g, Subgroup.mem_zpowers g⟩ : zpowers g) ∈
          (P ⊓ zpowers g).subgroupOf (zpowers g) := by rw [htop]; trivial
      exact hg_notP (Subgroup.mem_subgroupOf.mp hgm).1
  have hnorm : zpowers g ≤ Subgroup.normalizer (P : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨h.g_norm_P x, fun hx => ?_⟩
    have hginv : g⁻¹ * g⁻¹ = 1 := by rw [← mul_inv_rev, hg_sq, inv_one]
    have hx_eq : g * (g * x * g⁻¹) * g⁻¹ = x := by
      calc g * (g * x * g⁻¹) * g⁻¹ = (g * g) * x * (g⁻¹ * g⁻¹) := by group
        _ = (1 : G) * x * 1 := by rw [hg_sq, hginv]
        _ = x := by group
    have h2 := h.g_norm_P (g * x * g⁻¹) hx
    rwa [hx_eq] at h2
  have hsupcard : Nat.card ↥(P ⊔ zpowers g) = 2 ^ 13 := by
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer P (zpowers g)
      hnorm hdisj, h.card_P, hcardz]
    norm_num
  have hP0le : Nat.card ↥(normIn P1 Lam) ≤ Nat.card ↥(P ⊔ zpowers g) := by
    calc Nat.card ↥(normIn P1 Lam)
        ≤ 2 ^ 7 * Nat.card ↥(conjSub t (centIn P1 Lam)) := h.card_P0_le
      _ = 2 ^ 13 := by rw [hc]; norm_num
      _ = Nat.card ↥(P ⊔ zpowers g) := hsupcard.symm
  constructor
  · exact (Subgroup.eq_of_le_of_card_ge h.U_le_U0 (by simp [hc, h.card_U])).symm
  · exact (Subgroup.eq_of_le_of_card_ge
      (sup_le h.P_le_P0 (Subgroup.zpowers_le.mpr h.g_mem_P0)) hP0le).symm

end NtAbs

end CFSG.OddStandard.HigherRank.YamadaG23
