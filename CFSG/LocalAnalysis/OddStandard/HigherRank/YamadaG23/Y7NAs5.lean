module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7NAs3
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] [Finite G] {t g : G} {Lam P S U P1 : Subgroup G}

namespace NtAbs

theorem case1_direct (h : NtAbs t g Lam P S U P1)
    (hc : Nat.card ↥(conjSub t (centIn P1 Lam)) = 2 ^ 7) :
    IsInternalDirect (normIn P1 Lam) (conjSub t (centIn P1 Lam))
      (conjSub t (conjSub t (centIn P1 Lam))) := by
  have hnorm : centIn P1 Lam ≤ Subgroup.normalizer (conjSub t (centIn P1 Lam) : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro a ha b hb
    have hab : a * b * a⁻¹ = b := by
      rw [h.Z1_comm_U0 a ha b hb]
      group
    rw [hab]
    exact hb
  have hdisj : Disjoint (conjSub t (centIn P1 Lam)) (centIn P1 Lam) := by
    rw [disjoint_iff, inf_comm]
    exact h.Z1_inf_U0
  have hcard_sup : Nat.card ↥(conjSub t (centIn P1 Lam) ⊔ centIn P1 Lam) = 2 ^ 14 := by
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
      (conjSub t (centIn P1 Lam)) (centIn P1 Lam) hnorm hdisj, hc, h.card_Z1_eq_U0, hc]
    norm_num
  have hle : conjSub t (centIn P1 Lam) ⊔ centIn P1 Lam ≤ normIn P1 Lam :=
    sup_le h.U0_le_P0 h.Z1_le_P0
  have hcard : Nat.card ↥(normIn P1 Lam) ≤
      Nat.card ↥(conjSub t (centIn P1 Lam) ⊔ centIn P1 Lam) := by
    calc Nat.card ↥(normIn P1 Lam)
        ≤ 2 ^ 7 * Nat.card ↥(conjSub t (centIn P1 Lam)) := h.card_P0_le
      _ = 2 ^ 14 := by rw [hc]; norm_num
      _ = Nat.card ↥(conjSub t (centIn P1 Lam) ⊔ centIn P1 Lam) := hcard_sup.symm
  have hsup : conjSub t (centIn P1 Lam) ⊔ centIn P1 Lam = normIn P1 Lam :=
    Subgroup.eq_of_le_of_card_ge hle hcard
  rw [conjSub_conjSub_of_sq h.t_sq]
  exact ⟨hsup, by simpa [inf_comm] using h.Z1_inf_U0,
    fun u hu v hv => (h.Z1_comm_U0 v hv u hu).symm⟩

theorem case1_cent (h : NtAbs t g Lam P S U P1)
    (hc : Nat.card ↥(conjSub t (centIn P1 Lam)) = 2 ^ 7) :
    centEl (normIn P1 Lam) t = S ⊔ zpowers g := by
  have hwr : Wr7 t (normIn P1 Lam) (conjSub t (centIn P1 Lam)) :=
    ⟨h.t_sq, case1_direct h hc⟩
  have hcent_card : Nat.card ↥(centEl (normIn P1 Lam) t) = 2 ^ 7 := by
    change Nat.card ↥(normIn P1 Lam ⊓ centralizer ({t} : Set G)) = 2 ^ 7
    rw [← Nat.card_congr hwr.centEquiv.toEquiv, hc]
  have hle : S ⊔ zpowers g ≤ centEl (normIn P1 Lam) t := by
    apply sup_le
    · rw [← h.cent]
      change P ⊓ centralizer ({t} : Set G) ≤ normIn P1 Lam ⊓ centralizer ({t} : Set G)
      exact le_inf (le_trans inf_le_left h.P_le_P0) inf_le_right
    · rw [Subgroup.zpowers_le]
      exact ⟨h.g_mem_P0, Subgroup.mem_centralizer_singleton_iff.mpr h.tg.symm⟩
  have hg_norm : zpowers g ≤ Subgroup.normalizer (S : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff_map_conj_eq]
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro x ⟨y, hy, rfl⟩
      simpa [MulAut.conj_apply] using h.g_norm_S y hy
    · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
  have hdisj : Disjoint S (zpowers g) := by
    rw [disjoint_iff]
    apply le_antisymm _ bot_le
    intro x hx
    obtain ⟨hxS, hxg⟩ := hx
    rw [Subgroup.mem_bot]
    obtain ⟨k, rfl⟩ := hxg
    change g ^ k = 1
    change g ^ k ∈ S at hxS
    have hgsq : g ^ (2 : ℤ) = 1 := by rw [zpow_ofNat]; exact h.g_sq
    obtain ⟨m, hk | hk⟩ := Int.even_or_odd' k
    · rw [hk, zpow_mul, hgsq, one_zpow]
    · have hz : g ^ (2 * m + 1 : ℤ) = g := by
        rw [zpow_add, zpow_mul, hgsq, one_zpow, one_mul, zpow_one]
      rw [hk, hz] at hxS
      exact absurd hxS h.g_not_S
  have hg_ne : g ≠ 1 := by
    intro hg1
    exact h.g_not_S (by rw [hg1]; exact S.one_mem)
  have horder : orderOf g = 2 := by
    rw [orderOf_eq_iff (by norm_num : 0 < 2)]
    refine ⟨h.g_sq, ?_⟩
    intro m hm hm2
    have hm1 : m = 1 := by omega
    subst hm1
    simpa using hg_ne
  have hcard_Sg : Nat.card ↥(S ⊔ zpowers g) = 2 ^ 7 := by
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer S (zpowers g)
      hg_norm hdisj, h.card_S, Nat.card_zpowers, horder]
    norm_num
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcent_card, hcard_Sg])).symm

theorem case1_iso (h : NtAbs t g Lam P S U P1)
    (hc : Nat.card ↥(conjSub t (centIn P1 Lam)) = 2 ^ 7) :
    Nonempty (↥(conjSub t (centIn P1 Lam)) ≃* ↥(S ⊔ zpowers g)) := by
  have hwr : Wr7 t (normIn P1 Lam) (conjSub t (centIn P1 Lam)) :=
    ⟨h.t_sq, case1_direct h hc⟩
  exact ⟨hwr.centEquiv.trans (MulEquiv.subgroupCongr (case1_cent h hc))⟩

end NtAbs

end CFSG.OddStandard.HigherRank.YamadaG23
