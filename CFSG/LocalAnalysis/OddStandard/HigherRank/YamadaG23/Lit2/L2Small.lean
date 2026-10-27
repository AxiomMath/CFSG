module

public import CFSG.Assembly.GL83LieDefs
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YCtx

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.OddStandard.HigherRank.G2Three CFSG.OddStandard.HigherRank.G2Three.Sec1

theorem l2_card_dvd_L34 {M : Type} [Group M] (hM : CFSG.Blueprint.LieModel M .PSL 3 2 2) :
    Nat.card M ∣ 60480 := by
  have h := CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero
    (by norm_num : (3 : ℕ) ≠ 0) hM
  obtain ⟨-, K, hKf, hKfin, hcard, ⟨e⟩⟩ := h
  letI := hKf
  letI := hKfin
  have hcardM : Nat.card M = Nat.card (CFSG.Open.StatedProj (CFSG.Open.StatedSL 3 K)) :=
    Nat.card_congr e.toEquiv
  have hdvd : Nat.card (CFSG.Open.StatedProj (CFSG.Open.StatedSL 3 K)) ∣
      Nat.card (CFSG.Open.StatedSL 3 K) :=
    Subgroup.card_dvd_of_surjective (f := QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
  have hSL : Nat.card (CFSG.Open.StatedSL 3 K) = 60480 := by
    rw [CFSG.Open.StatedAPI.card_statedSL_three K, hcard]
    norm_num
  rw [hcardM, ← hSL]
  exact hdvd

theorem l2_dvd_card_of_quotIso {G : Type} [Group G] [Finite G] {M E : Subgroup G} {Q : Type}
    [Group Q] [Finite Q] (hQ : IsQuotIso (normIn M E) (centIn M E) Q) (hE : IsE 4 ↥E)
    (hEC : E ≤ centIn M E) (h360 : 360 ∣ Nat.card Q) : 5760 ∣ Nat.card ↥M := by
  obtain ⟨hCN, φ, hφ, hker⟩ := hQ
  have hker_card : Nat.card φ.ker = Nat.card ↥(centIn M E) := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCN).toEquiv
  have h16E : Nat.card ↥E = 16 := by
    rw [hE.2]
    norm_num
  have h16 : 16 ∣ Nat.card ↥(centIn M E) := h16E ▸ Subgroup.card_dvd_of_le hEC
  have hcardN : Nat.card ↥(normIn M E) = Nat.card Q * Nat.card ↥(centIn M E) := by
    rw [CFSG.GH74.Generic.card_eq_card_mul_card_ker φ hφ, hker_card]
  have hmul : 5760 ∣ Nat.card ↥(normIn M E) := by
    rw [hcardN, show (5760 : ℕ) = 360 * 16 by norm_num]
    exact Nat.mul_dvd_mul h360 h16
  exact dvd_trans hmul (Subgroup.card_dvd_of_le inf_le_left)

theorem l2_not_L34 {G : Type} [Group G] [Finite G] {M E : Subgroup G} {Q : Type} [Group Q]
    [Finite Q] (hQ : IsQuotIso (normIn M E) (centIn M E) Q) (hE : IsE 4 ↥E)
    (hEC : E ≤ centIn M E) (h360 : 360 ∣ Nat.card Q)
    (hM : CFSG.Blueprint.LieModel ↥M .PSL 3 2 2) : False := by
  have h1 : 5760 ∣ Nat.card ↥M := l2_dvd_card_of_quotIso hQ hE hEC h360
  have h2 : Nat.card ↥M ∣ 60480 := l2_card_dvd_L34 hM
  have h3 : 5760 ∣ 60480 := dvd_trans h1 h2
  norm_num at h3

end CFSG.OddStandard.HigherRank.YamadaG23
