module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaDInter
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaKernel

public noncomputable section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaSec3

open CFSG.Fischer Subgroup CFSG.EvenSmallLie.UnitarySix.YamadaD CFSG.Blueprint

variable {G : Type} [Group G] {L : Subgroup G} {t : G}

theorem card_le_of_setting [Finite G] {D : ToddParabolic L} (h : Yamada.Setting G L D t)
    (hL : Nat.card L = 9196830720) :
    ∀ P : Subgroup G, P ≤ centralizer ({t} : Set G) → IsPGroup 2 P → Nat.card P ≤ 2 ^ 17 := by
  intro P hPH hP
  set H := centralizer ({t} : Set G)
  set M := L ⊔ zpowers t
  have hMH : M ≤ H := sup_le h.le_H (zpowers_le.2 (mem_centralizer_singleton_iff.2 rfl))
  have hM : Nat.card M = 2 * Nat.card L := by
    have hc := YamadaD.card_sup_mul_card_inf_of_commute (A := L) (B := zpowers t) (by
      intro a ha b hb
      obtain ⟨n, rfl⟩ := hb
      exact (Commute.zpow_right (mem_centralizer_iff.1 h.mem a ha) n).eq)
    have hinf : L ⊓ zpowers t = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      rcases Yamada.eq_one_or_eq_of_mem_zpowers h.t_sq hx.2 with rfl | rfl
      · exact one_mem _
      · exact absurd hx.1 h.t_not_mem
    rw [hinf, card_bot, mul_one, Nat.card_zpowers, h.order] at hc
    rw [hc, mul_comm]
  have hT : centralizer (L : Set G) ⊓ H = zpowers t := h.inf_centralizer_eq
  have h6 : M.relIndex H ∣ 6 := by
    have := h.relIndex_dvd_six.1
    rwa [hT] at this
  have hH : Nat.card H = Nat.card M * M.relIndex H := by
    have := relIndex_mul_relIndex (⊥ : Subgroup G) M H bot_le hMH
    rw [relIndex_bot_left, relIndex_bot_left] at this
    exact this.symm
  have hdvd : Nat.card P ∣ 2 * 9196830720 * 6 := by
    refine (card_dvd_of_le hPH).trans ?_
    rw [hH, hM, hL]
    exact Nat.mul_dvd_mul_left _ h6
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hP
  rw [hk] at hdvd ⊢
  by_contra hcon
  have h18 : 18 ≤ k := by
    by_contra hk'
    exact hcon (Nat.pow_le_pow_right (by norm_num) (by omega))
  have := (Nat.pow_dvd_pow 2 h18).trans hdvd
  norm_num at this

end CFSG.EvenSmallLie.UnitarySix.YamadaSec3
