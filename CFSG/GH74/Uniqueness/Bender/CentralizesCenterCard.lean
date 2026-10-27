module

public import CFSG.GH74.Uniqueness.Bender.UnitaryAut
import CFSG.RankThree.PartTwo.Sec8.HeringU3nBender

public section

namespace CFSG.GH74.Uniqueness.Bender

variable {K : Type} [Group K] [Finite K]

theorem BenderType.card_autCentralizer_rootCenter {n i e : ℕ}
    (h : BenderType K n i e) (S : Sylow 2 K) :
    Nat.card (autCentralizer (rootCenter (S : Subgroup K))) =
      (2 ^ n) ^ i * (if i = 3 then 2 * (2 ^ n + 1) else 1) := by
  by_cases hi : i = 3
  · subst hi
    rw [if_pos rfl]
    exact CFSG.RankThree.PartTwo.Sec8.HeringU3n.bender_card_autCentralizer h S
  · rw [if_neg hi, mul_one]
    have hinj : Function.Injective (MulAut.conj : K →* MulAut K) := by
      rw [injective_iff_map_eq_one]
      intro g hg
      have hgZ : g ∈ Subgroup.center K := Subgroup.mem_center_iff.mpr fun x => by
        have hx := congrArg (fun φ : MulAut K => φ x) hg
        simp only [MulAut.conj_apply, MulAut.one_apply] at hx
        calc x * g = g * x * g⁻¹ * g := by rw [hx]
          _ = g * x := by group
      rw [h.center_eq_bot, Subgroup.mem_bot] at hgZ
      exact hgZ
    have heq : autCentralizer (rootCenter (S : Subgroup K)) =
        (S : Subgroup K).map (MulAut.conj : K →* MulAut K) := by
      apply le_antisymm
      · intro σ hσ
        obtain ⟨r, hr, rfl⟩ :=
          h.exists_eq_conj_of_centralizes_center_of_ne_three hi S σ (mem_autCentralizer_iff.mp hσ)
        exact ⟨r, hr, rfl⟩
      · rintro _ ⟨r, hr, rfl⟩
        refine mem_autCentralizer_iff.mpr fun z hz => ?_
        have hrz : r * z = z * r :=
          Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hz).2 r hr
        rw [MulAut.conj_apply, hrz, mul_inv_cancel_right]
    rw [heq, Subgroup.card_map_of_injective hinj]
    obtain ⟨t, hc⟩ := h.exists_benderCore S
    exact hc.card_eq

end CFSG.GH74.Uniqueness.Bender
