module

public import CFSG.Timmesfeld.RankTwo.LevisExtras

public section

namespace CFSG.ClassicalInvolution.WeakCT

open CFSG.Timmesfeld CFSG.Timmesfeld.LevisExtras
open scoped MatrixGroups

variable {F : Type} [Field F] {G : Type*} [Group G]

@[expose] def Adj3 (u v w : F → G) : Prop :=
  (∃ ρ : SL(3, F) →* G, ∀ c, ρ (tv 0 1 c) = u c ∧ ρ (tv 1 0 c) = v c ∧ ρ (tv 1 2 c) = w c) ∨
    ∃ ρ : SL(3, F) →* G, ∀ c, ρ (tv 1 2 c) = u c ∧ ρ (tv 2 1 c) = v c ∧ ρ (tv 0 1 c) = w c

theorem eq_one_of_adj3 {u v w : F → G} (h : Adj3 u v w) (hw : Function.Injective w) {t : F}
    (ht : t ≠ 0) (hc : Commute (hElt u v t) (w 1)) : t = 1 := by
  have key : hElt u v t * w 1 = w t⁻¹ * hElt u v t := by
    rcases h with ⟨ρ, hρ⟩ | ⟨ρ, hρ⟩
    · have eu : (fun c => ρ (tv 0 1 c)) = u := funext fun c => (hρ c).1
      have ev : (fun c => ρ (tv 1 0 c)) = v := funext fun c => (hρ c).2.1
      rw [← eu, ← ev, ← map_hElt, ← (hρ 1).2.2, ← (hρ t⁻¹).2.2, ← map_mul, ← map_mul,
        h01_mul_tv12 ht, mul_one]
    · have eu : (fun c => ρ (tv 1 2 c)) = u := funext fun c => (hρ c).1
      have ev : (fun c => ρ (tv 2 1 c)) = v := funext fun c => (hρ c).2.1
      rw [← eu, ← ev, ← map_hElt, ← (hρ 1).2.2, ← (hρ t⁻¹).2.2, ← map_mul, ← map_mul,
        h12_mul_tv01 ht, mul_one]
  have e : w t⁻¹ = w 1 := mul_right_cancel (key.symm.trans hc.eq)
  exact inv_eq_one.1 (hw e)

theorem injective_of_adj3 {ρ : SL(3, F) →* G} {ui vi uj vj w : F → G}
    (hi : ∀ c, ρ (tv 0 1 c) = ui c ∧ ρ (tv 1 0 c) = vi c)
    (hj : ∀ c, ρ (tv 1 2 c) = uj c ∧ ρ (tv 2 1 c) = vj c) (hnt : ∃ c, ui c ≠ 1)
    (hw : Function.Injective w)
    (h : ((∀ c, Commute (ui c) (w 1)) ∧ (∀ c, Commute (vi c) (w 1)) ∧ Adj3 uj vj w) ∨
      ((∀ c, Commute (uj c) (w 1)) ∧ (∀ c, Commute (vj c) (w 1)) ∧ Adj3 ui vi w)) :
    Function.Injective ρ := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hnt' : ∃ g, ρ g ≠ 1 := by
    obtain ⟨c, hc⟩ := hnt
    exact ⟨tv 0 1 c, by rw [(hi c).1]; exact hc⟩
  have hker : g ∈ Subgroup.center SL(3, F) :=
    CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple
      (CFSG.LieType.Universal.SpecialLinear.isQuasisimple 2 F le_rfl) hnt' hg
  obtain ⟨ω, hω0, hω3, rfl, h1⟩ := exists_eq_of_mem_center hker
  apply h1
  have eui : (fun c => ρ (tv 0 1 c)) = ui := funext fun c => (hi c).1
  have evi : (fun c => ρ (tv 1 0 c)) = vi := funext fun c => (hi c).2
  have euj : (fun c => ρ (tv 1 2 c)) = uj := funext fun c => (hj c).1
  have evj : (fun c => ρ (tv 2 1 c)) = vj := funext fun c => (hj c).2
  rw [map_mul, map_hElt, map_hElt, eui, evi, euj, evj] at hg
  rcases h with ⟨hu, hv, ha⟩ | ⟨hu, hv, ha⟩
  · have hc : Commute (hElt uj vj (ω ^ 2)) (w 1) := by
      rw [eq_inv_of_mul_eq_one_right hg]
      exact (commute_hElt hu hv ω).inv_left
    have h2 := eq_one_of_adj3 ha hw (pow_ne_zero 2 hω0) hc
    rw [← hω3, pow_succ, h2, one_mul]
  · have hc : Commute (hElt ui vi ω) (w 1) := by
      rw [eq_inv_of_mul_eq_one_left hg]
      exact (commute_hElt hu hv (ω ^ 2)).inv_left
    exact eq_one_of_adj3 ha hw hω0 hc

end CFSG.ClassicalInvolution.WeakCT
