module

public import CFSG.LocalAnalysis.EvenBN.Tits.S56Step08

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.Nd11

open Subgroup CFSG.Sporadic.Schreier.Tits CFSG.Open
open CFSG.LocalAnalysis.EvenBN.Tits CFSG.LocalAnalysis.EvenBN.Tits.Data
open scoped Pointwise commutatorElement

section YLemmas

variable {G : Type} [Group G] [Finite G] {d : Data G} {z₀ : G}

theorem centralizes_U11 {g : G} (hz : d.z * g = g * d.z) (h11 : d.pv 11 * g = g * d.pv 11) :
    ∀ u ∈ d.s56U11, u * g = g * u := by
  intro u hu
  rcases (Data.s56_mem_U11_iff).1 hu with rfl | rfl | rfl | rfl
  · simp
  · exact h11
  · exact hz
  · calc d.pv 11 * d.z * g = d.pv 11 * (d.z * g) := by group
      _ = d.pv 11 * (g * d.z) := by rw [hz]
      _ = (d.pv 11 * g) * d.z := by group
      _ = (g * d.pv 11) * d.z := by rw [h11]
      _ = g * (d.pv 11 * d.z) := by group

theorem comm_mul_P0_mem_U10_iff (h49 : d.Thm49Statement) (hd : d.Hyp) {n p f : G} (hn : n ∈ d.N)
    (hp : p ∈ d.s56P0) (hf : f ∈ d.F) :
    (n * p) * f * (n * p)⁻¹ * f⁻¹ ∈ d.s56U10 ↔ n * f * n⁻¹ * f⁻¹ ∈ d.s56U10 := by
  have hu : p * f * p⁻¹ * f⁻¹ ∈ d.s56U10 := hd.s56_P0_comm_F_le_U10 h49 hp hf
  have hu' : n * (p * f * p⁻¹ * f⁻¹) * n⁻¹ ∈ d.s56U10 := hd.s56_N_conj_U10 h49 hn hu
  have e : (n * p) * f * (n * p)⁻¹ * f⁻¹ =
      (n * (p * f * p⁻¹ * f⁻¹) * n⁻¹) * (n * f * n⁻¹ * f⁻¹) := by group
  rw [e]
  constructor
  · intro h
    have := mul_mem (inv_mem hu') h
    rwa [inv_mul_cancel_left] at this
  · intro h
    exact mul_mem hu' h

theorem comm_of_conj_eq {g u : G} (h : g * u * g⁻¹ = u) : u * g = g * u := by
  calc u * g = (g * u * g⁻¹) * g := by rw [h]
    _ = g * u := by group

theorem Y_comm_not_mem_of_IsY (h49 : d.Thm49Statement) (hd : d.Hyp) {y : G} (hy : IsY d y)
    {f : G} (hf : f ∈ d.F) (hfU : f ∉ d.s56U10) : y * f * y⁻¹ * f⁻¹ ∉ d.s56U10 := by
  obtain ⟨hyN, hy3, hy1⟩ := hy.facts
  obtain ⟨hŷNC, -, -, -, -, hŷ11, hŷz⟩ := hd.s56_Y_facts
  have hŷN : d.s56Y ∈ d.N := (mem_inf.1 hŷNC).1
  have hzsq : d.z * d.z = 1 := hd.s56_z_sq
  obtain ⟨ha, ha1, haz, hya, -⟩ := hd.s56_y_orbit h49 hyN hy3 hy1
  have hŷnot : ∀ g ∈ d.F, g ∉ d.s56U10 → d.s56Y * g * d.s56Y⁻¹ * g⁻¹ ∉ d.s56U10 :=
    fun g hg hgU => Data.s56_Y_comm_not_mem hg hgU
  have hcase : y * d.z * y⁻¹ = d.pv 11 ∨ y * d.z * y⁻¹ = d.pv 11 * d.z := by
    rcases (Data.s56_mem_U11_iff).1 ha with h | h | h | h
    · exact absurd h ha1
    · exact Or.inl h
    · exact absurd h haz
    · exact Or.inr h
  rcases hcase with hi | hi
  ·
    have hy11 : y * d.pv 11 * y⁻¹ = d.z * d.pv 11 := by rw [hi] at hya; exact hya
    have hP : d.s56Y * y ∈ d.s56P0 := by
      rw [← hd.s56_CN_U11_eq h49]
      refine mem_inf.2 ⟨mul_mem hŷN hyN, mem_centralizer_iff.2 ?_⟩
      refine centralizes_U11 (comm_of_conj_eq ?_) (comm_of_conj_eq ?_)
      · calc (d.s56Y * y) * d.z * (d.s56Y * y)⁻¹
            = d.s56Y * (y * d.z * y⁻¹) * d.s56Y⁻¹ := by group
          _ = d.s56Y * d.pv 11 * d.s56Y⁻¹ := by rw [hi]
          _ = d.z := hŷ11
      · calc (d.s56Y * y) * d.pv 11 * (d.s56Y * y)⁻¹
            = d.s56Y * (y * d.pv 11 * y⁻¹) * d.s56Y⁻¹ := by group
          _ = d.s56Y * (d.z * d.pv 11) * d.s56Y⁻¹ := by rw [hy11]
          _ = (d.s56Y * d.z * d.s56Y⁻¹) * (d.s56Y * d.pv 11 * d.s56Y⁻¹) := by group
          _ = (d.pv 11 * d.z) * d.z := by rw [hŷz, hŷ11]
          _ = d.pv 11 := by rw [mul_assoc, hzsq, mul_one]
    have hyeq : y = d.s56Y⁻¹ * (d.s56Y * y) := by group
    intro hcomm
    rw [hyeq, comm_mul_P0_mem_U10_iff h49 hd (inv_mem hŷN) hP hf] at hcomm
    have hgF : d.s56Y⁻¹ * f * d.s56Y⁻¹⁻¹ ∈ d.F := hd.s56_N_conj_F h49 (inv_mem hŷN) hf
    have hgU : d.s56Y⁻¹ * f * d.s56Y⁻¹⁻¹ ∉ d.s56U10 := fun h => hfU (by
      have := hd.s56_N_conj_U10 h49 hŷN h
      simpa [mul_assoc] using this)
    apply hŷnot _ hgF hgU
    have e : d.s56Y * (d.s56Y⁻¹ * f * d.s56Y⁻¹⁻¹) * d.s56Y⁻¹ * (d.s56Y⁻¹ * f * d.s56Y⁻¹⁻¹)⁻¹ =
        (d.s56Y⁻¹ * f * d.s56Y⁻¹⁻¹ * f⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem hcomm
  ·
    have hy11 : y * d.pv 11 * y⁻¹ = d.z := by
      have h := hya
      rw [hi] at h
      calc y * d.pv 11 * y⁻¹ = (y * (d.pv 11 * d.z) * y⁻¹) * (y * d.z * y⁻¹)⁻¹ := by group
        _ = (d.z * (d.pv 11 * d.z)) * (d.pv 11 * d.z)⁻¹ := by rw [h, hi]
        _ = d.z := by group
    have hP : d.s56Y⁻¹ * y ∈ d.s56P0 := by
      rw [← hd.s56_CN_U11_eq h49]
      refine mem_inf.2 ⟨mul_mem (inv_mem hŷN) hyN, mem_centralizer_iff.2 ?_⟩
      refine centralizes_U11 (comm_of_conj_eq ?_) (comm_of_conj_eq ?_)
      · calc (d.s56Y⁻¹ * y) * d.z * (d.s56Y⁻¹ * y)⁻¹
            = d.s56Y⁻¹ * (y * d.z * y⁻¹) * d.s56Y := by group
          _ = d.s56Y⁻¹ * (d.pv 11 * d.z) * d.s56Y := by rw [hi]
          _ = d.s56Y⁻¹ * (d.s56Y * d.z * d.s56Y⁻¹) * d.s56Y := by rw [hŷz]
          _ = d.z := by group
      · calc (d.s56Y⁻¹ * y) * d.pv 11 * (d.s56Y⁻¹ * y)⁻¹
            = d.s56Y⁻¹ * (y * d.pv 11 * y⁻¹) * d.s56Y := by group
          _ = d.s56Y⁻¹ * d.z * d.s56Y := by rw [hy11]
          _ = d.s56Y⁻¹ * (d.s56Y * d.pv 11 * d.s56Y⁻¹) * d.s56Y := by rw [hŷ11]
          _ = d.pv 11 := by group
    have hyeq : y = d.s56Y * (d.s56Y⁻¹ * y) := by group
    intro hcomm
    rw [hyeq, comm_mul_P0_mem_U10_iff h49 hd hŷN hP hf] at hcomm
    exact hŷnot f hf hfU hcomm

theorem eq_F_of_mem_of_IsY (h49 : d.Thm49Statement) (hd : d.Hyp) {y : G} (hy : IsY d y)
    {W : Subgroup G} (hWF : W ≤ d.F) (hUW : d.s56U10 ≤ W) {a : G} (haF : a ∈ d.F)
    (haU : a ∉ d.s56U10) (haW : a ∈ W) (hbW : y * a * y⁻¹ ∈ W) : W = d.F := by
  obtain ⟨hyN, -, -⟩ := hy.facts
  have hbU : y * a * y⁻¹ ∉ d.s56U10 := fun h => haU (by
    have := hd.s56_N_conj_U10 h49 (inv_mem hyN) h
    simpa [mul_assoc] using this)
  have hcomm : y * a * y⁻¹ * a⁻¹ ∉ d.s56U10 := Y_comm_not_mem_of_IsY h49 hd hy haF haU
  have hd32 : Nat.card W ∣ 32 := by
    have := Subgroup.card_dvd_of_le hWF
    rwa [hd.B_facts.1] at this
  have hd8 : 8 ∣ Nat.card W := by
    have := Subgroup.card_dvd_of_le hUW
    rwa [Data.s56_card_U10] at this
  have hne8 : Nat.card W ≠ 8 := fun h8 => haU (by
    have := Subgroup.eq_of_le_of_card_ge hUW (by rw [h8, Data.s56_card_U10])
    rw [this]; exact haW)
  have hne16 : Nat.card W ≠ 16 := fun h16 => hcomm
    (mul_inv_mem_of_card_eq_two_mul hUW (by rw [h16, Data.s56_card_U10]) hbW haW hbU haU)
  have h32 : Nat.card W = 32 := by
    obtain ⟨m, hm⟩ := hd8
    rw [hm] at hd32 hne8 hne16 ⊢
    have hm4 : m ∣ 4 := Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 8) (by simpa using hd32)
    have hle : m ≤ 4 := Nat.le_of_dvd (by norm_num) hm4
    interval_cases m <;> simp_all
  exact Subgroup.eq_of_le_of_card_ge hWF (by rw [h32, hd.B_facts.1])

end YLemmas

end CFSG.LocalAnalysis.EvenBN.Tits.N.Nd11
