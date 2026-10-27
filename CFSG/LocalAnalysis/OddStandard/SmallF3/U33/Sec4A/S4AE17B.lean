module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AL41UA
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AR10D

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem e17_no_big_elem {E : Subgroup G} (hE : CFSG.Open.IsElemAbelian 2 E)
    (hcard : 32 ≤ Nat.card E) {t : G} (ht2 : t * t = 1) (htE : t ∉ E)
    (hnorm : ∀ e ∈ E, t * e * t⁻¹ ∈ E)
    (hno : ∀ E' : Subgroup G, CFSG.Open.IsElemAbelian 2 E' → Nat.card E' = 16 →
      E' ≤ centralizer ({t} : Set G) → False) : False := by
  obtain ⟨E₁, hE₁def⟩ : ∃ E₁ : Subgroup G, E₁ = E ⊓ centralizer ({t} : Set G) := ⟨_, rfl⟩
  have hE₁el : CFSG.Open.IsElemAbelian 2 E₁ := by
    rw [hE₁def]
    exact hE.mono inf_le_left
  have hcardle := l41_card_le_sq_inf_cent hE hnorm ht2
  have h6 : 6 ≤ Nat.card E₁ := by
    rw [hE₁def]
    by_contra h
    have h5 : Nat.card ↥(E ⊓ centralizer ({t} : Set G)) ≤ 5 := by omega
    have h25 : Nat.card ↥(E ⊓ centralizer ({t} : Set G)) *
        Nat.card ↥(E ⊓ centralizer ({t} : Set G)) ≤ 5 * 5 := Nat.mul_le_mul h5 h5
    omega
  obtain ⟨n, hn⟩ := hE₁el.isPGroup.exists_card_eq
  have h8 : 8 ≤ Nat.card E₁ := by
    rw [hn]
    have hn3 : 3 ≤ n := by
      by_contra h
      have h2 : n ≤ 2 := by omega
      have hp : 2 ^ n ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) h2
      omega
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
  have ht1 : t ≠ 1 := fun h1 => htE (h1 ▸ E.one_mem)
  have htsq : t ^ 2 = 1 := by
    rw [pow_two]
    exact ht2
  have hord : orderOf t = 2 := orderOf_eq_prime htsq ht1
  have hE₂el : CFSG.Open.IsElemAbelian 2 (zpowers t) :=
    CFSG.Open.isElemAbelian_zpowers htsq
  have hE₂card : Nat.card (zpowers t) = 2 := by
    rw [Nat.card_zpowers]
    exact hord
  have hinf : E₁ ⊓ zpowers t = ⊥ := by
    rw [eq_bot_iff]
    intro u hu
    obtain ⟨hu1, hu2⟩ := Subgroup.mem_inf.mp hu
    rcases pt_eq_one_or_of_mem_zpowers hord hu2 with rfl | rfl
    · exact Subgroup.one_mem _
    · exfalso
      rw [hE₁def] at hu1
      exact htE (Subgroup.mem_inf.mp hu1).1
  have hcomm : ∀ a ∈ E₁, ∀ b ∈ zpowers t, a * b = b * a := by
    intro a ha b hb
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    rw [hE₁def] at ha
    have hc : Commute a t := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp ha).2
    exact (hc.zpow_right n).eq
  have hEel : CFSG.Open.IsElemAbelian 2 (E₁ ⊔ zpowers t) :=
    hE₁el.sup_of_commute hE₂el hcomm
  have hEcard : 16 ≤ Nat.card ↥(E₁ ⊔ zpowers t) := by
    have h1 := m11_card_mul_le_sup hinf
    rw [hE₂card] at h1
    omega
  obtain ⟨K, hKE, hK16⟩ := exists_sub_card_sixteen hEel.isPGroup hEcard
  have hEc : E₁ ⊔ zpowers t ≤ centralizer ({t} : Set G) := by
    refine sup_le ?_ ?_
    · rw [hE₁def]
      exact inf_le_right
    · exact Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  exact hno K (hEel.mono hKE) hK16 (hKE.trans hEc)

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
