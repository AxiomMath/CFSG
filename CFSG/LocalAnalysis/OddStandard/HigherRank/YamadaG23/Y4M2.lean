module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y4QApp
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y54K1
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y4Card

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {s : Setting3 G L}
  {e : Setting3.Ext s}

theorem y4_M2_le_C2 (hH : F33Hyp s e) : M2 s ≤ s.C₂ := by
  have hcomm : ⁅s.C₂, normIn L s.fr.B⁆ ≤ s.C₂ := by
    apply Subgroup.commutator_le.mpr
    intro x hx n hn
    have hnX : n ∈ s.X := f3_N_le_X s ⟨s3_L_le_H s hH.hS hn.1, hn.2⟩
    have hnx : n * x * n⁻¹ ∈ s.C₂ := f3_C₂_normal hH n hnX x hx
    rw [show ⁅x, n⁆ = x * (n * x * n⁻¹)⁻¹ by rw [commutatorElement_def]; group]
    exact s.C₂.mul_mem hx (s.C₂.inv_mem hnx)
  exact sup_le hcomm (y54_B_le_C2 hH)

theorem y4_t_notin_M2 (c : Ctx4 s e) : s.t ∉ M2 s :=
  y52_t_not_mem_M2 c.toF33 (y4_C2_comm c)

theorem y4_M2_norm_C2 (c : Ctx4 s e) : ∀ x ∈ s.C₂, ∀ m ∈ M2 s, x * m * x⁻¹ ∈ M2 s := by
  intro x hx m hm
  have hmC : m ∈ s.C₂ := y4_M2_le_C2 c.toF33 hm
  have hcomm : ⁅x, m⁆ ∈ s.fr.B := y4_C2_comm c x hx m hmC
  rw [show x * m * x⁻¹ = ⁅x, m⁆ * m by rw [commutatorElement_def]; group]
  exact (M2 s).mul_mem (y54_B_le_M2 s hcomm) hm

theorem y4_C2_cases (c : Ctx4 s e) :
    ∀ x ∈ s.C₂, x ∈ M2 s ∨ ∃ m ∈ M2 s, x = m * s.t := by
  have hH := c.toF33
  have hgen : s.C₂ = M2 s ⊔ zpowers s.t := y52_gen hH
  have hnorm : ∀ y ∈ zpowers s.t, ∀ m ∈ M2 s, y * m * y⁻¹ ∈ M2 s := by
    intro y hy m hm
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact y4_M2_norm_C2 c (s.t ^ k) (s.C₂.zpow_mem (y54_t_mem_C2 hH) k) m hm
  intro x hx
  rw [hgen] at hx
  obtain ⟨m, hm, n, hn, hx'⟩ := mem_sup_of_normalizes (T := zpowers s.t) (C := M2 s)
    hnorm x (by rw [sup_comm]; exact hx)
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hm
  have hm' : s.t ^ k * n * (s.t ^ k)⁻¹ ∈ M2 s :=
    hnorm (s.t ^ k) (Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩) n hn
  have hx'' : x = (s.t ^ k * n * (s.t ^ k)⁻¹) * s.t ^ k := by rw [hx']; group
  rcases Int.emod_two_eq_zero_or_one k with hk | hk
  · left
    have hk' : k % ((2 : ℕ) : ℤ) = 0 := hk
    have h1 : s.t ^ k = 1 := by rw [← zpow_mod_orderOf, s.t_order, hk']; simp
    rw [hx'', h1, mul_one]
    simpa only [h1] using hm'
  · right
    refine ⟨s.t ^ k * n * (s.t ^ k)⁻¹, hm', ?_⟩
    have hk' : k % ((2 : ℕ) : ℤ) = 1 := hk
    have h1 : s.t ^ k = s.t := by rw [← zpow_mod_orderOf, s.t_order, hk']; simp
    rw [hx'', h1]

theorem y4_M2_inf_P (c : Ctx4 s e) : M2 s ⊓ f3P s = s.fr.B := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxM2, hxP⟩ := Subgroup.mem_inf.mp hx
    rcases f3_mem_P x hxP with hxB | ⟨b, hb, rfl⟩
    · exact hxB
    · exact absurd (by
        have hbM2 : b ∈ M2 s := y54_B_le_M2 s hb
        have hmem : b⁻¹ * (b * s.t) ∈ M2 s := (M2 s).mul_mem ((M2 s).inv_mem hbM2) hxM2
        rwa [show b⁻¹ * (b * s.t) = s.t by group] at hmem) (y4_t_notin_M2 c)
  · intro x hx
    exact Subgroup.mem_inf.mpr ⟨y54_B_le_M2 s hx, Subgroup.mem_sup_left hx⟩

theorem y4_card_M2 (c : Ctx4 s e) : Nat.card ↥(M2 s) = 128 := by
  have hH := c.toF33
  have hgen : s.C₂ = M2 s ⊔ zpowers s.t := y52_gen hH
  have htC : s.t ∈ s.C₂ := y54_t_mem_C2 hH
  have hzt_le : zpowers s.t ≤ s.C₂ := Subgroup.zpowers_le.mpr htC
  have hnorm : ∀ x ∈ zpowers s.t, ∀ m ∈ M2 s, x * m * x⁻¹ ∈ M2 s := by
    intro x hx m hm
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact y4_M2_norm_C2 c (s.t ^ k) (s.C₂.zpow_mem htC k) m hm
  have hinf : zpowers s.t ⊓ M2 s = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    obtain ⟨hxT, hxM⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxT
    rcases Int.emod_two_eq_zero_or_one k with hk | hk
    · have hk' : k % ((2 : ℕ) : ℤ) = 0 := hk
      have h1 : s.t ^ k = 1 := by rw [← zpow_mod_orderOf, s.t_order, hk']; simp
      exact h1
    · have hk' : k % ((2 : ℕ) : ℤ) = 1 := hk
      have h1 : s.t ^ k = s.t := by rw [← zpow_mod_orderOf, s.t_order, hk']; simp
      exact absurd (h1 ▸ hxM) (y4_t_notin_M2 c)
  have hrelT : (zpowers s.t).relIndex s.C₂ = 128 := by
    have hcard := Subgroup.relIndex_mul_card (H := zpowers s.t) (K := s.C₂)
    rw [inf_eq_left.mpr hzt_le, Nat.card_zpowers, s.t_order, y4_card_C2 hH] at hcard
    omega
  have hrelBot : (⊥ : Subgroup G).relIndex (M2 s) = Nat.card ↥(M2 s) := by
    have hcard := Subgroup.relIndex_mul_card (H := (⊥ : Subgroup G)) (K := M2 s)
    rw [bot_inf_eq, Subgroup.card_bot] at hcard
    omega
  have hrel := relIndex_sup_of_normalizes (T := zpowers s.t) (C := M2 s) hnorm
  rw [hinf, show zpowers s.t ⊔ M2 s = s.C₂ by rw [sup_comm, hgen]] at hrel
  rw [hrelT, hrelBot] at hrel
  exact hrel.symm

end CFSG.OddStandard.HigherRank.YamadaG23
