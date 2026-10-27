module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Setting
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.ModelGlobalRank

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG.Open

namespace Data.Hyp

variable {G : Type} [Group G] [Finite G] {d : Data G}

theorem F_le_L (_h : d.Hyp) : d.F ≤ d.L := d.pull_le_L _

theorem F_comm (_h : d.Hyp) {x y : G} (hx : x ∈ d.F) (hy : y ∈ d.F) : x * y = y * x := by
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  rw [← map_mul, ← map_mul, Fsub_comm ha hb]

theorem F_sq (_h : d.Hyp) {x : G} (hx : x ∈ d.F) : x * x = 1 := by
  obtain ⟨a, ha, rfl⟩ := hx
  rw [← map_mul, Fsub_sq ha, map_one]

theorem t_comm_F (h : d.Hyp) {x : G} (hx : x ∈ d.F) : x * d.t = d.t * x :=
  mem_centralizer_iff.1 h.t_mem x (h.F_le_L hx)

theorem withT_F_le_H (h : d.Hyp) : d.withT d.F ≤ d.H :=
  sup_le (h.F_le_L.trans h.L_le_H) ((zpowers_le).2 h.t_mem_H)

theorem exists_eq_mul_of_mem_withT_F (h : d.Hyp) {x : G} (hx : x ∈ d.withT d.F) :
    ∃ a ∈ d.F, ∃ k : ℤ, x = a * d.t ^ k := by
  have hset := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute d.F (zpowers d.t)
    fun a ha y hy => by
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
      exact (Commute.zpow_right (h.t_comm_F ha) k).eq).2
  have hx' : x ∈ ((d.F ⊔ zpowers d.t : Subgroup G) : Set G) := hx
  rw [hset] at hx'
  obtain ⟨a, ha, y, hy, rfl⟩ := hx'
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
  exact ⟨a, ha, k, rfl⟩

theorem isElemAbelian_withT_F (h : d.Hyp) : IsElemAbelian 2 (d.withT d.F) := by
  have hcomm : ∀ x ∈ d.withT d.F, ∀ y ∈ d.withT d.F, x * y = y * x := by
    intro x hx y hy
    obtain ⟨a, ha, k, rfl⟩ := h.exists_eq_mul_of_mem_withT_F hx
    obtain ⟨b, hb, m, rfl⟩ := h.exists_eq_mul_of_mem_withT_F hy
    have hbt : d.t ^ k * b = b * d.t ^ k := (Commute.zpow_right (h.t_comm_F hb) k).eq.symm
    have hat : d.t ^ m * a = a * d.t ^ m := (Commute.zpow_right (h.t_comm_F ha) m).eq.symm
    calc a * d.t ^ k * (b * d.t ^ m) = a * (d.t ^ k * b) * d.t ^ m := by group
      _ = (a * b) * (d.t ^ k * d.t ^ m) := by rw [hbt]; group
      _ = (b * a) * (d.t ^ m * d.t ^ k) := by
          rw [h.F_comm ha hb, ← zpow_add, ← zpow_add, add_comm]
      _ = b * (a * d.t ^ m) * d.t ^ k := by group
      _ = b * (d.t ^ m * a) * d.t ^ k := by rw [hat]
      _ = b * d.t ^ m * (a * d.t ^ k) := by group
  refine ⟨isMulCommutative_iff.2 fun x y => Subtype.ext (hcomm _ x.2 _ y.2), fun x hx => ?_⟩
  obtain ⟨a, ha, k, rfl⟩ := h.exists_eq_mul_of_mem_withT_F hx
  have hat : d.t ^ k * a = a * d.t ^ k := (Commute.zpow_right (h.t_comm_F ha) k).eq.symm
  have htk : d.t ^ k * d.t ^ k = 1 := by
    rw [← zpow_add, ← two_mul, zpow_mul, show (d.t ^ (2 : ℤ)) = 1 by
      rw [zpow_two, h.t_mul_t], one_zpow]
  calc (a * d.t ^ k) ^ 2 = a * (d.t ^ k * a) * d.t ^ k := by rw [sq]; group
    _ = (a * a) * (d.t ^ k * d.t ^ k) := by rw [hat]; group
    _ = 1 := by rw [h.F_sq ha, htk, one_mul]

theorem card_withT_F (h : d.Hyp) : Nat.card (d.withT d.F) = 2 ^ 5 := by
  obtain ⟨hc, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute d.F (zpowers d.t)
    fun a ha y hy => by
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
      exact (Commute.zpow_right (h.t_comm_F ha) k).eq
  have hinf : d.F ⊓ zpowers d.t = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxF, hxt⟩
    rw [mem_bot]
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hxt
    have hk : d.t ^ k = d.t ^ (k % 2) := by
      rw [← zpow_mod_orderOf, h.t_two]
      norm_cast
    rcases Int.emod_two_eq_zero_or_one k with h0 | h1
    · rw [hk, h0, zpow_zero]
    · rw [hk, h1, zpow_one] at hxF
      exact absurd (h.F_le_L hxF) h.t_not_mem_L
  rw [hinf, Subgroup.card_bot, mul_one, h.card_zpowers_t, d.card_F] at hc
  rw [withT, hc]
  norm_num

theorem card_le_of_elemAb (h : d.Hyp) {E : Subgroup G} (hEH : E ≤ d.H)
    (hc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hs : ∀ x ∈ E, x * x = 1) :
    Nat.card E ≤ 2 ^ 5 := by
  set f : E →* MulAut SU52 := h.act.comp (inclusion hEH) with hf
  have hcard := Subgroup.card_ker_mul_card_range f
  have hr : Nat.card f.range ≤ 16 := by
    refine card_le_of_elemAb_mulAut ?_ ?_
    · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hc _ a.2 _ b.2)
    · rintro _ ⟨a, rfl⟩
      rw [← map_mul, show a * a = 1 from Subtype.ext (hs a a.2), map_one]
  have hk : Nat.card f.ker ≤ 2 := by
    have hmem : ∀ x : f.ker, ((x : E) : G) ∈ zpowers d.t := by
      intro x
      have hx : h.act ⟨(x : E), hEH (x : E).2⟩ = 1 := x.2
      rw [act_eq_one_iff] at hx
      rcases h.eq_one_or_eq_t_of_mem_kernel ⟨hx, hEH (x : E).2⟩ (hs _ (x : E).2) with e | e
      · rw [e]
        exact one_mem _
      · rw [e]
        exact mem_zpowers _
    calc Nat.card f.ker ≤ Nat.card (zpowers d.t) :=
          Nat.card_le_card_of_injective (fun x => (⟨((x : E) : G), hmem x⟩ : zpowers d.t))
            fun x y e => by
              apply Subtype.ext
              apply Subtype.ext
              exact congrArg (fun z : zpowers d.t => (z : G)) e
      _ = 2 := h.card_zpowers_t
  calc Nat.card E = Nat.card f.ker * Nat.card f.range := hcard.symm
    _ ≤ 2 * 16 := Nat.mul_le_mul hk hr
    _ = 2 ^ 5 := by norm_num

end Data.Hyp

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
