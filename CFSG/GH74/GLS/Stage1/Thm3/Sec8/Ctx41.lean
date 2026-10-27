module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx10

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
open scoped commutatorElement Pointwise

@[expose] def Nh {G : Type} [Group G] (S : Subgroup G) (h : G) : Subgroup G :=
  S ⊓ normalizer (zpowers h : Set G)

theorem mem_Nh {G : Type} [Group G] {S : Subgroup G} {h d : G} :
    d ∈ Nh S h ↔ d ∈ S ∧ d ∈ normalizer (zpowers h : Set G) := Subgroup.mem_inf

theorem Nh_le_S {G : Type} [Group G] {S : Subgroup G} {h : G} : Nh S h ≤ S := inf_le_left

theorem h_mem_normalizer_zpowers {G : Type} [Group G] {h : G} :
    h ∈ normalizer (zpowers h : Set G) := by
  have : zpowers h ≤ normalizer (zpowers h : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      exact mul_mem (mul_mem hx hy) (inv_mem hx)
    · intro hy
      have := mul_mem (mul_mem (inv_mem hx) hy) hx
      simpa [mul_assoc] using this
  exact this (Subgroup.mem_zpowers h)

structure YData {G : Type} [Group G] (S K₁ W₂ U : Subgroup G) (h : G) (Y : Subgroup G) : Prop where
  A_le : Aof S K₁ W₂ h ≤ Y
  le_W : Y ≤ Wsub S U
  card : Nat.card ↥Y = 64
  conj_h : ∀ y ∈ Y, h⁻¹ * y * h ∈ Y
  cent_h : ∀ y ∈ Y, h * y = y * h → y = 1
  decomp : ∀ s ∈ S, ∃ y ∈ Y, ∃ d ∈ Nh S h, s = y * d
  norm_D : ∀ d ∈ Nh S h, ∀ y ∈ Y, d * y * d⁻¹ ∈ Y

namespace YData

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ W₁ W₂ U : Subgroup G} {u h : G}
  {Y : Subgroup G}

theorem Y_le_S (hY : YData S K₁ W₂ U h Y) : Y ≤ S := hY.le_W.trans inf_le_left

theorem h_mem_normalizer (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) (hY : YData S K₁ W₂ U h Y) :
    h ∈ normalizer (Y : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have e : ∀ y ∈ Y, h * y * h⁻¹ = h⁻¹ * (h⁻¹ * y * h) * h := by
    intro y hy
    have hc := hs.h_cube y (hY.le_W hy)
    have e3 : h ^ 3 = h * h * h := by simp only [pow_succ, pow_zero, one_mul]
    rw [e3] at hc
    calc h * y * h⁻¹ = h * ((h * h * h)⁻¹ * ((h * h * h) * y)) * h⁻¹ := by group
      _ = h * ((h * h * h)⁻¹ * (y * (h * h * h))) * h⁻¹ := by rw [hc]
      _ = h⁻¹ * (h⁻¹ * y * h) * h := by group
  constructor
  · intro hy
    rw [e y hy]
    exact hY.conj_h _ (hY.conj_h _ hy)
  · intro hy
    have := hY.conj_h _ hy
    simpa [mul_assoc] using this

theorem Nh_le_normalizer (hY : YData S K₁ W₂ U h Y) : Nh S h ≤ normalizer (Y : Set G) := by
  intro d hd
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    exact hY.norm_D d hd y hy
  · intro hy
    have h1 := hY.norm_D d⁻¹ (inv_mem hd) _ hy
    have e : d⁻¹ * (d * y * d⁻¹) * d⁻¹⁻¹ = y := by group
    rwa [e] at h1

theorem S_le_normalizer (hY : YData S K₁ W₂ U h Y) : S ≤ normalizer (Y : Set G) := by
  intro s hs
  obtain ⟨y, hy, d, hd, rfl⟩ := hY.decomp s hs
  have hyN : y ∈ normalizer (Y : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact mul_mem (mul_mem hy hx) (inv_mem hy)
    · intro hx
      have := mul_mem (mul_mem (inv_mem hy) hx) hy
      simpa [mul_assoc] using this
  exact mul_mem hyN (hY.Nh_le_normalizer hd)

theorem N_le_normalizer (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) (hY : YData S K₁ W₂ U h Y) :
    S ⊔ zpowers h ≤ normalizer (Y : Set G) := by
  apply sup_le hY.S_le_normalizer
  rw [zpowers_le]
  exact hY.h_mem_normalizer hs

theorem normedBy_N (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) (hY : YData S K₁ W₂ U h Y) :
    NormedBy Y (S ⊔ zpowers h) :=
  normedBy_iff_le_normalizer.2 (hY.N_le_normalizer hs)

end YData

end CFSG.GH74.GLS.Stage1.Thm3.Sec8
