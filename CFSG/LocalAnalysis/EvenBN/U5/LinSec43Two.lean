module

public import CFSG.LocalAnalysis.EvenBN.U5.LinSec43TwoCent

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.ABGLocalTools (IsSylowOf)

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

namespace CaseBData

variable (hl : d.LinCtx) (k : d.Know12) (c : d.CaseBData)
include hl k c

theorem lin43_conj_t_conj_t (x : G) :
    (MulAut.conj d.t).toMonoidHom ((MulAut.conj d.t).toMonoidHom x) = x := by
  have ht := hl.hyp.t_mul_t
  have hti := hl.hyp.t_inv'
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hti]
  calc d.t * (d.t * x * d.t) * d.t = (d.t * d.t) * x * (d.t * d.t) := by group
    _ = x := by rw [ht]; group

theorem lin_sec43_two_aux (h41 : c.Sec41) {A₀ : Subgroup G} (hA₀S : A₀ ≤ c.S)
    (hA₀el : CFSG.IsElementaryAbelian 2 A₀) (hcard : (2 ^ f) ^ 10 < Nat.card A₀)
    (hDB : A₀ ⊓ d.D ≤ c.Bc) : A₀ ≤ c.Bc := by
  have hcomm : ∀ a ∈ A₀, ∀ b ∈ A₀, a * b = b * a := fun a ha b hb =>
    LinearThree.comm_of_isElemAbelian
      (CFSG.Open.isElemAbelian_of_isElementaryAbelian (h := hA₀el)) ha hb
  have hkey : ∀ x ∈ A₀, Nat.card (A₀ ⊓ d.D : Subgroup G) ≤
      Nat.card (c.Bc ⊓ centralizer ({x} : Set G) : Subgroup G) := by
    intro x hx
    refine Subgroup.card_le_of_le fun a ha => ?_
    exact Subgroup.mem_inf.2 ⟨hDB ha,
      mem_centralizer_singleton_iff.2 (hcomm a (Subgroup.mem_inf.1 ha).1 x hx)⟩
  have hc4 := lin43_card_le_S hl k c hA₀S
  by_cases hA : A₀ ≤ d.D ⊔ (c.Y ⊓ c.S)
  ·
    have hc2 := lin43_card_le_DQ hl k c hA
    by_contra hnot
    obtain ⟨x, hxA, hxB⟩ := SetLike.not_le_iff_exists.1 hnot
    obtain ⟨d', hd', q', hq', rfl⟩ := lin43_exists_mul_DQ hl k c x (hA hxA)
    have hq'1 : q' ≠ 1 := by
      rintro rfl
      rw [mul_one] at hxA hxB
      exact hxB (hDB (Subgroup.mem_inf.2 ⟨hxA, hd'⟩))
    have h1 := lin43_card_Bc_cent_le_q hl k c h41 hd' hq'.1 hq'1
    have h2 := hkey _ hxA
    have h3 : Nat.card A₀ ≤ (2 ^ f) ^ 10 := by
      calc Nat.card A₀ ≤ (2 ^ f) ^ 2 * Nat.card (A₀ ⊓ d.D : Subgroup G) := hc2
        _ ≤ (2 ^ f) ^ 2 * (2 ^ f) ^ 8 := Nat.mul_le_mul_left _ (h2.trans h1)
        _ = (2 ^ f) ^ 10 := by rw [← pow_add]
    exact absurd hcard (not_lt.2 h3)
  ·
    obtain ⟨x, hxA, hxDQ⟩ : ∃ x ∈ A₀, x ∉ d.D ⊔ (c.Y ⊓ c.S) := by
      by_contra hcon
      push Not at hcon
      exact hA hcon
    exfalso
    obtain ⟨d', hd', p, hp, q', hq', rfl⟩ := lin43_exists_mul_S hl k c x (hA₀S hxA)
    have hp1 : p ≠ 1 := by
      rintro rfl
      apply hxDQ
      rw [mul_one]
      exact mul_mem (mem_sup_left hd') (mem_sup_right hq')
    have h1 := lin43_card_Bc_cent_le_p hl k c h41 hd' hp.1 hp1 hq'
    have h2 := hkey _ hxA
    have h3 : Nat.card A₀ ≤ (2 ^ f) ^ 10 := by
      calc Nat.card A₀ ≤ (2 ^ f) ^ 4 * Nat.card (A₀ ⊓ d.D : Subgroup G) := hc4
        _ ≤ (2 ^ f) ^ 4 * (2 ^ f) ^ 6 := Nat.mul_le_mul_left _ (h2.trans h1)
        _ = (2 ^ f) ^ 10 := by rw [← pow_add]
    exact absurd hcard (not_lt.2 h3)

theorem lin_sec43_two (h41 : c.Sec41)
    (h42 : c.Sec42)
    (h43 : ∀ Y : Subgroup G, Y ≤ d.D → CFSG.IsElementaryAbelian 2 Y → Y ≤ c.Bc ∨ Y ≤ c.Bt) :
    ∀ X : Subgroup G, X ≤ c.S → CFSG.IsElementaryAbelian 2 X → (2 ^ f) ^ 10 < Nat.card X →
      X ≤ c.Bc ∨ X ≤ c.Bt := by
  intro X hXS hXel hcard
  have hXDel : CFSG.IsElementaryAbelian 2 (X ⊓ d.D : Subgroup G) :=
    CFSG.IsElementaryAbelian.of_le hXel inf_le_left
  rcases h43 _ inf_le_right hXDel with hB | hBt
  · exact Or.inl (lin_sec43_two_aux hl k c h41 hXS hXel hcard hB)
  · right
    have hτinv := lin43_conj_t_conj_t hl k c
    have hτS : ∀ x ∈ c.S, (MulAut.conj d.t).toMonoidHom x ∈ c.S := fun x hx =>
      (mem_normalizer_iff.1 (s313a_t_mem_normalizer_S hl.toCaseHyp k c.S_syl c.P_le_S) x).1 hx
    have hA₁S : X.map (MulAut.conj d.t).toMonoidHom ≤ c.S := by
      rintro _ ⟨x, hx, rfl⟩
      exact hτS x (hXS hx)
    have hA₁el : CFSG.IsElementaryAbelian 2 (X.map (MulAut.conj d.t).toMonoidHom) :=
      hXel.subgroup_map _
    have hA₁card : Nat.card (X.map (MulAut.conj d.t).toMonoidHom) = Nat.card X :=
      Subgroup.card_map_of_injective (MulAut.conj d.t).injective
    have hA₁D : (X.map (MulAut.conj d.t).toMonoidHom) ⊓ d.D ≤ c.Bc := by
      rintro _ ⟨⟨x, hx, rfl⟩, hxD⟩
      have hxD' : x ∈ d.D := by
        have h1 : (MulAut.conj d.t).toMonoidHom ((MulAut.conj d.t).toMonoidHom x) ∈
            d.D.map (MulAut.conj d.t).toMonoidHom := ⟨_, hxD, rfl⟩
        rw [lin_map_conj_t_D hl k c, hτinv] at h1
        exact h1
      obtain ⟨b, hb, hbx⟩ : x ∈ c.Bc.map (MulAut.conj d.t).toMonoidHom :=
        hBt (Subgroup.mem_inf.2 ⟨hx, hxD'⟩)
      rw [← hbx, hτinv]
      exact hb
    have hA₁ := lin_sec43_two_aux hl k c h41 hA₁S hA₁el (by rw [hA₁card]; exact hcard) hA₁D
    intro x hx
    exact ⟨_, hA₁ ⟨x, hx, rfl⟩, hτinv x⟩

end CaseBData

end Data

end CFSG.LocalAnalysis.EvenBN.U5
