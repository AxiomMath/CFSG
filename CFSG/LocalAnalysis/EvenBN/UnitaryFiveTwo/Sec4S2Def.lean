module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4R3Two
public import CFSG.LocalAnalysis.SeitzReduction.Endgame

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG.Fischer

@[expose] def Data.S₃ {G : Type} [Group G] (d : Data G) : Subgroup G :=
  d.R₃ ⊓ centralizer (d.W : Set G)

section C7

namespace Data.Hyp

variable {G : Type} [Group G] [Finite G] {d : Data G}

theorem S₃_le_R₃ : d.S₃ ≤ d.R₃ := inf_le_left

theorem S₃_le_centralizer_W : d.S₃ ≤ centralizer (d.W : Set G) := inf_le_right

theorem t_not_mem_centralizer_W
    (h : d.Hyp) :
    d.t ∉ centralizer (d.W : Set G) := by
  intro hc
  obtain ⟨w, hw, hwt⟩ := h.sec4_9_W.2.2.1 d.z (z_mem_ZX₄ (d := d))
  have hcomm : w * d.t = d.t * w := mem_centralizer_iff.1 hc w hw
  have : w⁻¹ * d.t * w = d.t := by rw [mul_assoc, ← hcomm]; group
  rw [this] at hwt
  have h1 : d.z = 1 := (mul_right_cancel ((one_mul d.t).trans hwt)).symm
  exact z_ne_one h1

section B4

theorem t_mem_normalizer_D₃ (h : d.Hyp) : d.t ∈ normalizer (d.D₃ : Set G) := by
  have hz : d.z ∈ d.L := d.ι_mem zSU
  have htXW : d.t ∈ d.XW := h.mem_XW_of_comm_z_of_mem_H h.t_mem_H
    (mem_centralizer_iff.1 h.t_mem d.z hz).symm
  have htR₂ : d.t ∈ normalizer (d.R₂ : Set G) :=
    (d.R₂).le_normalizer (mem_sup_left (mem_sup_right (mem_zpowers _)))
  refine mem_normalizer_fintype fun u hu => ?_
  obtain ⟨huN, huD⟩ := Subgroup.mem_inf.1 hu
  exact Subgroup.mem_inf.2 ⟨mul_mem (mul_mem htR₂ huN) (inv_mem htR₂), h.conj_mem_D₁ htXW huD⟩

theorem S_le_centralizer_W : d.S ≤ centralizer (d.W : Set G) := fun s hs =>
  mem_centralizer_iff.2 fun w hw => (mem_centralizer_iff.1 (d.W_le_centralizer hw) s hs).symm

theorem D₃_le_centralizer_W : d.D₃ ≤ centralizer (d.W : Set G) := fun u hu =>
  (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hu).2).2

theorem Y_le_centralizer_W (h : d.Hyp) : d.Y ≤ centralizer (d.W : Set G) := fun y hy =>
  mem_centralizer_iff.2 fun w hw => h.Y_comm (d.W_le_Y hw) hy

theorem SYD₃_le_centralizer_W (h : d.Hyp) :
    (d.S ⊔ d.Y) ⊔ d.D₃ ≤ centralizer (d.W : Set G) :=
  sup_le (sup_le S_le_centralizer_W h.Y_le_centralizer_W) D₃_le_centralizer_W

theorem t_mem_normalizer_SYD₃ (h : d.Hyp) :
    d.t ∈ normalizer (((d.S ⊔ d.Y) ⊔ d.D₃ : Subgroup G) : Set G) := by
  have hSt : ∀ s ∈ d.S, d.t * s * d.t⁻¹ ∈ d.S := fun s hs => by
    have : s * d.t = d.t * s := mem_centralizer_singleton_iff.1 (h.L_le_H (d.pull_le_L _ hs))
    rwa [← this, mul_assoc, mul_inv_cancel, mul_one]
  have hYt : ∀ y ∈ d.Y, d.t * y * d.t⁻¹ ∈ d.Y := fun y hy => by
    rw [h.t_inv]
    exact h.t_conj_mem_Y hy
  have hDt : ∀ u ∈ d.D₃, d.t * u * d.t⁻¹ ∈ d.D₃ := fun u hu =>
    (mem_normalizer_iff.1 (h.t_mem_normalizer_D₃) u).1 hu
  have hle : ((d.S ⊔ d.Y) ⊔ d.D₃).map (MulAut.conj d.t).toMonoidHom ≤ (d.S ⊔ d.Y) ⊔ d.D₃ := by
    rw [Subgroup.map_sup, Subgroup.map_sup]
    refine sup_le (sup_le ?_ ?_) ?_
    · rintro _ ⟨s, hs, rfl⟩
      exact mem_sup_left (mem_sup_left (hSt s hs))
    · rintro _ ⟨y, hy, rfl⟩
      exact mem_sup_left (mem_sup_right (hYt y hy))
    · rintro _ ⟨u, hu, rfl⟩
      exact mem_sup_right (hDt u hu)
  exact mem_normalizer_fintype fun x hx => hle ⟨x, hx, rfl⟩

theorem R₃_eq_SYD₃_sup (h : d.Hyp) :
    d.R₃ = ((d.S ⊔ d.Y) ⊔ d.D₃) ⊔ zpowers d.t := by
  have hRdef : d.R = d.S ⊔ zpowers d.t := rfl
  have hSN : d.S ≤ (d.S ⊔ d.Y) ⊔ d.D₃ :=
    (le_sup_left : d.S ≤ d.S ⊔ d.Y).trans (le_sup_left : d.S ⊔ d.Y ≤ (d.S ⊔ d.Y) ⊔ d.D₃)
  have hYN : d.Y ≤ (d.S ⊔ d.Y) ⊔ d.D₃ :=
    (le_sup_right : d.Y ≤ d.S ⊔ d.Y).trans (le_sup_left : d.S ⊔ d.Y ≤ (d.S ⊔ d.Y) ⊔ d.D₃)
  have hDN : d.D₃ ≤ (d.S ⊔ d.Y) ⊔ d.D₃ := le_sup_right
  rw [h.R₃_eq, hRdef]
  apply le_antisymm
  · refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_
    · exact hSN.trans le_sup_left
    · exact le_sup_right
    · exact hYN.trans le_sup_left
    · exact hDN.trans le_sup_left
  · have hS : d.S ≤ ((d.S ⊔ zpowers d.t) ⊔ d.Y) ⊔ d.D₃ :=
      (le_sup_left : d.S ≤ d.S ⊔ zpowers d.t).trans
        ((le_sup_left : d.S ⊔ zpowers d.t ≤ (d.S ⊔ zpowers d.t) ⊔ d.Y).trans le_sup_left)
    have hY : d.Y ≤ ((d.S ⊔ zpowers d.t) ⊔ d.Y) ⊔ d.D₃ :=
      (le_sup_right : d.Y ≤ (d.S ⊔ zpowers d.t) ⊔ d.Y).trans le_sup_left
    have hD : d.D₃ ≤ ((d.S ⊔ zpowers d.t) ⊔ d.Y) ⊔ d.D₃ := le_sup_right
    have ht : zpowers d.t ≤ ((d.S ⊔ zpowers d.t) ⊔ d.Y) ⊔ d.D₃ :=
      (le_sup_right : zpowers d.t ≤ d.S ⊔ zpowers d.t).trans
        ((le_sup_left : d.S ⊔ zpowers d.t ≤ (d.S ⊔ zpowers d.t) ⊔ d.Y).trans le_sup_left)
    exact sup_le (sup_le (sup_le hS hY) hD) ht

theorem S₃_eq (h : d.Hyp) : d.S₃ = (d.S ⊔ d.Y) ⊔ d.D₃ := by
  set N : Subgroup G := (d.S ⊔ d.Y) ⊔ d.D₃ with hN
  have hNR : N ≤ d.R₃ := by
    rw [h.R₃_eq_SYD₃_sup]
    exact le_sup_left
  have htN : ∀ k ∈ N, d.t * k * d.t ∈ N := fun k hk => by
    have := (mem_normalizer_iff.1 (h.t_mem_normalizer_SYD₃) k).1 hk
    rwa [h.t_inv] at this
  apply le_antisymm
  · intro x hx
    obtain ⟨hxR, hxc⟩ := Subgroup.mem_inf.1 hx
    rw [h.R₃_eq_SYD₃_sup] at hxR
    rcases (mem_sup_zpowers_iff h.t_mul_t htN).1 hxR with hxN | hxt
    · exact hxN
    · exfalso
      have hxtc : x * d.t ∈ centralizer (d.W : Set G) := h.SYD₃_le_centralizer_W hxt
      apply h.t_not_mem_centralizer_W
      have := mul_mem (inv_mem hxc) hxtc
      rwa [inv_mul_cancel_left] at this
  · exact le_inf hNR h.SYD₃_le_centralizer_W

theorem t_not_mem_S₃ (h : d.Hyp) : d.t ∉ d.S₃ := fun ht =>
  h.t_not_mem_centralizer_W (Subgroup.mem_inf.1 ht).2

theorem R₃_eq_S₃_sup (h : d.Hyp) : d.R₃ = d.S₃ ⊔ zpowers d.t := by
  rw [h.S₃_eq]
  exact h.R₃_eq_SYD₃_sup

theorem card_S₃ (h : d.Hyp) : Nat.card d.S₃ = 2 ^ 16 := by
  have htN : d.t ∈ normalizer (d.S₃ : Set G) := by
    rw [h.S₃_eq]
    exact h.t_mem_normalizer_SYD₃
  have hrel := CFSG.SeitzReduction.relIndex_inf_eq_two h.t_mul_t htN h.t_not_mem_S₃
    (le_of_eq h.R₃_eq_S₃_sup) (T := d.R₃)
    (h.R₃_eq_S₃_sup ▸ mem_sup_right (mem_zpowers d.t))
  rw [inf_eq_right.2 S₃_le_R₃] at hrel
  have h1 := Subgroup.relIndex_mul_card d.S₃ d.R₃
  rw [inf_eq_left.2 S₃_le_R₃, hrel] at h1
  have h2 : Nat.card d.R₃ = 2 ^ 17 := h.sec4_13_3.2.2.2.2.2.1
  rw [h2] at h1
  omega

theorem S_le_S₃ (h : d.Hyp) : d.S ≤ d.S₃ := by
  rw [h.S₃_eq]
  exact (le_sup_left : d.S ≤ d.S ⊔ d.Y).trans (le_sup_left : d.S ⊔ d.Y ≤ (d.S ⊔ d.Y) ⊔ d.D₃)

theorem S₃_inf_H (h : d.Hyp) : d.S₃ ⊓ d.H = d.S := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxS, hxH⟩ := Subgroup.mem_inf.1 hx
    have hxR : x ∈ d.R := by
      have := (h.sec4_13_2).2.1
      exact this ▸ Subgroup.mem_inf.2 ⟨S₃_le_R₃ hxS, hxH⟩
    have hSt : ∀ k ∈ d.S, d.t * k * d.t ∈ d.S := fun k hk => by
      have : k * d.t = d.t * k := mem_centralizer_singleton_iff.1 (h.L_le_H (d.pull_le_L _ hk))
      rw [← this, mul_assoc, h.t_mul_t, mul_one]
      exact hk
    rcases (mem_sup_zpowers_iff h.t_mul_t hSt).1 hxR with hxS' | hxt
    · exact hxS'
    · exfalso
      apply h.t_not_mem_S₃
      have := mul_mem (d.S₃.inv_mem hxS) (h.S_le_S₃ hxt)
      rwa [inv_mul_cancel_left] at this
  · intro s hs
    exact Subgroup.mem_inf.2 ⟨h.S_le_S₃ hs, h.L_le_H (d.pull_le_L _ hs)⟩

end B4

end Data.Hyp

end C7

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
