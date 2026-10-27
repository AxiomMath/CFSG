module

public import CFSG.GH74.GLS.IVK.Proofs2.GHInvA5

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup CFSG CFSG.ABGLocalTools Blueprint CFSG.Sporadic.Schreier CFSG.Sporadic.SmallOddCore
  CFSG.GH74.Generic.S45
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open scoped commutatorElement

namespace GHInv

theorem map_conj_centralizerIn_of_norm {M : Type*} [Group M] {H : Subgroup M} {g : M}
    (hg : ∀ h ∈ H, g * h * g⁻¹ ∈ H) (hg' : ∀ h ∈ H, g⁻¹ * h * g ∈ H) (τ : M) :
    (centralizerIn H τ).map (MulAut.conj g).toMonoidHom = centralizerIn H (g * τ * g⁻¹) := by
  ext x
  simp only [Subgroup.mem_map, mem_centralizerIn, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨c, ⟨hc, hcτ⟩, rfl⟩
    refine ⟨hg c hc, ?_⟩
    calc g * c * g⁻¹ * (g * τ * g⁻¹) = g * (c * τ) * g⁻¹ := by group
      _ = g * (τ * c) * g⁻¹ := by rw [hcτ]
      _ = g * τ * g⁻¹ * (g * c * g⁻¹) := by group
  · rintro ⟨hx, hxc⟩
    refine ⟨g⁻¹ * x * g, ⟨hg' x hx, ?_⟩, by group⟩
    have h2 : x * (g * τ * g⁻¹) = (g * τ * g⁻¹) * x := hxc
    calc g⁻¹ * x * g * τ = g⁻¹ * (x * (g * τ * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * τ * g⁻¹) * x) * g := by rw [h2]
      _ = τ * (g⁻¹ * x * g) := by group

theorem card_centralizerIn_conj_of_norm {M : Type*} [Group M] {H : Subgroup M} {g : M}
    (hg : ∀ h ∈ H, g * h * g⁻¹ ∈ H) (hg' : ∀ h ∈ H, g⁻¹ * h * g ∈ H) (τ : M) :
    Nat.card ↥(centralizerIn H (g * τ * g⁻¹)) = Nat.card ↥(centralizerIn H τ) := by
  rw [← map_conj_centralizerIn_of_norm hg hg' τ,
    Subgroup.card_map_of_injective (MulAut.conj g).injective]

end GHInv

structure Ivk73Model {M : Type} [Group M] (P R A : Subgroup M) (tX : M) : Prop where
  autModel : AutModel P R
  card_le : Nat.card ↥R ≤ 2 * Nat.card ↥P
  tX_mem : tX ∈ P
  tX_ord : orderOf tX = 2
  card_A : Nat.card ↥A = 60
  card_cent : Nat.card ↥(centralizerIn P tX) = 240
  derived : ∀ x ∈ centralizerIn P tX, ∀ y ∈ centralizerIn P tX, ⁅x, y⁆ ∈ A
  classes : ∀ t ∈ P, orderOf t = 2 →
    (∃ g ∈ R, t = g * tX * g⁻¹) ∨ GHInv.NoU2Comp ↥(centralizerIn P t)

variable {M : Type} [Group M] [Finite M] {N : Type} [Group N] [Finite N] {L K Q : Subgroup N}

theorem Ivk73Cfg.exists_inner_comp
    (h : Ivk73Cfg N L K Q)
    (hOut : ∀ E : Subgroup (Outer ↥L), (∀ e ∈ E, e * e = 1) → Nat.card E ≤ 2 ^ 1) :
    ∃ (u : N) (hu : u ∈ L), u ∈ Q ∧ orderOf u = 2 ∧
      IsCompIn (centralizer ({(⟨u, hu⟩ : ↥L)} : Set ↥L)) (K.subgroupOf L) := by
  obtain ⟨u, huQ, hu2, huL⟩ := h.exists_involution_mem_L hOut
  refine ⟨u, huL, huQ, hu2, ?_⟩
  have huC : u ∈ centralizer (K : Set N) := h.Q_sylow.le huQ
  have hterm := h.terminal u hu2 huC
  have hKM : K ≤ centralizer ({u} : Set N) ⊓ L := le_inf hterm.1 h.K_le
  have hM : IsCompIn (centralizer ({u} : Set N) ⊓ L) K :=
    LU.Local.isCompIn_mono' hterm hKM inf_le_left
  rw [← subgroupOf_centralizer_inf_eq u huL]
  exact ⟨Subgroup.subgroupOf_mono L hKM,
    (LU.Local.isComponent_subgroupOf_iff' (K := K) (M := centralizer ({u} : Set N) ⊓ L) (H := L)
      inf_le_right).2 hM.2⟩

theorem Ivk73Cfg.Q_row (h : Ivk73Cfg N L K Q)
    (hb : ∀ S : Subgroup N, S ≤ centralizer (K : Set N) → IsPGroup 2 ↥S → Nat.card ↥S ≤ 4) :
    IsElementaryAbelian 2 ↥Q ∧ Nat.card ↥Q = 4 := by
  obtain ⟨E, hEQ, hE, hE4⟩ := h.exists_E
  have hQle : Nat.card ↥Q ≤ 4 := hb Q h.Q_sylow.le h.Q_sylow.isPGroup
  have hEcard : Nat.card ↥E ≤ Nat.card ↥Q := Subgroup.card_le_of_le hEQ
  have hEQeq : E = Q := Subgroup.eq_of_le_of_card_ge hEQ (by omega)
  subst hEQeq
  exact ⟨hE, hE4⟩

theorem Ivk73Cfg.index_row (_h : Ivk73Cfg N L K Q) (hc : Nat.card N ≤ 2 * Nat.card ↥L) :
    L = ⊤ ∨ Nat.card N = 2 * Nat.card ↥L := by
  obtain ⟨m, hm⟩ := Subgroup.card_subgroup_dvd_card L
  have hpos : 0 < Nat.card ↥L := Nat.card_pos
  have hm1 : m ≤ 2 := by
    by_contra hcon
    push Not at hcon
    have : 3 * Nat.card ↥L ≤ Nat.card ↥L * m := by rw [mul_comm]; exact Nat.mul_le_mul_left _ hcon
    omega
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hm
    exact (Nat.card_pos (α := N)).ne' hm
  obtain rfl | rfl : m = 1 ∨ m = 2 := by omega
  · left
    exact Subgroup.eq_top_of_card_eq L (by rw [hm, mul_one])
  · right
    rw [hm, mul_comm]

end CFSG.GH74.GLS.IVK
