module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFyWrRec
public import Mathlib.GroupTheory.SpecificGroups.Dihedral


public section

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup

abbrev D8 : Type := DihedralGroup 4

theorem d8_central_of_ne_one : ∀ a : D8, a ≠ 1 → a = DihedralGroup.r 2 ∨
    a * a = DihedralGroup.r 2 ∨ ∃ g : D8, a * (g * a⁻¹ * g⁻¹) = DihedralGroup.r 2 := by
  decide

variable {X : Type*} [Group X]

structure WrCtx (ρ : D8 →* X) (Q : Subgroup X) (x v : X) : Prop where
  inj : Function.Injective ρ
  card : Nat.card Q = 64
  rho_mem : ∀ a, ρ a ∈ Q
  normal : ∀ q ∈ Q, ∀ a : D8, ∃ a' : D8, q * ρ a * q⁻¹ = ρ a'
  x_conj : ∀ q ∈ Q, x * q * x⁻¹ ∈ Q
  x_conj' : ∀ q ∈ Q, x⁻¹ * q * x ∈ Q
  tau : x * ρ (DihedralGroup.r 2) * x⁻¹ = v
  vtau : x * v * x⁻¹ = ρ (DihedralGroup.r 2)
  v_notin : ∀ a : D8, ρ a ≠ v

namespace WrCtx

variable {ρ : D8 →* X} {Q : Subgroup X} {x v : X} (h : WrCtx ρ Q x v)
include h

theorem conj_S (g c : D8) : ∃ c' : D8,
    ρ g * (x * ρ c * x⁻¹) * (ρ g)⁻¹ = x * ρ c' * x⁻¹ := by
  obtain ⟨c', hc'⟩ := h.normal (x⁻¹ * ρ g * x) (h.x_conj' _ (h.rho_mem g)) c
  refine ⟨c', ?_⟩
  calc ρ g * (x * ρ c * x⁻¹) * (ρ g)⁻¹
      = x * ((x⁻¹ * ρ g * x) * ρ c * (x⁻¹ * ρ g * x)⁻¹) * x⁻¹ := by group
    _ = x * ρ c' * x⁻¹ := by rw [hc']

theorem conj_D (b a : D8) : ∃ a' : D8,
    (x * ρ b * x⁻¹) * ρ a * (x * ρ b * x⁻¹)⁻¹ = ρ a' :=
  h.normal _ (h.x_conj _ (h.rho_mem b)) a

theorem inf_aux {a b : D8} (hab : ρ a = x * ρ b * x⁻¹) : a = 1 := by
  by_contra ha
  have hτ : ∃ b' : D8, ρ (DihedralGroup.r 2) = x * ρ b' * x⁻¹ := by
    rcases d8_central_of_ne_one a ha with h1 | h1 | ⟨g, h1⟩
    · exact ⟨b, by rw [← h1]; exact hab⟩
    · refine ⟨b * b, ?_⟩
      rw [← h1, map_mul, hab, map_mul]; group
    · obtain ⟨b'', hb''⟩ := h.conj_S g b
      refine ⟨b * b''⁻¹, ?_⟩
      have h1' : ρ a * (ρ g * (ρ a)⁻¹ * (ρ g)⁻¹) = ρ (DihedralGroup.r 2) := by
        rw [← h1]; simp [map_mul, map_inv]
      have hc : ρ g * (ρ a)⁻¹ * (ρ g)⁻¹ = (x * ρ b'' * x⁻¹)⁻¹ := by
        rw [← hb'', hab]; group
      rw [← h1', hc, hab]
      simp only [map_mul, map_inv]
      group
  obtain ⟨b', hb'⟩ := hτ
  apply h.v_notin b'
  calc ρ b' = x⁻¹ * (x * ρ b' * x⁻¹) * x := by group
    _ = x⁻¹ * ρ (DihedralGroup.r 2) * x := by rw [hb']
    _ = v := by
      calc x⁻¹ * ρ (DihedralGroup.r 2) * x = x⁻¹ * (x * v * x⁻¹) * x := by rw [h.vtau]
        _ = v := by group

theorem comm (a b : D8) : ρ a * (x * ρ b * x⁻¹) = (x * ρ b * x⁻¹) * ρ a := by
  obtain ⟨c, hc⟩ := h.conj_S a b
  obtain ⟨a'', ha''⟩ := h.conj_D b a⁻¹
  rw [map_inv] at ha''
  have h1 : ρ (a * a'') = x * ρ (c * b⁻¹) * x⁻¹ := by
    rw [map_mul, ← ha'', map_mul, map_inv]
    have e : ρ a * ((x * ρ b * x⁻¹) * (ρ a)⁻¹ * (x * ρ b * x⁻¹)⁻¹) =
        (ρ a * (x * ρ b * x⁻¹) * (ρ a)⁻¹) * (x * ρ b * x⁻¹)⁻¹ := by group
    rw [e, hc]; group
  have h2 := h.inf_aux h1
  have h3 : ρ a * ((x * ρ b * x⁻¹) * (ρ a)⁻¹ * (x * ρ b * x⁻¹)⁻¹) = 1 := by
    have : ρ (a * a'') = 1 := by rw [h2, map_one]
    rw [map_mul, ← ha''] at this
    exact this
  calc ρ a * (x * ρ b * x⁻¹)
      = (ρ a * ((x * ρ b * x⁻¹) * (ρ a)⁻¹ * (x * ρ b * x⁻¹)⁻¹)) * (x * ρ b * x⁻¹) * ρ a := by
        group
    _ = (x * ρ b * x⁻¹) * ρ a := by rw [h3]; group

theorem decomp_inj {a b a' b' : D8}
    (hab : ρ a * (x * ρ b * x⁻¹) = ρ a' * (x * ρ b' * x⁻¹)) : a = a' ∧ b = b' := by
  have h1 : ρ (a'⁻¹ * a) = x * ρ (b' * b⁻¹) * x⁻¹ := by
    rw [map_mul, map_inv, map_mul, map_inv]
    calc (ρ a')⁻¹ * ρ a = (ρ a')⁻¹ * (ρ a * (x * ρ b * x⁻¹)) * (x * ρ b * x⁻¹)⁻¹ := by group
      _ = (ρ a')⁻¹ * (ρ a' * (x * ρ b' * x⁻¹)) * (x * ρ b * x⁻¹)⁻¹ := by rw [hab]
      _ = x * (ρ b' * (ρ b)⁻¹) * x⁻¹ := by group
  have h2 : a'⁻¹ * a = 1 := h.inf_aux h1
  have ha : a = a' := (inv_inj.1 (mul_eq_one_iff_eq_inv.1 h2)).symm
  subst ha
  have hb : ρ b = ρ b' := by
    have : x * ρ b * x⁻¹ = x * ρ b' * x⁻¹ := mul_left_cancel hab
    have := mul_right_cancel this
    exact mul_left_cancel this
  exact ⟨rfl, h.inj hb⟩

theorem exists_decomp : ∀ q ∈ Q, ∃ a b : D8, q = ρ a * (x * ρ b * x⁻¹) := by
  set f : D8 × D8 → X := fun p => ρ p.1 * (x * ρ p.2 * x⁻¹) with hf
  have hfinj : Function.Injective f := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ hab
    obtain ⟨rfl, rfl⟩ := h.decomp_inj hab
    rfl
  have hsub : Set.range f ⊆ (Q : Set X) := by
    rintro _ ⟨⟨a, b⟩, rfl⟩
    exact Q.mul_mem (h.rho_mem a) (h.x_conj _ (h.rho_mem b))
  have hfin : Finite Q := Nat.finite_of_card_ne_zero (by rw [h.card]; norm_num)
  have hQfin : (Q : Set X).Finite := Set.toFinite _
  have hcardf : (Set.range f).ncard = 64 := by
    rw [← Set.image_univ, Set.ncard_image_of_injective _ hfinj, Set.ncard_univ, Nat.card_prod,
      DihedralGroup.nat_card]
  have hcardQ : (Q : Set X).ncard = 64 := by
    rw [← Nat.card_coe_set_eq]; exact h.card
  have heq : Set.range f = (Q : Set X) :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [hcardf, hcardQ]) hQfin
  intro q hq
  have : q ∈ Set.range f := by rw [heq]; exact hq
  obtain ⟨⟨a, b⟩, hab⟩ := this
  exact ⟨a, b, hab.symm⟩

end WrCtx

end CFSG.EvenSporadicStandard.TwoHS
