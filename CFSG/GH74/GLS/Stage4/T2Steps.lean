module

public import CFSG.GH74.GLS.Stage4.T2Coord
public import CFSG.GH74.GLS.Stage4.RestSetup

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage4 CFSG.GH74.GLS.Stage4.Hex
  CFSG.GH74.BNPair CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

@[expose] def Ch6T2Rem : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Std G → pRank 2 G = 3 →
    ∀ (Gs : Type) [Group Gs] (q₁ q₂ : ℕ) (z : G) (K₁ K₂ : Subgroup G) (F₁ F₂ : Type)
      [Field F₁] [Field F₂], Ch6Setup G Gs q₁ q₂ z K₁ K₂ F₁ F₂ → ∃ t : G, Ch6Rem z K₁ K₂ F₁ F₂ t

@[expose] def Ch6T2Num : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Std G → pRank 2 G = 3 →
    ∀ (Gs : Type) [Group Gs] (q₁ q₂ : ℕ), IsTwoCentralG2TypeG2At G Gs q₁ q₂ →
      ¬ (q₁ = 9 ∧ q₂ = 9) → (¬ ∃ n : ℕ, 3 ≤ n ∧ q₁ = 3 ^ n ∧ q₂ = 3 ^ n) → Ch6Num q₁ q₂

@[expose] def Ch6T2P51 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Gs : Type) [Group Gs] (q₁ q₂ : ℕ) (z : G) (K₁ K₂ : Subgroup G)
    (F₁ F₂ : Type) [Field F₁] [Field F₂] (t : G),
    Ch6Setup G Gs q₁ q₂ z K₁ K₂ F₁ F₂ → Ch6Rem z K₁ K₂ F₁ F₂ t → q₁ % 4 = q₂ % 4 →
      ∃ (N : T2N1 G) (u : G), N.z = z ∧ N.K₁ = K₁ ∧ N.K₂ = K₂ ∧ N.q₁ = q₁ ∧ N.q₂ = q₂ ∧
        Ch6Loc5 N u ∧ Ch6Coord N

@[expose] def Ch6T2P52 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Gs : Type) [Group Gs] (q₁ q₂ : ℕ) (z : G) (K₁ K₂ : Subgroup G)
    (F₁ F₂ : Type) [Field F₁] [Field F₂] (t : G),
    Ch6Setup G Gs q₁ q₂ z K₁ K₂ F₁ F₂ → Ch6Rem z K₁ K₂ F₁ F₂ t →
      ∀ (N : T2N1 G) (u : G), N.z = z → N.K₁ = K₁ → N.K₂ = K₂ → N.q₁ = q₁ → N.q₂ = q₂ →
        Ch6Loc5 N u → Ch6Coord N → ∃ F : Subgroup G, Ch6F5 (⟨N, F⟩ : T2N2 G)

@[expose] def Ch6T2P53 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], pRank 2 G = 3 →
    ∀ (Gs : Type) [Group Gs] (q₁ q₂ : ℕ) (z : G) (K₁ K₂ : Subgroup G) (F₁ F₂ : Type) [Field F₁]
      [Field F₂] (t : G), Ch6Setup G Gs q₁ q₂ z K₁ K₂ F₁ F₂ → Ch6Rem z K₁ K₂ F₁ F₂ t →
        ∀ (N : T2N2 G) (u : G), N.z = z → N.K₁ = K₁ → N.K₂ = K₂ → N.q₁ = q₁ → N.q₂ = q₂ →
          Ch6Loc5 N.toT2N1 u → Ch6Coord N.toT2N1 → Ch6F5 N →
            ∃ a : G, a⁻¹ * N.z * a = u ∧ Ch6Weyl (⟨N, a⟩ : T2N3 G)

@[expose] def Ch6T2SLe : Prop :=
  ∀ (G : Type) [Group G] [Finite G], pRank 2 G = 3 →
    ∀ (Gs : Type) [Group Gs] (q₁ q₂ : ℕ) (z : G) (K₁ K₂ : Subgroup G) (F₁ F₂ : Type) [Field F₁]
      [Field F₂] (t : G), Ch6Setup G Gs q₁ q₂ z K₁ K₂ F₁ F₂ → Ch6Rem z K₁ K₂ F₁ F₂ t →
        ∀ (N : T2N3 G) (u : G), N.z = z → N.K₁ = K₁ → N.K₂ = K₂ → N.q₁ = q₁ → N.q₂ = q₂ →
          Ch6Loc5 N.toT2N2.toT2N1 u → Ch6Coord N.toT2N2.toT2N1 → Ch6F5 N.toT2N2 → Ch6Weyl N →
            N.S ≤ ⨆ n ∈ N.Nsub, conjBy n (N.K₁ ⊔ N.K₂)

variable {G : Type} [Group G]

theorem Ch6Basics.of_stages {N : T2N4 G} {u : G} (hn : Ch6NumD N.p N.q₁ N.q₂)
    (h5 : Ch6Sec5 N.toT2N3 u) (hSle : N.S ≤ ⨆ n ∈ N.Nsub, conjBy n (N.K₁ ⊔ N.K₂))
    (h6 : Ch6S6 N.toCh6) : Ch6Basics N.toCh6 := by
  have hloc := h5.loc
  have hF := h5.F5
  have hW := h5.weyl
  have hq₁p : N.q₁.minFac = N.p := by
    obtain ⟨m, hm⟩ := hn.q₁_pow
    have hm0 : m ≠ 0 := by
      rintro rfl
      have := hloc.q₁_ge
      simp [hm] at this
    rw [hm]
    exact hn.prime.pow_minFac hm0
  have hq₂p : N.q₂.minFac = N.p := by
    obtain ⟨m, hm⟩ := hn.q₂_pow
    have hm0 : m ≠ 0 := by
      rintro rfl
      have := hloc.q₂_ge
      simp [hm] at this
    rw [hm]
    exact hn.prime.pow_minFac hm0
  exact
    { prime := hn.prime
      p_ne_two := hn.p_ne_two
      q₁_pow := hn.q₁_pow
      q₂_pow := hn.q₂_pow
      q₁_odd := hloc.q₁_odd
      q₂_odd := hloc.q₂_odd
      q₁_ge := hloc.q₁_ge
      q₂_ge := hloc.q₂_ge
      q_rel := hn.q_rel
      z_ord := hloc.z_ord
      one_class := hloc.one_class
      O2prime := hloc.O2prime
      K₁_eq := hloc.K₁_eq
      K₂_eq := hloc.K₂_eq
      K_comm := hloc.K_comm
      iso₁ := hloc.iso₁
      iso₂ := hloc.iso₂
      z_mem_K₁ := hloc.z_mem_K₁
      z_mem_K₂ := hloc.z_mem_K₂
      card_X₁ := hloc.card_X₁
      card_X₁' := hloc.card_X₁'
      card_X₂ := hloc.card_X₂
      card_X₂' := hloc.card_X₂'
      X₁_comm := hloc.X₁_comm
      X₁'_comm := hloc.X₁'_comm
      X₂_comm := hloc.X₂_comm
      X₂'_comm := hloc.X₂'_comm
      X₁_exp := fun x hx => by have h := hloc.X₁_exp x hx; rw [hq₁p] at h; exact h
      X₁'_exp := fun x hx => by have h := hloc.X₁'_exp x hx; rw [hq₁p] at h; exact h
      X₂_exp := fun x hx => by have h := hloc.X₂_exp x hx; rw [hq₂p] at h; exact h
      X₂'_exp := fun x hx => by have h := hloc.X₂'_exp x hx; rw [hq₂p] at h; exact h
      X₁_ne := hloc.X₁_ne
      X₂_ne := hloc.X₂_ne
      H_comm := hloc.H_comm
      H_pPrime := h6.H_pPrime
      z_mem_H := hloc.z_mem_H
      H_norm_X₁ := hloc.H_norm_X₁
      H_norm_X₁' := hloc.H_norm_X₁'
      H_norm_X₂ := hloc.H_norm_X₂
      H_norm_X₂' := hloc.H_norm_X₂'
      card_H_K₁ := hloc.card_H_K₁
      card_H_K₂ := hloc.card_H_K₂
      w₁_mem := hloc.w₁_mem
      w₂_mem := hloc.w₂_mem
      w₁_sq := hloc.w₁_sq
      w₂_sq := hloc.w₂_sq
      w₁_swap := hloc.w₁_swap
      w₁_swap' := hloc.w₁_swap'
      w₂_swap := hloc.w₂_swap
      w₂_swap' := hloc.w₂_swap'
      w₁_normH := hloc.w₁_normH
      w₂_normH := hloc.w₂_normH
      a_normH := hW.a_normH
      a_cube := hW.a_cube
      w₁_a := hW.w₁_a
      w₂_a := hW.w₂_a
      a_mem_N := hW.a_mem_N
      S_pGroup := hloc.S_pGroup
      S_sylow := hloc.S_sylow
      z_mem_S := hloc.z_mem_S
      S_idx := hloc.S_idx
      S_le := hSle
      F_odd := hF.F_odd
      F_normN := hW.F_normN
      C_le := hF.C_le
      P₀_le := h6.P₀_le
      P₀_pGroup := h6.P₀_pGroup }

theorem Ch6Pre.of_stages {N : T2N4 G} {u : G} (hn : Ch6NumD N.p N.q₁ N.q₂)
    (h5 : Ch6Sec5 N.toT2N3 u) (hSle : N.S ≤ ⨆ n ∈ N.Nsub, conjBy n (N.K₁ ⊔ N.K₂))
    (h6 : Ch6S6 N.toCh6) (hs : Ch6Shape N.toCh6) : Ch6Pre N.toCh6 := by
  have hloc := h5.loc
  have hu : N.u = u := h5.u_eq
  refine ⟨Ch6Basics.of_stages hn h5 hSle h6, ?_⟩
  exact
    { K_inter := hloc.K_inter
      u_inv_X₁ := fun x hx => by
        have h := hloc.u_inv_X₁ x hx; rw [← hu] at h; exact h
      u_inv_X₁' := fun x hx => by
        have h := hloc.u_inv_X₁' x hx; rw [← hu] at h; exact h
      u_inv_X₂ := fun x hx => by
        have h := hloc.u_inv_X₂ x hx; rw [← hu] at h; exact h
      u_inv_X₂' := fun x hx => by
        have h := hloc.u_inv_X₂' x hx; rw [← hu] at h; exact h
      a_cycle := h5.weyl.a_cycle
      P_pGroup := h6.P_pGroup
      P_card := h6.P_card
      P_normH := h6.P_normH
      X₂_central := h6.X₂_central
      shape := hs.shape
      inequiv := hs.inequiv
      comm_R := hs.comm_R
      F_normB := h6.F_normB
      P₀_normP := h6.P₀_normP
      Sylow_PP₀ := h6.Sylow_PP₀ }

theorem pow_three_mod_four_of_odd {n : ℕ} (hn : Odd n) : n ^ 3 % 4 = n % 4 := by
  have h2 : n % 2 = 1 := Nat.odd_iff.1 hn
  have h4 : n % 4 = 1 ∨ n % 4 = 3 := by omega
  rcases h4 with h | h <;> simp [Nat.pow_mod, h]

end CFSG.GH74.GLS.Stage4.Rest
