module

public import CFSG.GH74.GLS.Stage4.T6Fields

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage4 CFSG.GH74.GLS.Stage4.Hex
  CFSG.GH74.BNPair CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

structure S6Shape {G : Type} [Group G] (D : Ch6Notation G) : Prop where
  R₂_card : Nat.card ↥D.R₂ = D.q₁ ^ 2 * D.q₂ ^ 3
  R₂_comm : ∀ x ∈ D.R₂, ∀ y ∈ D.R₂, ⁅x, y⁆ ∈ D.X₂
  K₁_normR₂ : ∀ x ∈ D.K₁, ∀ r ∈ D.R₂, x * r * x⁻¹ ∈ D.R₂
  P_eq : D.P = D.R₂ ⊔ D.X₁
  P_pGroup : IsPGroup D.p ↥D.P

structure S6Core {G : Type} [Group G] (D : Ch6Notation G) : Prop where
  H_pPrime : ∀ h ∈ D.H, ¬ D.p ∣ orderOf h
  R₂_card : Nat.card ↥D.R₂ = D.q₁ ^ 2 * D.q₂ ^ 3
  R₂_comm : ∀ x ∈ D.R₂, ∀ y ∈ D.R₂, ⁅x, y⁆ ∈ D.X₂
  K₁_normR₂ : ∀ x ∈ D.K₁, ∀ r ∈ D.R₂, x * r * x⁻¹ ∈ D.R₂
  P_eq : D.P = D.R₂ ⊔ D.X₁
  P_pGroup : IsPGroup D.p ↥D.P
  P_card : Nat.card ↥D.P = D.q₁ ^ 3 * D.q₂ ^ 3
  P_normH : ∀ h ∈ D.H, ∀ x ∈ D.P, h * x * h⁻¹ ∈ D.P
  X₂_central : ∀ x ∈ D.X₂, ∀ y ∈ D.P, x * y = y * x
  P₀_le : D.P₀ ≤ D.F
  P₀_pGroup : IsPGroup D.p ↥D.P₀
  F_normB : D.F ≤ normalizer ((D.H ⊔ D.P : Subgroup G) : Set G)
  P₀_normP : D.P₀ ≤ normalizer (D.P : Set G)
  Sylow_PP₀ : ∃ T : Sylow D.p G, (T : Subgroup G) = D.P ⊔ D.P₀

variable {G : Type} [Group G]

theorem Ch6S6.toShape {D : Ch6Notation G} (h : Ch6S6 D) : S6Shape D where
  R₂_card := h.R₂_card
  R₂_comm := h.R₂_comm
  K₁_normR₂ := h.K₁_normR₂
  P_eq := h.P_eq
  P_pGroup := h.P_pGroup

theorem S6Core.toShape {D : Ch6Notation G} (h : S6Core D) : S6Shape D where
  R₂_card := h.R₂_card
  R₂_comm := h.R₂_comm
  K₁_normR₂ := h.K₁_normR₂
  P_eq := h.P_eq
  P_pGroup := h.P_pGroup

theorem Ch6Basics.of_stages_core {N : T2N4 G} {u : G} (hn : Ch6NumD N.p N.q₁ N.q₂)
    (h5 : Ch6Sec5 N.toT2N3 u) (hSle : N.S ≤ ⨆ n ∈ N.Nsub, conjBy n (N.K₁ ⊔ N.K₂))
    (h6 : S6Core N.toCh6) : Ch6Basics N.toCh6 := by
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

theorem Ch6Pre.of_stages_core {N : T2N4 G} {u : G} (hn : Ch6NumD N.p N.q₁ N.q₂)
    (h5 : Ch6Sec5 N.toT2N3 u) (hSle : N.S ≤ ⨆ n ∈ N.Nsub, conjBy n (N.K₁ ⊔ N.K₂))
    (h6 : S6Core N.toCh6) (hs : Ch6Shape N.toCh6) : Ch6Pre N.toCh6 := by
  have hloc := h5.loc
  have hu : N.u = u := h5.u_eq
  refine ⟨Ch6Basics.of_stages_core hn h5 hSle h6, ?_⟩
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

end CFSG.GH74.GLS.Stage4.Rest

namespace CFSG.GH74.GLS.Stage4.Rest.T6

open Subgroup CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.Stage4.Rest.T2 CFSG.GH74.GLS.IVK.Proofs2
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem s6Core_of_parts {N : T2N3 G} {u : G} {p : ℕ} (h : T6Ctx N u p)
    (hord : Nat.card ↥(R₂ N p) = N.q₁ ^ 2 * N.q₂ ^ 3) (P₀ : Subgroup G)
    (hP₀F : P₀ ≤ N.F) (hP₀p : IsPGroup p ↥P₀)
    (hSyl : ∃ T : Sylow p G, (T : Subgroup G) = (R₂ N p ⊔ N.X₁) ⊔ P₀) :
    S6Core (T2N4.toCh6 ⟨N, p, P₀, R₂ N p ⊔ N.X₁⟩) := by
  obtain ⟨m, hm⟩ := h.q₁_pow
  obtain ⟨n, hn⟩ := h.q₂_pow
  have hloc := h.sec5.loc
  have hF := h.sec5.F5
  have hpgR := R₂_pGroup N h.prime
  have hX₁K := X₁_le_K₁ h
  have hnormX₁R : N.X₁ ≤ Subgroup.normalizer (R₂ N p : Set G) := fun g hg =>
    Subgroup.mem_normalizer_fintype (fun n hn => R₂_norm N p (K₁_le_M₂ h (hX₁K hg)) hn)
  have hdisj : Disjoint (R₂ N p) N.X₁ := by
    rw [disjoint_iff, eq_bot_iff, ← R₂_inf_K₁ h]
    exact inf_le_inf_left _ hX₁K
  have hPcard : Nat.card ↥(R₂ N p ⊔ N.X₁) = N.q₁ ^ 3 * N.q₂ ^ 3 := by
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hnormX₁R hdisj,
      hord, hloc.card_X₁]
    ring
  have hFR : ∀ f ∈ N.F, ∀ r ∈ R₂ N p, f * r * f⁻¹ ∈ R₂ N p := fun f hf r hr =>
    R₂_norm N p (F_le_M₂ h hf) hr
  have hFX₁ : ∀ f ∈ N.F, ∀ x ∈ N.X₁, f * x * f⁻¹ ∈ N.X₁ := fun f hf x hx => hF.F_normX₁ f hf x hx
  have hFH : ∀ f ∈ N.F, ∀ x ∈ N.H, f * x * f⁻¹ ∈ N.H := fun f hf x hx =>
    (Subgroup.mem_normalizer_iff.1 (hF.F_normH hf) x).1 hx
  have hHR : ∀ x ∈ N.H, ∀ r ∈ R₂ N p, x * r * x⁻¹ ∈ R₂ N p := fun x hx r hr =>
    R₂_norm N p (H_le_M₂ h hx) hr
  have hHX₁ : ∀ x ∈ N.H, ∀ w ∈ N.X₁, x * w * x⁻¹ ∈ N.X₁ := fun x hx w hw =>
    hloc.H_norm_X₁ x hx w hw
  exact
    { H_pPrime := H_pPrime_of h
      R₂_card := hord
      R₂_comm := (R₂_inv_comm h).2
      K₁_normR₂ := fun x hx r hr => R₂_norm N p (K₁_le_M₂ h hx) hr
      P_eq := rfl
      P_pGroup := IsPGroup.of_card (n := 3 * m + 3 * n) (by
        show Nat.card ↥(R₂ N p ⊔ N.X₁) = p ^ (3 * m + 3 * n)
        rw [hPcard, hm, hn, ← pow_mul, ← pow_mul, ← pow_add]; ring_nf)
      P_card := hPcard
      P_normH := fun x hx => t6_norm_sup (hHR x hx) (hHX₁ x hx)
      X₂_central := by
        intro x hx
        refine t6_comm_sup (fun r hr => ?_) (fun w hw => ?_)
        · have := R₂_cent h r hr x hx
          calc x * r = (r * x * r⁻¹) * r := by rw [this]
            _ = r * x := by group
        · have hwK := hX₁K hw
          have hxK : x ∈ N.K₂ := by rw [hloc.K₂_eq]; exact Subgroup.mem_sup_left hx
          exact (hloc.K_comm w hwK x hxK).symm
      P₀_le := hP₀F
      P₀_pGroup := hP₀p
      F_normB := fun f hf => by
        apply Subgroup.mem_normalizer_fintype
        exact t6_norm_sup (hFH f hf) (t6_norm_sup (hFR f hf) (hFX₁ f hf))
      P₀_normP := fun f hf => by
        apply Subgroup.mem_normalizer_fintype
        exact t6_norm_sup (hFR f (hP₀F hf)) (hFX₁ f (hP₀F hf))
      Sylow_PP₀ := hSyl }

end CFSG.GH74.GLS.Stage4.Rest.T6
