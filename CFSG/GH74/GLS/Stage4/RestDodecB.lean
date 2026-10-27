module

public import CFSG.GH74.GLS.Stage4.RestRoot
public import CFSG.GH74.GLS.Stage4.LocalGen

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage4 CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.BNPair
open scoped Pointwise

variable {G : Type} [Group G] {D : Ch6Notation G}

theorem card_conjBy' (m : G) (A : Subgroup G) : Nat.card ↥(conjBy m A) = Nat.card ↥A := by
  unfold BNPair.conjBy
  exact (Nat.card_congr (Subgroup.equivMapOfInjective A (MulAut.conj m⁻¹).toMonoidHom
    (MulAut.conj m⁻¹).injective).toEquiv).symm

@[expose] noncomputable def conjByEquiv (m : G) (A : Subgroup G) : ↥(conjBy m A) ≃* ↥A :=
  (Subgroup.equivMapOfInjective A (MulAut.conj m⁻¹).toMonoidHom (MulAut.conj m⁻¹).injective).symm

theorem conjBy_sup' (m : G) (A B : Subgroup G) : conjBy m (A ⊔ B) = conjBy m A ⊔ conjBy m B := by
  unfold BNPair.conjBy
  exact Subgroup.map_sup _ _ _

theorem mem_conjBy_conjBy_of_mem {m x : G} {A : Subgroup G} (hx : x ∈ A) :
    m⁻¹ * x * m ∈ conjBy m A := by
  rw [mem_conjBy_iff]
  simpa [mul_assoc] using hx

theorem six_mem_mul {A₁ A₂ A₃ A₄ A₅ A₆ : Subgroup G} {x₁ x₂ x₃ x₄ x₅ x₆ : G} (h₁ : x₁ ∈ A₁)
    (h₂ : x₂ ∈ A₂) (h₃ : x₃ ∈ A₃) (h₄ : x₄ ∈ A₄) (h₅ : x₅ ∈ A₅) (h₆ : x₆ ∈ A₆) :
    x₁ * x₂ * x₃ * x₄ * x₅ * x₆ ∈ (A₁ : Set G) * (A₂ : Set G) * (A₃ : Set G) * (A₄ : Set G) *
      (A₅ : Set G) * (A₆ : Set G) :=
  Set.mul_mem_mul (Set.mul_mem_mul (Set.mul_mem_mul (Set.mul_mem_mul (Set.mul_mem_mul h₁ h₂) h₃)
    h₄) h₅) h₆

theorem set_prod_subset_of_le {S : Set G} {A J : Subgroup G} (hS : S ⊆ (J : Set G)) (hA : A ≤ J) :
    S * (A : Set G) ⊆ (J : Set G) :=
  Set.mul_subset_iff.2 fun _ ha _ hb => J.mul_mem (hS ha) (hA hb)

theorem set_six_subset_of_le (A₁ A₂ A₃ A₄ A₅ A₆ J : Subgroup G) (h₁ : A₁ ≤ J) (h₂ : A₂ ≤ J)
    (h₃ : A₃ ≤ J) (h₄ : A₄ ≤ J) (h₅ : A₅ ≤ J) (h₆ : A₆ ≤ J) :
    (A₁ : Set G) * (A₂ : Set G) * (A₃ : Set G) * (A₄ : Set G) * (A₅ : Set G) * (A₆ : Set G) ⊆
      (J : Set G) := by
  have h1 : (A₁ : Set G) ⊆ (J : Set G) := h₁
  exact set_prod_subset_of_le (set_prod_subset_of_le (set_prod_subset_of_le
    (set_prod_subset_of_le (set_prod_subset_of_le h1 h₂) h₃) h₄) h₅) h₆

theorem Ch6Core.root_le_P (h : Ch6Core D) {i : ℤ} (hi : 1 ≤ i) (hi6 : i ≤ 6) : D.root i ≤ D.P := by
  rw [h.P_gen]
  exact le_iSup₂_of_le i ⟨hi, hi6⟩ le_rfl

theorem Ch6Core.U_gen (h : Ch6Core D) : D.P = ⨆ k ∈ Set.Icc (1 : ℤ) 6, D.root k := h.P_gen

theorem Ch6Basics.sl2₁ (h : Ch6Basics D) : SL2Pair D.H D.w₁ (D.root 1) (D.root (-1)) := by
  obtain ⟨F, hF, hFin, hcard, ⟨e⟩⟩ := h.iso₁
  obtain ⟨m, hm⟩ := h.q₁_pow
  refine ⟨F, hF, hFin, D.p, m, h.prime, by rw [hcard, hm], ?_, ?_, ?_, ?_, D.H ⊓ D.K₁, inf_le_left,
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [root_p1, h.card_X₁, hcard]
  · rw [root_m1, h.card_X₁', hcard]
  · rw [root_p1, root_m1]
    exact h.X₁_ne
  · rw [root_p1, root_m1, ← h.K₁_eq]
    exact ⟨e⟩
  · rw [root_p1, root_m1, ← h.K₁_eq]
    exact inf_le_right
  · rw [h.card_H_K₁, hcard]
  · rw [root_p1, root_m1, ← h.K₁_eq]
    exact h.w₁_mem
  · rw [h.w₁_sq]
    exact ⟨h.z_mem_H, h.z_mem_K₁⟩
  · rw [root_p1, root_m1]
    exact h.w₁_swap

theorem Ch6Basics.sl2₆ (h : Ch6Basics D) : SL2Pair D.H D.r₂ (D.root 6) (D.root (-6)) := by
  obtain ⟨F, hF, hFin, hcard, ⟨e⟩⟩ := h.iso₂
  obtain ⟨n, hn⟩ := h.q₂_pow
  have hK : conjBy D.a D.X₂' ⊔ conjBy D.a D.X₂ = conjBy D.a D.K₂ := by
    rw [← conjBy_sup', h.K₂_eq, sup_comm]
  have hA : D.a ∈ normalizer (D.H : Set G) := h.a_normH
  refine ⟨F, hF, hFin, D.p, n, h.prime, by rw [hcard, hn], ?_, ?_, ?_, ?_,
    conjBy D.a (D.H ⊓ D.K₂), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [root_p6, card_conjBy', h.card_X₂', hcard]
  · rw [root_m6, card_conjBy', h.card_X₂, hcard]
  · rw [root_p6, root_m6]
    intro hEq
    have : conjBy D.a⁻¹ (conjBy D.a D.X₂') = conjBy D.a⁻¹ (conjBy D.a D.X₂) := by rw [hEq]
    rw [← BNPair.conjBy_mul, ← BNPair.conjBy_mul, mul_inv_cancel, BNPair.conjBy_one,
      BNPair.conjBy_one] at this
    exact h.X₂_ne this.symm
  · rw [root_p6, root_m6, hK]
    exact ⟨(conjByEquiv D.a D.K₂).trans e⟩
  · intro x hx
    rw [mem_conjBy_iff, Subgroup.mem_inf] at hx
    exact (Subgroup.mem_normalizer_iff.1 hA x).2 hx.1
  · rw [root_p6, root_m6, hK]
    intro x hx
    rw [mem_conjBy_iff] at hx ⊢
    exact hx.2
  · rw [card_conjBy', h.card_H_K₂, hcard]
  · rw [root_p6, root_m6, hK, Ch6Notation.r₂, mem_conjBy_iff]
    simpa [mul_assoc] using h.w₂_mem
  · rw [Ch6Notation.r₂, mem_conjBy_iff, Subgroup.mem_inf]
    refine ⟨?_, ?_⟩
    · have : D.a * (D.a⁻¹ * D.w₂ * D.a * (D.a⁻¹ * D.w₂ * D.a)) * D.a⁻¹ = D.z := by
        calc D.a * (D.a⁻¹ * D.w₂ * D.a * (D.a⁻¹ * D.w₂ * D.a)) * D.a⁻¹
            = D.w₂ * D.w₂ := by group
          _ = D.z := h.w₂_sq
      rw [this]
      exact h.z_mem_H
    · have : D.a * (D.a⁻¹ * D.w₂ * D.a * (D.a⁻¹ * D.w₂ * D.a)) * D.a⁻¹ = D.z := by
        calc D.a * (D.a⁻¹ * D.w₂ * D.a * (D.a⁻¹ * D.w₂ * D.a)) * D.a⁻¹
            = D.w₂ * D.w₂ := by group
          _ = D.z := h.w₂_sq
      rw [this]
      exact h.z_mem_K₂
  · intro x hx
    rw [root_p6] at hx
    rw [root_m6, mem_conjBy_iff] at *
    rw [Ch6Notation.r₂]
    have e1 : D.a * (D.a⁻¹ * D.w₂ * D.a * x * (D.a⁻¹ * D.w₂ * D.a)⁻¹) * D.a⁻¹ =
        D.w₂ * (D.a * x * D.a⁻¹) * D.w₂⁻¹ := by group
    rw [e1]
    exact h.w₂_swap' _ hx

theorem Ch6Core.gen97 (h : Ch6Core D) (hz : D.ZClass) :
    Gen97 D.p D.H D.w₁ D.r₂ D.P D.root D.z D.S D.K₁ D.K₂ D.F D.P₀ where
  z_ord := h.z_ord
  K₁_eq := by rw [root_p1, root_m1]; exact h.K₁_eq
  K₂_eq := by rw [root_p4, root_m4]; exact h.K₂_eq
  S_pGroup := h.S_pGroup
  S_sylow := h.S_sylow
  z_mem := ⟨h.z_mem_S, Subgroup.mem_sup_left h.z_mem_K₁⟩
  S_idx := h.S_idx
  z_class := hz
  S_le := h.S_le
  F_odd := h.F_odd
  F_normB := h.F_normB
  F_normN := h.F_normN
  C_le := h.C_le
  P₀_le := h.P₀_le
  P₀_pGroup := h.P₀_pGroup
  P₀_normU := h.P₀_normP
  Sylow_UP₀ := h.Sylow_PP₀

end CFSG.GH74.GLS.Stage4.Rest
