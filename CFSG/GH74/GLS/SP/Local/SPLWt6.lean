module

public import CFSG.GH74.GLS.SP.Local.SPLWt5

public section

namespace CFSG.GH74.GLS.SP.Local

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.BNPair
open CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS.SP
open scoped Pointwise commutatorElement

variable {G : Type} [Group G]

section KernelInj

variable [Finite G] (D : SPLNot3 G)

theorem ker_ne_12 (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) (h3 : SPL3M2 D) :
    kernelOf D.H D.X₁ ≠ kernelOf D.H D.X₂ := by
  intro h
  have h' := h₁_mem_ker₂ D hs h1 h3
  rw [← h] at h'
  exact h₁_not_mem_ker₁ D hs h1 h3 h'

theorem ker_ne_13 (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) (h3 : SPL3M2 D) :
    kernelOf D.H D.X₁ ≠ kernelOf D.H D.X₃ := by
  intro h
  have h' := z_mem_ker₁ D hs h1 h3
  rw [h] at h'
  exact z_not_mem_ker₃ D hs h3 h'

theorem ker_ne_14 (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) (h3 : SPL3M2 D) :
    kernelOf D.H D.X₁ ≠ kernelOf D.H D.X₄ := by
  intro h
  have h' := z_mem_ker₁ D hs h1 h3
  rw [h] at h'
  exact z_not_mem_ker₄ D hs h1 h3 h'

theorem ker_ne_23 (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) (h3 : SPL3M2 D) :
    kernelOf D.H D.X₂ ≠ kernelOf D.H D.X₃ := by
  intro h
  have h' := z_mem_ker₂ D hs h1 h3
  rw [h] at h'
  exact z_not_mem_ker₃ D hs h3 h'

theorem ker_ne_24 (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) (h3 : SPL3M2 D) :
    kernelOf D.H D.X₂ ≠ kernelOf D.H D.X₄ := by
  intro h
  have h' := z_mem_ker₂ D hs h1 h3
  rw [h] at h'
  exact z_not_mem_ker₄ D hs h1 h3 h'

theorem kernel_inj (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) (h3 : SPL3M2 D)
    (hR : SPLR₁ D) {A B : Subgroup G}
    (hA : A = D.X₁ ∨ A = D.X₂ ∨ A = D.X₃ ∨ A = D.X₄)
    (hB : B = D.X₁ ∨ B = D.X₂ ∨ B = D.X₃ ∨ B = D.X₄)
    (h : kernelOf D.H A = kernelOf D.H B) : A = B := by
  have n12 := ker_ne_12 D hs h1 h3
  have n13 := ker_ne_13 D hs h1 h3
  have n14 := ker_ne_14 D hs h1 h3
  have n23 := ker_ne_23 D hs h1 h3
  have n24 := ker_ne_24 D hs h1 h3
  have n34 := ker₃_ne_ker₄ D hs h1 h3 hR
  rcases hA with rfl | rfl | rfl | rfl <;> rcases hB with rfl | rfl | rfl | rfl
  all_goals first
    | rfl
    | exact absurd h ‹_›
    | exact absurd h.symm ‹_›

theorem ch_diff_one (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) (h3 : SPL3M2 D)
    (hR : SPLR₁ D) :
    ∀ i j : ℤ, 1 ≤ i → i ≤ 4 → 1 ≤ j → j ≤ 4 → i ≠ j →
      centralizer (D.root i : Set G) ⊓ D.H ≠ centralizer (D.root j : Set G) ⊓ D.H := by
  intro i j hi1 hi4 hj1 hj4 hij
  have n12 := ker_ne_12 D hs h1 h3
  have n13 := ker_ne_13 D hs h1 h3
  have n14 := ker_ne_14 D hs h1 h3
  have n23 := ker_ne_23 D hs h1 h3
  have n24 := ker_ne_24 D hs h1 h3
  have n34 := ker₃_ne_ker₄ D hs h1 h3 hR
  have hi' : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
  have hj' : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by omega
  rcases hi' with rfl | rfl | rfl | rfl <;> rcases hj' with rfl | rfl | rfl | rfl
  all_goals first
    | exact absurd rfl hij
    | (simp only [root_p1, root_p2, root_p3, root_p4]
       first
         | exact n12 | exact n12.symm | exact n13 | exact n13.symm | exact n14 | exact n14.symm
         | exact n23 | exact n23.symm | exact n24 | exact n24.symm | exact n34 | exact n34.symm)

end KernelInj

section W0

variable [Finite G] (D : SPLNot3 G)

omit [Finite G] in
theorem w₂_inv_H₂ (h1 : SPL2Set D.toSPLNot1) :
    ∀ b ∈ D.H₂, D.w₂ * b * D.w₂⁻¹ = b⁻¹ := by
  intro b hb
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hb
  have e : D.h₂ ^ i = D.t * D.h₁ ^ i * D.t⁻¹ := by
    unfold SPLNot1.h₂
    rw [conj_zpow]
  rw [e]
  have h1i : D.w₁ * D.h₁ ^ i * D.w₁⁻¹ = (D.h₁ ^ i)⁻¹ :=
    h1.w₁_inv _ (zpow_mem (mem_zpowers _) i)
  calc D.w₂ * (D.t * D.h₁ ^ i * D.t⁻¹) * D.w₂⁻¹
      = D.t * (D.w₁ * D.h₁ ^ i * D.w₁⁻¹) * D.t⁻¹ := by
        show (D.t * D.w₁ * D.t⁻¹) * (D.t * D.h₁ ^ i * D.t⁻¹) * (D.t * D.w₁ * D.t⁻¹)⁻¹ = _
        group
    _ = D.t * (D.h₁ ^ i)⁻¹ * D.t⁻¹ := by rw [h1i]
    _ = (D.t * D.h₁ ^ i * D.t⁻¹)⁻¹ := by group

theorem w0_inv_H (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) :
    ∀ h ∈ D.H, (D.w₁ * D.w₂) * h * (D.w₁ * D.w₂)⁻¹ = h⁻¹ := by
  intro h hh
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commute (H₁_H₂_comm D hs h1) hh
  have ha1 : D.w₁ * a * D.w₁⁻¹ = a⁻¹ := h1.w₁_inv a ha
  have ha2 : D.w₂ * a = a * D.w₂ :=
    (hs.comps.comm a (H₁_le_K₁ D h1 ha) D.w₂ (w₂_mem_K₂ D hs h1)).symm
  have hb1 : D.w₁ * b = b * D.w₁ := hs.comps.comm D.w₁ h1.w₁_mem b (H₂_le_K₂ D hs h1 hb)
  have hb2 : D.w₂ * b * D.w₂⁻¹ = b⁻¹ := w₂_inv_H₂ D h1 b hb
  have hab : a * b = b * a := H₁_H₂_comm D hs h1 a ha b hb
  have hb1' : D.w₁ * b⁻¹ * D.w₁⁻¹ = b⁻¹ := by
    calc D.w₁ * b⁻¹ * D.w₁⁻¹ = (D.w₁ * b * D.w₁⁻¹)⁻¹ := by group
      _ = b⁻¹ := by rw [hb1]; group
  have e1 : D.w₂ * a * b * D.w₂⁻¹ = a * b⁻¹ := by
    calc D.w₂ * a * b * D.w₂⁻¹ = (D.w₂ * a) * b * D.w₂⁻¹ := rfl
      _ = (a * D.w₂) * b * D.w₂⁻¹ := by rw [ha2]
      _ = a * (D.w₂ * b * D.w₂⁻¹) := by group
      _ = a * b⁻¹ := by rw [hb2]
  have e2 : D.w₁ * (a * b⁻¹) * D.w₁⁻¹ = a⁻¹ * b⁻¹ := by
    calc D.w₁ * (a * b⁻¹) * D.w₁⁻¹ = (D.w₁ * a * D.w₁⁻¹) * (D.w₁ * b⁻¹ * D.w₁⁻¹) := by group
      _ = a⁻¹ * b⁻¹ := by rw [ha1, hb1']
  have e3 : a⁻¹ * b⁻¹ = (a * b)⁻¹ := by
    rw [mul_inv_rev]
    have : b⁻¹ * a⁻¹ = a⁻¹ * b⁻¹ := by
      calc b⁻¹ * a⁻¹ = (a * b)⁻¹ := by group
        _ = (b * a)⁻¹ := by rw [hab]
        _ = a⁻¹ * b⁻¹ := by group
    exact this.symm
  calc (D.w₁ * D.w₂) * (a * b) * (D.w₁ * D.w₂)⁻¹
      = D.w₁ * (D.w₂ * a * b * D.w₂⁻¹) * D.w₁⁻¹ := by group
    _ = D.w₁ * (a * b⁻¹) * D.w₁⁻¹ := by rw [e1]
    _ = a⁻¹ * b⁻¹ := e2
    _ = (a * b)⁻¹ := e3

theorem w0_sq (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) :
    (D.w₁ * D.w₂) * (D.w₁ * D.w₂) = 1 := by
  have c := w₁_w₂_comm D hs h1
  calc D.w₁ * D.w₂ * (D.w₁ * D.w₂) = D.w₁ * (D.w₂ * D.w₁) * D.w₂ := by group
    _ = D.w₁ * (D.w₁ * D.w₂) * D.w₂ := by rw [← c]
    _ = (D.w₁ * D.w₁) * (D.w₂ * D.w₂) := by group
    _ = 1 := by rw [h1.w₁_sq, w₂_sq D hs h1, z_mul_z D hs]

theorem w0_norm_H (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) :
    D.w₁ * D.w₂ ∈ normalizer (D.H : Set G) := by
  have hsub : D.w₁ * D.w₂ ∈ normalizer (D.H : Set G) := by
    apply mem_normalizer_of_conj_le
    intro x hx
    rw [w0_inv_H D hs h1 x hx]
    exact D.H.inv_mem hx
  exact hsub

theorem w0_t_comm (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) :
    D.t * (D.w₁ * D.w₂) = (D.w₁ * D.w₂) * D.t := by
  have htt := t_mul_t D hs
  have hc := w₁_w₂_comm D hs h1
  have e : D.t * (D.w₁ * D.w₂) * D.t⁻¹ = D.w₁ * D.w₂ := by
    have hw1 : D.t * D.w₁ * D.t⁻¹ = D.w₂ := rfl
    have hw2 : D.t * D.w₂ * D.t⁻¹ = D.w₁ := by
      show D.t * (D.t * D.w₁ * D.t⁻¹) * D.t⁻¹ = D.w₁
      calc D.t * (D.t * D.w₁ * D.t⁻¹) * D.t⁻¹ = (D.t * D.t) * D.w₁ * (D.t * D.t)⁻¹ := by group
        _ = D.w₁ := by rw [htt]; group
    calc D.t * (D.w₁ * D.w₂) * D.t⁻¹ = (D.t * D.w₁ * D.t⁻¹) * (D.t * D.w₂ * D.t⁻¹) := by group
      _ = D.w₂ * D.w₁ := by rw [hw1, hw2]
      _ = D.w₁ * D.w₂ := hc.symm
  calc D.t * (D.w₁ * D.w₂) = (D.t * (D.w₁ * D.w₂) * D.t⁻¹) * D.t := by group
    _ = (D.w₁ * D.w₂) * D.t := by rw [e]

omit [Finite G] in
theorem ker_conj_w0 (D : SPLNot3 G) (hw : ∀ h ∈ D.H, (D.w₁ * D.w₂) * h * (D.w₁ * D.w₂)⁻¹ = h⁻¹)
    (A : Subgroup G) : kernelOf D.H (conjBy (D.w₁ * D.w₂) A) = kernelOf D.H A := by
  ext h
  rw [mem_kernelOf_iff, mem_kernelOf_iff]
  constructor
  · rintro ⟨hH, hc⟩
    refine ⟨hH, fun a ha => ?_⟩
    have := centralizes_conjBy_iff.mp hc a ha
    rw [hw h hH] at this
    calc h * a = h * (a * h⁻¹) * h := by group
      _ = h * (h⁻¹ * a) * h := by rw [this]
      _ = a * h := by group
  · rintro ⟨hH, hc⟩
    refine ⟨hH, centralizes_conjBy_iff.mpr fun a ha => ?_⟩
    rw [hw h hH]
    have := hc a ha
    calc h⁻¹ * a = h⁻¹ * (a * h) * h⁻¹ := by group
      _ = h⁻¹ * (h * a) * h⁻¹ := by rw [this]
      _ = a * h⁻¹ := by group

end W0

section Main

variable [Finite G] (D : SPLNot3 G)

theorem H_P (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) (h3 : SPL3M2 D) :
    Normalizes D.H D.P := normalizes_sup h3.H_X₁ (H_R₂ D hs h1 h3)

omit [Finite G] in
theorem conjBy_one' (A : Subgroup G) : conjBy (1 : G) A = A := by
  ext x
  simp [mem_conjBy_iff]

theorem conj_w0_X₁ (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) (h3 : SPL3M2 D) :
    conjBy (D.w₁ * D.w₂) D.X₁ = D.X₁' := by
  rw [← conjBy_conjBy D.w₂ D.w₁ D.X₁, ← h3.X₁'_eq]
  apply conjBy_eq_self_of_comm
  intro x hx
  exact (hs.comps.comm x (h3.X₁'_le hx) D.w₂ (w₂_mem_K₂ D hs h1)).symm

theorem not_norm_X₁ (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) (h3 : SPL3M2 D) :
    conjBy (D.w₁ * D.w₂) D.X₁ ≠ D.X₁ := by
  rw [conj_w0_X₁ D hs h1 h3]
  exact h3.X₁_ne.symm

theorem not_norm_X₂ (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) (h3 : SPL3M2 D) :
    conjBy (D.w₁ * D.w₂) D.X₂ ≠ D.X₂ := by
  intro h
  have hX : conjBy D.t D.X₂ = D.X₁ := by
    show conjBy D.t (conjBy D.t D.X₁) = D.X₁
    rw [conjBy_conjBy, t_mul_t D hs, conjBy_one']
  apply not_norm_X₁ D hs h1 h3
  calc conjBy (D.w₁ * D.w₂) D.X₁ = conjBy (D.w₁ * D.w₂) (conjBy D.t D.X₂) := by rw [hX]
    _ = conjBy (D.t * (D.w₁ * D.w₂)) D.X₂ := conjBy_conjBy _ _ _
    _ = conjBy ((D.w₁ * D.w₂) * D.t) D.X₂ := by rw [w0_t_comm D hs h1]
    _ = conjBy D.t (conjBy (D.w₁ * D.w₂) D.X₂) := (conjBy_conjBy _ _ _).symm
    _ = conjBy D.t D.X₂ := by rw [h]
    _ = D.X₁ := hX

theorem w0_w₁_comm (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) :
    D.w₁ * (D.w₁ * D.w₂) = (D.w₁ * D.w₂) * D.w₁ := by
  have c := w₁_w₂_comm D hs h1
  calc D.w₁ * (D.w₁ * D.w₂) = D.w₁ * (D.w₂ * D.w₁) := by rw [c]
    _ = (D.w₁ * D.w₂) * D.w₁ := by group

theorem norm_X₃_iff_X₄ (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) (h3 : SPL3M2 D) :
    conjBy (D.w₁ * D.w₂) D.X₃ = D.X₃ ↔ conjBy (D.w₁ * D.w₂) D.X₄ = D.X₄ := by
  have hc := w0_w₁_comm D hs h1
  have hzX : conjBy D.z D.X₃ = D.X₃ := conjBy_eq_of_mem h3.H_X₃ (z_mem_H D h1)
  have h4 : ∀ B : Subgroup G, conjBy (D.w₁ * D.w₂) (conjBy D.w₁ B) =
      conjBy D.w₁ (conjBy (D.w₁ * D.w₂) B) := by
    intro B
    rw [conjBy_conjBy, conjBy_conjBy, hc]
  have hX₃ : D.X₃ = conjBy D.w₁ D.X₄ := by
    show D.X₃ = conjBy D.w₁ (conjBy D.w₁ D.X₃)
    rw [conjBy_conjBy, h1.w₁_sq, hzX]
  constructor
  · intro h
    show conjBy (D.w₁ * D.w₂) (conjBy D.w₁ D.X₃) = conjBy D.w₁ D.X₃
    rw [h4, h]
  · intro h
    rw [hX₃, h4, h]

theorem norm_X₂_of_X₃ (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) (h3 : SPL3M2 D)
    (h : conjBy (D.w₁ * D.w₂) D.X₃ = D.X₃) : conjBy (D.w₁ * D.w₂) D.X₂ = D.X₂ := by
  have h' := (norm_X₃_iff_X₄ D hs h1 h3).mp h
  rw [← comm_X₃_X₄ D hs h1 h3]
  unfold CFSG.GH74.BNPair.conjBy at h h' ⊢
  rw [Subgroup.map_commutator, h, h']

theorem ch_diff_two (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) (h3 : SPL3M2 D)
    (hR : SPLR₁ D) : D.P ⊓ conjBy (D.w₁ * D.w₂) D.P = ⊥ := by
  by_contra hne
  have hw0 := w0_inv_H D hs h1
  have hw0n := w0_norm_H D hs h1
  have hw0s := w0_sq D hs h1
  have hHP := H_P D hs h1 h3
  have hZP : D.P ⊓ conjBy (D.w₁ * D.w₂) D.P ≤ D.P := inf_le_left
  have hZH : Normalizes D.H (D.P ⊓ conjBy (D.w₁ * D.w₂) D.P) :=
    fun h hh x hx => ⟨hHP h hh x hx.1, (hHP.map_conjBy hw0n) h hh x hx.2⟩
  have hexists := exists_root_le D hs h1 h3 hR hZP hZH hne
  have claim : ∀ A : Subgroup G, (A = D.X₁ ∨ A = D.X₂ ∨ A = D.X₃ ∨ A = D.X₄) →
      Normalizes D.H A → Nat.card ↥A = D.q → A ≤ D.P ⊓ conjBy (D.w₁ * D.w₂) D.P →
      conjBy (D.w₁ * D.w₂) A = A := by
    intro A hA hAH hAc hAZ
    have hYP : conjBy (D.w₁ * D.w₂) A ≤ D.P := by
      intro y hy
      rw [mem_conjBy_iff] at hy
      have h2 : (D.w₁ * D.w₂) * y * (D.w₁ * D.w₂)⁻¹ ∈ conjBy (D.w₁ * D.w₂) D.P := (hAZ hy).2
      rw [mem_conjBy_iff] at h2
      have e : (D.w₁ * D.w₂) * ((D.w₁ * D.w₂) * y * (D.w₁ * D.w₂)⁻¹) * (D.w₁ * D.w₂)⁻¹ = y := by
        calc (D.w₁ * D.w₂) * ((D.w₁ * D.w₂) * y * (D.w₁ * D.w₂)⁻¹) * (D.w₁ * D.w₂)⁻¹
            = ((D.w₁ * D.w₂) * (D.w₁ * D.w₂)) * y * ((D.w₁ * D.w₂) * (D.w₁ * D.w₂))⁻¹ := by group
          _ = y := by rw [hw0s]; group
      rw [e] at h2
      exact h2
    have hYH : Normalizes D.H (conjBy (D.w₁ * D.w₂) A) := hAH.map_conjBy hw0n
    have hYc : Nat.card ↥(conjBy (D.w₁ * D.w₂) A) = D.q := by rw [card_conjBy]; exact hAc
    have hYne : conjBy (D.w₁ * D.w₂) A ≠ ⊥ := by
      intro h
      rw [h, Subgroup.card_bot] at hYc
      have := hs.q_ge
      omega
    have hj := exists_root_le D hs h1 h3 hR hYP hYH hYne
    have hmain : ∀ B : Subgroup G, (B = D.X₁ ∨ B = D.X₂ ∨ B = D.X₃ ∨ B = D.X₄) →
        Nat.card ↥B = D.q → B ≤ conjBy (D.w₁ * D.w₂) A → conjBy (D.w₁ * D.w₂) A = A := by
      intro B hB hBc hBY
      have hBeq : B = conjBy (D.w₁ * D.w₂) A :=
        Subgroup.eq_of_le_of_card_ge hBY (by rw [hBc, hYc])
      have hk : kernelOf D.H B = kernelOf D.H A := by
        rw [hBeq]; exact ker_conj_w0 D hw0 A
      have := kernel_inj D hs h1 h3 hR hB hA hk
      rw [← hBeq, this]
    rcases hj with hj | hj | hj | hj
    · exact hmain D.X₁ (Or.inl rfl) h3.X₁_card hj
    · exact hmain D.X₂ (Or.inr (Or.inl rfl)) (X₂_card D h3) hj
    · exact hmain D.X₃ (Or.inr (Or.inr (Or.inl rfl))) (X₃_card D h3) hj
    · exact hmain D.X₄ (Or.inr (Or.inr (Or.inr rfl))) (X₄_card D h3) hj
  rcases hexists with hj | hj | hj | hj
  · exact not_norm_X₁ D hs h1 h3
      (claim D.X₁ (Or.inl rfl) h3.H_X₁ h3.X₁_card hj)
  · exact not_norm_X₂ D hs h1 h3
      (claim D.X₂ (Or.inr (Or.inl rfl)) (H_X₂ D hs h1 h3.toSPL3X) (X₂_card D h3) hj)
  · exact not_norm_X₂ D hs h1 h3 (norm_X₂_of_X₃ D hs h1 h3
      (claim D.X₃ (Or.inr (Or.inr (Or.inl rfl))) h3.H_X₃ (X₃_card D h3) hj))
  · exact not_norm_X₂ D hs h1 h3 (norm_X₂_of_X₃ D hs h1 h3
      ((norm_X₃_iff_X₄ D hs h1 h3).mpr
        (claim D.X₄ (Or.inr (Or.inr (Or.inr rfl))) (H_X₄ D hs h1 h3) (X₄_card D h3) hj)))

end Main

theorem splLeafL42 :
    ∀ (G : Type) [Group G] [Finite G], IsKProperSimple G → ∀ D : SPLNot4 G, SPLStage4 D →
      D.toSPLNot3.L42 ∧ D.toSPLNot3.CH_diff := by
  intro G _ _ _ D hstage
  have hR : SPLR₁ D.toSPLNot3 := hstage.m1.toR₁
  exact ⟨l42_of D.toSPLNot3 hstage.setup hstage.set hstage.m2 hR,
    ch_diff_one D.toSPLNot3 hstage.setup hstage.set hstage.m2 hR,
    ch_diff_two D.toSPLNot3 hstage.setup hstage.set hstage.m2 hR⟩

end CFSG.GH74.GLS.SP.Local
