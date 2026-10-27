module

public import CFSG.GH74.GLS.Stage4.RestL94
public import CFSG.GH74.GLS.Stage4.RestPreA
public import CFSG.GH74.GLS.Stage4.RestMirror

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage4 CFSG.GH74.GLS.Stage4.Hex
  CFSG.GH74.BNPair CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] {D : Ch6Notation G}

theorem Ch6Notation.shape_true_eq (hS : D.Shape true true false true) :
    (D.P : Set G) = (D.X₁ : Set G) * (D.X₂ : Set G) * (conjBy D.a D.X₁' : Set G) *
      (conjBy D.a D.X₂' : Set G) * (conjBy (D.a ^ 2) D.X₁ : Set G) *
      (conjBy (D.a ^ 2) D.X₂' : Set G) := by
  simpa [Ch6Notation.Shape, Ch6Notation.A, Ch6Notation.B] using hS

theorem Ch6Notation.root_le_P_of_shape (hS : D.Shape true true false true) {i : ℤ} (hi : 1 ≤ i)
    (hi6 : i ≤ 6) : D.root i ≤ D.P := by
  have hS' := Ch6Notation.shape_true_eq hS
  intro x hx
  have hmem : x ∈ (D.P : Set G) := by
    rw [hS']
    have e1 : (1 : G) ∈ D.X₁ := D.X₁.one_mem
    have e2 : (1 : G) ∈ D.X₂ := D.X₂.one_mem
    have e3 : (1 : G) ∈ conjBy D.a D.X₁' := (conjBy D.a D.X₁').one_mem
    have e4 : (1 : G) ∈ conjBy D.a D.X₂' := (conjBy D.a D.X₂').one_mem
    have e5 : (1 : G) ∈ conjBy (D.a ^ 2) D.X₁ := (conjBy (D.a ^ 2) D.X₁).one_mem
    have e6 : (1 : G) ∈ conjBy (D.a ^ 2) D.X₂' := (conjBy (D.a ^ 2) D.X₂').one_mem
    have : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [root_p1] at hx
      simpa using six_mem_mul hx e2 e3 e4 e5 e6
    · rw [root_p2] at hx
      simpa using six_mem_mul e1 e2 e3 e4 e5 hx
    · rw [root_p3] at hx
      simpa using six_mem_mul e1 e2 hx e4 e5 e6
    · rw [root_p4] at hx
      simpa using six_mem_mul e1 hx e3 e4 e5 e6
    · rw [root_p5] at hx
      simpa using six_mem_mul e1 e2 e3 e4 hx e6
    · rw [root_p6] at hx
      simpa using six_mem_mul e1 e2 e3 hx e5 e6
  exact hmem

theorem Ch6Notation.P_gen_of_shape (hS : D.Shape true true false true) :
    D.P = ⨆ k ∈ Set.Icc (1 : ℤ) 6, D.root k := by
  apply le_antisymm
  · intro x hx
    have hx' : x ∈ (D.P : Set G) := hx
    rw [Ch6Notation.shape_true_eq hS] at hx'
    refine set_six_subset_of_le _ _ _ _ _ _ (⨆ k ∈ Set.Icc (1 : ℤ) 6, D.root k) ?_ ?_ ?_ ?_ ?_ ?_ hx'
    · exact le_iSup₂_of_le 1 ⟨le_refl _, by norm_num⟩ (by rw [root_p1])
    · exact le_iSup₂_of_le 4 ⟨by norm_num, by norm_num⟩ (by rw [root_p4])
    · exact le_iSup₂_of_le 3 ⟨by norm_num, by norm_num⟩ (by rw [root_p3])
    · exact le_iSup₂_of_le 6 ⟨by norm_num, by norm_num⟩ (by rw [root_p6])
    · exact le_iSup₂_of_le 5 ⟨by norm_num, by norm_num⟩ (by rw [root_p5])
    · exact le_iSup₂_of_le 2 ⟨by norm_num, by norm_num⟩ (by rw [root_p2])
  · exact iSup₂_le fun k hk => Ch6Notation.root_le_P_of_shape hS hk.1 hk.2

theorem Ch6Pre.long_A2_of_shape (h : Ch6Pre D) (hS : D.Shape true true false true) :
    (∀ x ∈ D.root 2, ∀ y ∈ D.root 4, x * y = y * x) ∧
      (∀ x ∈ D.root 4, ∀ y ∈ D.root 6, x * y = y * x) ∧
        (∀ x ∈ D.root 2, ∀ y ∈ D.root 6, ⁅x, y⁆ ∈ D.root 4) := by
  have hX2c := h.pre.X₂_central
  have h2P := Ch6Notation.root_le_P_of_shape hS (i := 2) (by norm_num) (by norm_num)
  have h6P := Ch6Notation.root_le_P_of_shape hS (i := 6) (by norm_num) (by norm_num)
  refine ⟨?_, ?_, ?_⟩
  · intro x hx y hy
    rw [root_p4] at hy
    exact (hX2c y hy x (h2P hx)).symm
  · intro x hx y hy
    rw [root_p4] at hx
    exact hX2c x hx y (h6P hy)
  · intro x hx y hy
    have hx' : x ∈ conjBy (D.a ^ 2) (D.B true) := by
      rw [Ch6Notation.B_true]
      rw [root_p2] at hx
      exact hx
    have hy' : y ∈ conjBy D.a (D.B true) := by
      rw [Ch6Notation.B_true]
      rw [root_p6] at hy
      exact hy
    rw [root_p4]
    exact h.pre.comm_R true true false true hS _ (by simp [Ch6Notation.Rfac]) _
      (by simp [Ch6Notation.Rfac]) x hx' y hy'

theorem Ch6Pre.core_of_shape (h : Ch6Pre D) (hS : D.Shape true true false true) : Ch6Core D :=
  { h.basics with
    P_pGroup := h.pre.P_pGroup
    P_card := h.pre.P_card
    P_normH := h.pre.P_normH
    P_gen := Ch6Notation.P_gen_of_shape hS
    opp := h.opp
    F_normB := h.pre.F_normB
    P₀_normP := h.pre.P₀_normP
    Sylow_PP₀ := h.pre.Sylow_PP₀
    inequiv := fun i j hi hi6 hj hj6 hij =>
      h.pre.inequiv i j ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
        (Ch6Notation.root_le_P_of_shape hS hi hi6) (Ch6Notation.root_le_P_of_shape hS hj hj6) hij
    long_A2 := h.long_A2_of_shape hS }

theorem Ch6Notation.shape_false_eq (hS : D.Shape false true true true) :
    (D.P : Set G) = (D.X₁ : Set G) * (D.X₂ : Set G) * (conjBy D.a D.X₁ : Set G) *
      (conjBy D.a D.X₂' : Set G) * (conjBy (D.a ^ 2) D.X₁' : Set G) *
      (conjBy (D.a ^ 2) D.X₂' : Set G) := by
  simpa [Ch6Notation.Shape, Ch6Notation.A, Ch6Notation.B] using hS

theorem Ch6Notation.mirror_root_le_P (hb : Ch6Basics D) (hS : D.Shape false true true true) {i : ℤ}
    (hi : 1 ≤ i) (hi6 : i ≤ 6) : D.mirror.root i ≤ D.P := by
  have hS' := Ch6Notation.shape_false_eq hS
  intro x hx
  have hmem : x ∈ (D.P : Set G) := by
    rw [hS']
    have e1 : (1 : G) ∈ D.X₁ := D.X₁.one_mem
    have e2 : (1 : G) ∈ D.X₂ := D.X₂.one_mem
    have e3 : (1 : G) ∈ conjBy D.a D.X₁ := (conjBy D.a D.X₁).one_mem
    have e4 : (1 : G) ∈ conjBy D.a D.X₂' := (conjBy D.a D.X₂').one_mem
    have e5 : (1 : G) ∈ conjBy (D.a ^ 2) D.X₁' := (conjBy (D.a ^ 2) D.X₁').one_mem
    have e6 : (1 : G) ∈ conjBy (D.a ^ 2) D.X₂' := (conjBy (D.a ^ 2) D.X₂').one_mem
    have : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hb.mirror_root_1, root_p1] at hx
      simpa using six_mem_mul hx e2 e3 e4 e5 e6
    · rw [hb.mirror_root_2, root_p6] at hx
      simpa using six_mem_mul e1 e2 e3 hx e5 e6
    · rw [hb.mirror_root_3, root_m5] at hx
      simpa using six_mem_mul e1 e2 e3 e4 hx e6
    · rw [hb.mirror_root_4, root_p4] at hx
      simpa using six_mem_mul e1 hx e3 e4 e5 e6
    · rw [hb.mirror_root_5, root_m3] at hx
      simpa using six_mem_mul e1 e2 hx e4 e5 e6
    · rw [hb.mirror_root_6, root_p2] at hx
      simpa using six_mem_mul e1 e2 e3 e4 e5 hx
  exact hmem

theorem Ch6Notation.P_gen_of_shape_mirror (hb : Ch6Basics D) (hS : D.Shape false true true true) :
    D.P = ⨆ k ∈ Set.Icc (1 : ℤ) 6, D.mirror.root k := by
  apply le_antisymm
  · intro x hx
    have hx' : x ∈ (D.P : Set G) := hx
    rw [Ch6Notation.shape_false_eq hS] at hx'
    refine set_six_subset_of_le _ _ _ _ _ _ (⨆ k ∈ Set.Icc (1 : ℤ) 6, D.mirror.root k) ?_ ?_ ?_ ?_ ?_ ?_
      hx'
    · exact le_iSup₂_of_le 1 ⟨le_refl _, by norm_num⟩ (by rw [hb.mirror_root_1, root_p1])
    · exact le_iSup₂_of_le 4 ⟨by norm_num, by norm_num⟩ (by rw [hb.mirror_root_4, root_p4])
    · exact le_iSup₂_of_le 5 ⟨by norm_num, by norm_num⟩ (by rw [hb.mirror_root_5, root_m3])
    · exact le_iSup₂_of_le 2 ⟨by norm_num, by norm_num⟩ (by rw [hb.mirror_root_2, root_p6])
    · exact le_iSup₂_of_le 3 ⟨by norm_num, by norm_num⟩ (by rw [hb.mirror_root_3, root_m5])
    · exact le_iSup₂_of_le 6 ⟨by norm_num, by norm_num⟩ (by rw [hb.mirror_root_6, root_p2])
  · exact iSup₂_le fun k hk => Ch6Notation.mirror_root_le_P hb hS hk.1 hk.2

@[expose] def mirrorIdx (i : ℤ) : ℤ :=
  if i = 1 then 1 else if i = 2 then 6 else if i = 3 then -5 else if i = 4 then 4
  else if i = 5 then -3 else 2

theorem mirrorIdx_isRoot {i : ℤ} (hi : 1 ≤ i) (hi6 : i ≤ 6) : IsRoot 6 (mirrorIdx i) := by
  have : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [mirrorIdx, IsRoot]

theorem mirrorIdx_inj {i j : ℤ} (hi : 1 ≤ i) (hi6 : i ≤ 6) (hj : 1 ≤ j) (hj6 : j ≤ 6)
    (h : mirrorIdx i = mirrorIdx j) : i = j := by
  have hi' : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by omega
  have hj' : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 := by omega
  rcases hi' with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj' with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [mirrorIdx] at h ⊢

theorem Ch6Basics.mirror_root_eq (h : Ch6Basics D) {i : ℤ} (hi : 1 ≤ i) (hi6 : i ≤ 6) :
    D.mirror.root i = D.root (mirrorIdx i) := by
  have : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa [mirrorIdx] using h.mirror_root_1
  · simpa [mirrorIdx] using h.mirror_root_2
  · simpa [mirrorIdx] using h.mirror_root_3
  · simpa [mirrorIdx] using h.mirror_root_4
  · simpa [mirrorIdx] using h.mirror_root_5
  · simpa [mirrorIdx] using h.mirror_root_6

theorem Ch6Pre.long_A2_of_shape_mirror (h : Ch6Pre D) (hS : D.Shape false true true true) :
    (∀ x ∈ D.mirror.root 2, ∀ y ∈ D.mirror.root 4, x * y = y * x) ∧
      (∀ x ∈ D.mirror.root 4, ∀ y ∈ D.mirror.root 6, x * y = y * x) ∧
        (∀ x ∈ D.mirror.root 2, ∀ y ∈ D.mirror.root 6, ⁅x, y⁆ ∈ D.mirror.root 4) := by
  have hb := h.basics
  have hX2c := h.pre.X₂_central
  have h2P := Ch6Notation.mirror_root_le_P hb hS (i := 2) (by norm_num) (by norm_num)
  have h6P := Ch6Notation.mirror_root_le_P hb hS (i := 6) (by norm_num) (by norm_num)
  refine ⟨?_, ?_, ?_⟩
  · intro x hx y hy
    rw [hb.mirror_root_4, root_p4] at hy
    exact (hX2c y hy x (h2P hx)).symm
  · intro x hx y hy
    rw [hb.mirror_root_4, root_p4] at hx
    exact hX2c x hx y (h6P hy)
  · intro x hx y hy
    have hx' : x ∈ conjBy D.a (D.B true) := by
      rw [Ch6Notation.B_true]
      rw [hb.mirror_root_2, root_p6] at hx
      exact hx
    have hy' : y ∈ conjBy (D.a ^ 2) (D.B true) := by
      rw [Ch6Notation.B_true]
      rw [hb.mirror_root_6, root_p2] at hy
      exact hy
    rw [hb.mirror_root_4, root_p4]
    exact h.pre.comm_R false true true true hS _ (by simp [Ch6Notation.Rfac]) _
      (by simp [Ch6Notation.Rfac]) x hx' y hy'

theorem Ch6Pre.core_of_shape_mirror (h : Ch6Pre D) (hS : D.Shape false true true true) :
    Ch6Core D.mirror :=
  { h.basics.mirror with
    P_pGroup := h.pre.P_pGroup
    P_card := h.pre.P_card
    P_normH := h.pre.P_normH
    P_gen := Ch6Notation.P_gen_of_shape_mirror h.basics hS
    opp := h.opp
    F_normB := h.pre.F_normB
    P₀_normP := h.pre.P₀_normP
    Sylow_PP₀ := h.pre.Sylow_PP₀
    inequiv := fun i j hi hi6 hj hj6 hij => by
      show ¬ HEquiv D.H (D.mirror.root i) (D.mirror.root j)
      have hle : ∀ k : ℤ, 1 ≤ k → k ≤ 6 → D.root (mirrorIdx k) ≤ D.P := fun k hk hk6 => by
        rw [← h.basics.mirror_root_eq hk hk6]
        exact Ch6Notation.mirror_root_le_P h.basics hS hk hk6
      rw [h.basics.mirror_root_eq hi hi6, h.basics.mirror_root_eq hj hj6]
      exact h.pre.inequiv _ _ (mirrorIdx_isRoot hi hi6) (mirrorIdx_isRoot hj hj6) (hle i hi hi6)
        (hle j hj hj6) fun e => hij (mirrorIdx_inj hi hi6 hj hj6 e)
    long_A2 := h.long_A2_of_shape_mirror hS }

@[expose] def Ch6Notation.AllX2 (D : Ch6Notation G) : Prop :=
  ∃ α γ : Bool, α ≠ γ ∧ D.Shape α false γ false

theorem Ch6Pre.core_or_allX2 (h : Ch6Pre D) : (∃ D' : Ch6Notation G, Ch6Core D') ∨ D.AllX2 := by
  obtain ⟨α, β, γ, δ, hS, -⟩ := h.pre.shape
  obtain ⟨hαγ, hβδ⟩ := h.shape_ne hS
  subst hβδ
  cases α <;> cases β <;> cases γ
  · exact absurd rfl hαγ
  · exact Or.inr ⟨false, true, by decide, hS⟩
  · exact absurd rfl hαγ
  · exact Or.inl ⟨D.mirror, h.core_of_shape_mirror hS⟩
  · exact Or.inr ⟨true, false, by decide, hS⟩
  · exact absurd rfl hαγ
  · exact Or.inl ⟨D, h.core_of_shape hS⟩
  · exact absurd rfl hαγ

@[expose] def Ch6RestT2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Std G → pRank 2 G = 3 →
    ∀ (Gs : Type) [Group Gs] (q₁ q₂ : ℕ), IsTwoCentralG2TypeG2At G Gs q₁ q₂ →
      ¬ (q₁ = 9 ∧ q₂ = 9) → (¬ ∃ n : ℕ, 3 ≤ n ∧ q₁ = 3 ^ n ∧ q₂ = 3 ^ n) →
        ∃ D : Ch6Notation G, Ch6Pre D

@[expose] def Ch6RestAllX2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Std G → pRank 2 G = 3 →
    ∀ (Gs : Type) [Group Gs] (q₁ q₂ : ℕ), IsTwoCentralG2TypeG2At G Gs q₁ q₂ →
      ∀ D : Ch6Notation G, Ch6Pre D → D.AllX2 → ∃ D' : Ch6Notation G, Ch6Core D'

theorem ch6RestMain_of (hT2 : Ch6RestT2) (hX2 : Ch6RestAllX2) : Ch6RestMain := by
  intro G _ _ hStd hr Gs _ q₁ q₂ hAt h99 hn
  obtain ⟨D, hD⟩ := hT2 G hStd hr Gs q₁ q₂ hAt h99 hn
  rcases hD.core_or_allX2 with h | h
  · exact h
  · exact hX2 G hStd hr Gs q₁ q₂ hAt D hD h

theorem Ch6Pre.outPlus (hX2 : Ch6RestAllX2) (hL : Ch6RestL92) (hZ : Ch6RestZClass) {G : Type}
    [Group G] [Finite G] (hStd : Std G) (hr : pRank 2 G = 3) {Gs : Type} [Group Gs] {q₁ q₂ : ℕ}
    (hAt : IsTwoCentralG2TypeG2At G Gs q₁ q₂) {D : Ch6Notation G} (hD : Ch6Pre D) :
    Ch6OutPlus G := by
  rcases hD.core_or_allX2 with ⟨D', hD'⟩ | h
  · exact (Ch6Post.mk hD' (hL G hStd hr Gs q₁ q₂ hAt D' hD') (hZ G hStd hr Gs q₁ q₂ hAt D' hD')).outPlus
  · obtain ⟨D', hD'⟩ := hX2 G hStd hr Gs q₁ q₂ hAt D hD h
    exact (Ch6Post.mk hD' (hL G hStd hr Gs q₁ q₂ hAt D' hD') (hZ G hStd hr Gs q₁ q₂ hAt D' hD')).outPlus

theorem ch6CaseRest_of_leaves4 (hT2 : Ch6RestT2) (hX2 : Ch6RestAllX2) (hL : Ch6RestL92)
    (hZ : Ch6RestZClass) : Ch6CaseRest :=
  ch6CaseRest_of_leaves (ch6RestMain_of hT2 hX2) hL hZ

theorem ch6CaseRestPlus_of_leaves4 (hT2 : Ch6RestT2) (hX2 : Ch6RestAllX2) (hL : Ch6RestL92)
    (hZ : Ch6RestZClass) : Ch6CaseRestPlus :=
  ch6CaseRestPlus_of_leaves (ch6RestMain_of hT2 hX2) hL hZ

end CFSG.GH74.GLS.Stage4.Rest
