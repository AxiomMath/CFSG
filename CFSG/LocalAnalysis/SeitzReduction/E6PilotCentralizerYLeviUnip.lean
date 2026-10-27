module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCentralizerYParabolicBasic

public section

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint

local instance e6CentralizerYLeviUnipNeZeroRank : NeZero Tag.E6.rank := ⟨by decide⟩

@[expose] def yD4Pos : List (Fin Tag.E6.rank → ℤ) :=
  [![0, 1, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 1, 0],
    ![0, 1, 0, 1, 0, 0], ![0, 0, 1, 1, 0, 0], ![0, 0, 0, 1, 1, 0],
    ![0, 1, 1, 1, 0, 0], ![0, 1, 0, 1, 1, 0], ![0, 0, 1, 1, 1, 0],
    ![0, 1, 1, 1, 1, 0], ![0, 1, 1, 2, 1, 0]]

@[expose] def yZeta : ℕ → Fin Tag.E6.rank → ℤ
  | 1 => ![1, 1, 2, 2, 2, 1]
  | 2 => ![1, 1, 2, 3, 2, 1]
  | _ => ![1, 2, 2, 3, 2, 1]

@[expose] def yGam : ℕ → Fin Tag.E6.rank → ℤ
  | 1 => ![0, 0, 1, 0, 0, 0]
  | 2 => ![0, 0, 1, 1, 0, 0]
  | _ => ![0, 1, 1, 1, 0, 0]

@[expose] def yGamP : ℕ → Fin Tag.E6.rank → ℤ
  | 1 => ![0, 0, 0, 0, 1, 0]
  | 2 => ![0, 0, 0, 1, 1, 0]
  | _ => ![0, 1, 0, 1, 1, 0]

@[expose] def yFix : ℕ → Fin Tag.E6.rank → ℤ
  | 0 => ![0, 1, 0, 0, 0, 0]
  | 1 => ![0, 0, 0, 1, 0, 0]
  | 2 => ![0, 1, 0, 1, 0, 0]
  | 3 => ![0, 0, 1, 1, 1, 0]
  | 4 => ![0, 1, 1, 1, 1, 0]
  | _ => ![0, 1, 1, 2, 1, 0]

theorem yFix_check : ∀ i ∈ [0, 1, 2, 3, 4, 5],
    yFix i ∈ rootFinset .E6 ∧ iform (yFix i) yAlphaAS = 0 ∧ iform (yFix i) yBetaAS = 0 := by
  decide +kernel

theorem yD4Pos_check :
    (∀ γ ∈ rootFinset .E6, (γ 0 = 0 ∧ γ 5 = 0 ∧ 0 < height γ) ↔ γ ∈ yD4Pos) ∧
    yD4Pos.Nodup ∧ (∀ γ ∈ yD4Pos, γ ∈ rootFinset .E6 ∧ γ 0 = 0 ∧ γ 5 = 0 ∧ 0 < height γ) ∧
    (∀ γ ∈ yD4Pos.drop 4, 2 ≤ height γ) ∧ (∀ γ ∈ yD4Pos.drop 7, 3 ≤ height γ) ∧
    (∀ γ ∈ yD4Pos.drop 10, 4 ≤ height γ) ∧ (∀ γ ∈ yD4Pos, height γ < 8) := by
  decide +kernel

theorem yD4Zeta_check :
    (∀ δ ∈ yD4Pos, δ + yAlphaAS = yZeta 1 → δ = yGamP 1) ∧
    (∀ δ ∈ yD4Pos, δ + yBetaAS = yZeta 1 → δ = yGam 1) ∧
    (∀ δ ∈ yD4Pos.drop 4, δ + yAlphaAS = yZeta 2 → δ = yGamP 2) ∧
    (∀ δ ∈ yD4Pos.drop 4, δ + yBetaAS = yZeta 2 → δ = yGam 2) ∧
    (∀ δ ∈ yD4Pos.drop 7, δ + yAlphaAS = yZeta 3 → δ = yGamP 3) ∧
    (∀ δ ∈ yD4Pos.drop 7, δ + yBetaAS = yZeta 3 → δ = yGam 3) := by
  decide +kernel

theorem yHighWeights_check :
    (∀ ζ ∈ yHigh, ∀ δ ∈ rootFinset .E6, 0 < height δ → ζ + δ ∈ rootFinset .E6 → ζ + δ ∈ yHigh) ∧
    (∀ ζ ∈ yHigh, ∀ ζ' ∈ yHigh, height ζ = height ζ' → ζ = ζ') ∧
    (∀ k ∈ [1, 2, 3], yZeta k ∈ yHigh ∧ height (yZeta k) = 8 + k) ∧
    height yAlphaAS = 8 ∧ height yBetaAS = 8 ∧
    (∀ γ ∈ rootFinset .E6, 9 ≤ height γ → γ ∈ yHigh) := by
  decide +kernel

theorem yGam_check :
    (yGam 1 ∈ yD4Pos ∧ yGamP 1 ∈ yD4Pos ∧ yGam 2 ∈ yD4Pos.drop 4 ∧ yGamP 2 ∈ yD4Pos.drop 4 ∧
      yGam 3 ∈ yD4Pos.drop 7 ∧ yGamP 3 ∈ yD4Pos.drop 7) ∧
    (∀ k ∈ [1, 2, 3], yGam k ∈ rootFinset .E6 ∧ iform (yGam k) yAlphaAS = 1 ∧
      iform (yGam k) yBetaAS = -1) ∧
    yPartnerAS (yGam 1) = yGamP 1 ∧ yPartnerAS (yGam 2) = yGamP 2 ∧
      yPartnerAS (yGam 3) = yGamP 3 ∧
    (yGamP 1 + yAlphaAS = yZeta 1 ∧ yGam 1 + yBetaAS = yZeta 1) ∧
    (yGamP 2 + yAlphaAS = yZeta 2 ∧ yGam 2 + yBetaAS = yZeta 2) ∧
    (yGamP 3 + yAlphaAS = yZeta 3 ∧ yGam 3 + yBetaAS = yZeta 3) := by
  decide +kernel

section Conj

variable {K : Type} [Field K]

theorem heightSeries_le_yHighSpan (k : ℕ) :
    heightSeries .E6 K (9 + k) ≤ yHighSpan K :=
  rootSpan_mono fun γ hγ =>
    yHighWeights_check.2.2.2.2.2 γ (mem_rootFinset.2 hγ.1) (by have := hγ.2.2; omega)

theorem eq_zero_of_pinnedX_mem_heightSeries {k : ℕ} {ζ : Fin Tag.E6.rank → ℤ} (hζ : IsRoot .E6 ζ)
    (hh : height ζ = 8 + k) {d : K} (h : pinnedX .E6 K ζ d ∈ heightSeries .E6 K (9 + k)) :
    d = 0 := by
  have hT : ∀ β ∈ {α | IsRoot .E6 α ∧ 0 < height α ∧ (9 + k : ℤ) ≤ height α},
      IsRoot .E6 β ∧ 0 < height β := fun β hβ => ⟨hβ.1, hβ.2.1⟩
  have hTc : ∀ β ∈ {α | IsRoot .E6 α ∧ 0 < height α ∧ (9 + k : ℤ) ≤ height α},
      ∀ γ ∈ {α | IsRoot .E6 α ∧ 0 < height α ∧ (9 + k : ℤ) ≤ height α}, ∀ a b : ℕ, 1 ≤ a →
        1 ≤ b → IsRoot .E6 (a • β + b • γ) →
          a • β + b • γ ∈ {α | IsRoot .E6 α ∧ 0 < height α ∧ (9 + k : ℤ) ≤ height α} := by
    intro β hβ γ hγ a b ha hb hr
    obtain ⟨h1, h2, h3⟩ := nsmul_add_nsmul_mem_heightSet (τ := .E6) ⟨hβ.2.1, hβ.2.2⟩
      ⟨hγ.2.1, hγ.2.2⟩ ha hb hr
    exact ⟨h1, h2, by linarith [hβ.2.1, hγ.2.1]⟩
  have := eq_zero_of_list_prod_mem_rootSpan_annih (K := K) hT hTc (l := [ζ]) (List.nodup_singleton _)
    (fun γ hγ => by
      rw [List.mem_singleton] at hγ
      subst hγ
      exact ⟨hζ, by omega⟩)
    (fun γ hγ => by
      rw [List.mem_singleton] at hγ
      subst hγ
      intro h'
      have := h'.2.2
      omega)
    (fun _ => d) (by
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      exact h)
  exact this ζ (List.mem_singleton_self _)

theorem conj_pinnedX_step [CharP K 2] {k : ℕ} (hk : k ∈ [1, 2, 3]) {ζ : Fin Tag.E6.rank → ℤ}
    (hζ : ζ = yAlphaAS ∨ ζ = yBetaAS) {δ : Fin Tag.E6.rank → ℤ} (hδ : IsRoot .E6 δ)
    (hpos : 0 < height δ) (hkδ : (k : ℤ) ≤ height δ) (hδ8 : height δ < 8) (s l : K) :
    ∃ w ∈ heightSeries .E6 K (9 + k), pinnedX .E6 K δ s * pinnedX .E6 K ζ l *
      (pinnedX .E6 K δ s)⁻¹ =
        pinnedX .E6 K ζ l * pinnedX .E6 K (yZeta k) (if δ + ζ = yZeta k then s * l else 0) * w := by
  have hζ5 : ζ ∈ yU5 := by rcases hζ with rfl | rfl <;> simp [yU5]
  have hζr := mem_rootFinset.1 (yU5_check.1 ζ hζ5).1
  have hζh : height ζ = 8 := by
    rcases hζ with rfl | rfl
    · exact yHighWeights_check.2.2.2.1
    · exact yHighWeights_check.2.2.2.2.1
  obtain ⟨hzk, hzkh⟩ := yHighWeights_check.2.2.1 k hk
  have hzk5 := mem_yU5_of_mem_yHigh hzk
  by_cases hr : IsRoot .E6 (δ + ζ)
  · have hmem : ζ + δ ∈ yHigh := by
      rcases hζ with rfl | rfl
      · exact (yConj_check δ (mem_rootFinset.2 hδ) hpos).1 (by
          rw [add_comm]; exact mem_rootFinset.2 hr)
      · exact (yConj_check δ (mem_rootFinset.2 hδ) hpos).2 (by
          rw [add_comm]; exact mem_rootFinset.2 hr)
    have hmem' : δ + ζ ∈ yHigh := by rw [add_comm]; exact hmem
    have hht : height (δ + ζ) = height δ + 8 := by rw [height_add, hζh]
    have hδζ : δ ≠ ζ := fun e => by rw [e] at hδ8; omega
    obtain ⟨hε, hcomm⟩ := (simply_laced_root_commutator_unit.{0} Tag.E6 (Or.inr (Or.inl rfl)) hδ
      hζr hδζ (fun e => hr.ne_zero (by rw [e, neg_add_cancel]))).1 hr
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    have hε1 : (commConst Tag.E6 δ ζ (1, 1) : K) = 1 := by
      rcases hε with h | h
      · rw [h, Int.cast_one]
      · rw [h, Int.cast_neg, Int.cast_one]
        linear_combination -h2
    have hc := hcomm K s l
    rw [hε1, one_mul, commutatorElement_def] at hc
    have e : pinnedX .E6 K δ s * pinnedX .E6 K ζ l * (pinnedX .E6 K δ s)⁻¹ =
        pinnedX .E6 K (δ + ζ) (s * l) * pinnedX .E6 K ζ l := by
      rw [← hc]; group
    have hcm : Commute (pinnedX .E6 K (δ + ζ) (s * l)) (pinnedX .E6 K ζ l) :=
      commute_of_mem_yHighSpan (pinnedX_mem_rootSpan (S := {ξ | ξ ∈ yHigh}) hmem' _) hζ5 l
    by_cases hz : δ + ζ = yZeta k
    · refine ⟨1, one_mem _, ?_⟩
      rw [e, hcm.eq, ite_eq_left_iff.2 (fun h => absurd hz h), hz, mul_one]
    · refine ⟨pinnedX .E6 K (δ + ζ) (s * l), ?_, ?_⟩
      · refine pinnedX_mem_rootSpan
          (S := {α | IsRoot .E6 α ∧ 0 < height α ∧ (9 + k : ℤ) ≤ height α}) ⟨hr, by omega, ?_⟩ _
        have hne : height (δ + ζ) ≠ 8 + k := fun h' =>
          hz (yHighWeights_check.2.1 _ hmem' _ hzk (by rw [h', hzkh]))
        omega
      · rw [e, hcm.eq, ite_eq_right_iff.2 (fun h => absurd h hz), pinnedX_zero, mul_one]
  · have hδζ : δ ≠ ζ := fun e => by rw [e] at hδ8; omega
    have hc := (simply_laced_root_commutator_unit.{0} Tag.E6 (Or.inr (Or.inl rfl)) hδ hζr
      hδζ (fun e => by
        have h1 : 0 < height (-ζ) := by rw [← e]; exact hpos
        rw [height_neg] at h1
        omega)).2 hr K _ (mem_rootSubgroup.2 ⟨s, rfl⟩) _ (mem_rootSubgroup.2 ⟨l, rfl⟩)
    refine ⟨1, one_mem _, ?_⟩
    have hz : δ + ζ ≠ yZeta k := fun e => hr (by rw [e]; exact mem_rootFinset.1 (yU5_check.1 _ hzk5).1)
    rw [hc.eq, mul_inv_cancel_right, ite_eq_right_iff.2 (fun h => absurd h hz), pinnedX_zero,
      mul_one, mul_one]

theorem conj_pinnedX_zeta_step [CharP K 2] {k : ℕ} (hk : k ∈ [1, 2, 3])
    {δ : Fin Tag.E6.rank → ℤ} (hδ : IsRoot .E6 δ) (hpos : 0 < height δ) (s e : K) :
    ∃ w ∈ heightSeries .E6 K (9 + k), pinnedX .E6 K δ s * pinnedX .E6 K (yZeta k) e *
      (pinnedX .E6 K δ s)⁻¹ = pinnedX .E6 K (yZeta k) e * w := by
  obtain ⟨hzk, hzkh⟩ := yHighWeights_check.2.2.1 k hk
  have hzr := mem_rootFinset.1 (yU5_check.1 _ (mem_yU5_of_mem_yHigh hzk)).1
  have hB : pinnedX .E6 K δ s ∈ normalizer (heightSeries .E6 K (9 + k) : Set (ModGL .E6 K)) :=
    heightSeries_le_normalizer K (9 + k) (pinnedX_mem_rootSpan (S := {α | IsRoot .E6 α ∧
      0 < height α}) ⟨hδ, hpos⟩ s)
  by_cases hδz : δ = yZeta k
  · subst hδz
    refine ⟨1, one_mem _, ?_⟩
    rw [show pinnedX .E6 K (yZeta k) s * pinnedX .E6 K (yZeta k) e =
      pinnedX .E6 K (yZeta k) e * pinnedX .E6 K (yZeta k) s by
        rw [← pinnedX_add, ← pinnedX_add, add_comm], mul_inv_cancel_right, mul_one]
  by_cases hr : IsRoot .E6 (δ + yZeta k)
  · have hht : height (δ + yZeta k) = height δ + (8 + k) := by rw [height_add, hzkh]
    obtain ⟨hε, hcomm⟩ := (simply_laced_root_commutator_unit.{0} Tag.E6 (Or.inr (Or.inl rfl)) hδ
      hzr hδz (fun e => hr.ne_zero (by rw [e, neg_add_cancel]))).1 hr
    have hc := hcomm K s e
    rw [commutatorElement_def] at hc
    have hm : pinnedX .E6 K (δ + yZeta k) ((commConst Tag.E6 δ (yZeta k) (1, 1) : K) * s * e) ∈
        heightSeries .E6 K (9 + k) := pinnedX_mem_rootSpan
          (S := {α | IsRoot .E6 α ∧ 0 < height α ∧ (9 + k : ℤ) ≤ height α}) ⟨hr, by omega, by omega⟩ _
    refine ⟨(pinnedX .E6 K (yZeta k) e)⁻¹ * (pinnedX .E6 K (δ + yZeta k)
      ((commConst Tag.E6 δ (yZeta k) (1, 1) : K) * s * e)) * pinnedX .E6 K (yZeta k) e, ?_, ?_⟩
    · have hzN : pinnedX .E6 K (yZeta k) e ∈
          normalizer (heightSeries .E6 K (9 + k) : Set (ModGL .E6 K)) :=
        heightSeries_le_normalizer K (9 + k) (pinnedX_mem_rootSpan (S := {α | IsRoot .E6 α ∧
          0 < height α}) ⟨hzr, by omega⟩ e)
      have := (mem_normalizer_iff.1 (inv_mem hzN) _).1 hm
      simpa using this
    · rw [← hc]; group
  · have hc := (simply_laced_root_commutator_unit.{0} Tag.E6 (Or.inr (Or.inl rfl)) hδ hzr hδz
      (fun e' => by
        have h1 : 0 < height (-yZeta k) := by rw [← e']; exact hpos
        rw [height_neg] at h1
        omega)).2 hr K _ (mem_rootSubgroup.2 ⟨s, rfl⟩) _ (mem_rootSubgroup.2 ⟨e, rfl⟩)
    exact ⟨1, one_mem _, by rw [hc.eq, mul_inv_cancel_right, mul_one]⟩

end Conj

section Product

variable {K : Type} [Field K]

theorem conj_listProd_pinnedX [CharP K 2] {k : ℕ} (hk : k ∈ [1, 2, 3])
    {ζ δ₀ : Fin Tag.E6.rank → ℤ} (hζ : ζ = yAlphaAS ∨ ζ = yBetaAS) (h0 : δ₀ + ζ = yZeta k)
    (c : (Fin Tag.E6.rank → ℤ) → K) (l : K) :
    ∀ D : List (Fin Tag.E6.rank → ℤ), D.Nodup →
      (∀ δ ∈ D, IsRoot .E6 δ ∧ 0 < height δ ∧ (k : ℤ) ≤ height δ ∧ height δ < 8) →
      (∀ δ ∈ D, δ + ζ = yZeta k → δ = δ₀) →
      ∃ w ∈ heightSeries .E6 K (9 + k),
        (D.map fun δ => pinnedX .E6 K δ (c δ)).prod * pinnedX .E6 K ζ l *
            ((D.map fun δ => pinnedX .E6 K δ (c δ)).prod)⁻¹ =
          pinnedX .E6 K ζ l * pinnedX .E6 K (yZeta k) (if δ₀ ∈ D then c δ₀ * l else 0) * w
  | [], _, _, _ => ⟨1, one_mem _, by simp [pinnedX_zero]⟩
  | δ :: D, hnd, hD, hD0 => by
    obtain ⟨w', hw', e'⟩ := conj_listProd_pinnedX hk hζ h0 c l D (List.nodup_cons.1 hnd).2
      (fun δ' h' => hD δ' (List.mem_cons_of_mem _ h'))
      (fun δ' h' => hD0 δ' (List.mem_cons_of_mem _ h'))
    have hδ := hD δ List.mem_cons_self
    obtain ⟨a, ha, ea⟩ := conj_pinnedX_step hk hζ hδ.1 hδ.2.1 hδ.2.2.1 hδ.2.2.2 (c δ) l
    obtain ⟨b, hb, eb⟩ := conj_pinnedX_zeta_step hk hδ.1 hδ.2.1 (c δ)
      (if δ₀ ∈ D then c δ₀ * l else 0)
    have hN : pinnedX .E6 K δ (c δ) ∈
        normalizer (heightSeries .E6 K (9 + k) : Set (ModGL .E6 K)) :=
      heightSeries_le_normalizer K (9 + k) (pinnedX_mem_rootSpan (S := {α | IsRoot .E6 α ∧
        0 < height α}) ⟨hδ.1, hδ.2.1⟩ _)
    obtain ⟨hzk, -⟩ := yHighWeights_check.2.2.1 k hk
    have hcomm : Commute a (pinnedX .E6 K (yZeta k) (if δ₀ ∈ D then c δ₀ * l else 0)) :=
      commute_of_mem_yHighSpan (heightSeries_le_yHighSpan k ha) (mem_yU5_of_mem_yHigh hzk) _
    set P' := (D.map fun δ => pinnedX .E6 K δ (c δ)).prod with hP'
    set x := pinnedX .E6 K δ (c δ) with hx
    refine ⟨a * b * (x * w' * x⁻¹), mul_mem (mul_mem ha hb) ((mem_normalizer_iff.1 hN w').1 hw'),
      ?_⟩
    have hsum : (if δ + ζ = yZeta k then c δ * l else 0) +
        (if δ₀ ∈ D then c δ₀ * l else 0) = if δ₀ ∈ δ :: D then c δ₀ * l else 0 := by
      by_cases hδ0 : δ = δ₀
      · subst hδ0
        have hnot : δ ∉ D := (List.nodup_cons.1 hnd).1
        simp [h0, hnot]
      · have h1 : ¬ δ + ζ = yZeta k := fun h => hδ0 (hD0 δ List.mem_cons_self h)
        have h2 : δ₀ ∈ δ :: D ↔ δ₀ ∈ D := by
          simp only [List.mem_cons]
          exact ⟨fun h => h.resolve_left (Ne.symm hδ0), Or.inr⟩
        simp only [h1, ↓reduceIte, zero_add, h2]
    simp only [List.map_cons, List.prod_cons]
    calc x * P' * pinnedX .E6 K ζ l * (x * P')⁻¹
        = x * (P' * pinnedX .E6 K ζ l * P'⁻¹) * x⁻¹ := by group
      _ = x * (pinnedX .E6 K ζ l * pinnedX .E6 K (yZeta k) (if δ₀ ∈ D then c δ₀ * l else 0) * w') *
            x⁻¹ := by rw [e']
      _ = (x * pinnedX .E6 K ζ l * x⁻¹) *
            (x * pinnedX .E6 K (yZeta k) (if δ₀ ∈ D then c δ₀ * l else 0) * x⁻¹) *
            (x * w' * x⁻¹) := by group
      _ = pinnedX .E6 K ζ l * pinnedX .E6 K (yZeta k) (if δ + ζ = yZeta k then c δ * l else 0) * a *
            (pinnedX .E6 K (yZeta k) (if δ₀ ∈ D then c δ₀ * l else 0) * b) * (x * w' * x⁻¹) := by
          rw [ea, eb]
      _ = pinnedX .E6 K ζ l * pinnedX .E6 K (yZeta k) (if δ + ζ = yZeta k then c δ * l else 0) *
            (a * pinnedX .E6 K (yZeta k) (if δ₀ ∈ D then c δ₀ * l else 0)) * b * (x * w' * x⁻¹) := by
          group
      _ = pinnedX .E6 K ζ l * pinnedX .E6 K (yZeta k) (if δ + ζ = yZeta k then c δ * l else 0) *
            (pinnedX .E6 K (yZeta k) (if δ₀ ∈ D then c δ₀ * l else 0) * a) * b * (x * w' * x⁻¹) := by
          rw [hcomm.eq]
      _ = pinnedX .E6 K ζ l * (pinnedX .E6 K (yZeta k) (if δ + ζ = yZeta k then c δ * l else 0) *
            pinnedX .E6 K (yZeta k) (if δ₀ ∈ D then c δ₀ * l else 0)) * (a * b * (x * w' * x⁻¹)) := by
          group
      _ = _ := by rw [← pinnedX_add, hsum]

theorem coeff_eq_of_commute [CharP K 2] {k : ℕ} (hk : k ∈ [1, 2, 3])
    (D : List (Fin Tag.E6.rank → ℤ)) (hnd : D.Nodup)
    (hD : ∀ δ ∈ D, IsRoot .E6 δ ∧ 0 < height δ ∧ (k : ℤ) ≤ height δ ∧ height δ < 8)
    (hDα : ∀ δ ∈ D, δ + yAlphaAS = yZeta k → δ = yGamP k)
    (hDβ : ∀ δ ∈ D, δ + yBetaAS = yZeta k → δ = yGam k)
    (hα0 : yGamP k + yAlphaAS = yZeta k) (hβ0 : yGam k + yBetaAS = yZeta k)
    (hmα : yGamP k ∈ D) (hmβ : yGam k ∈ D) (c : (Fin Tag.E6.rank → ℤ) → K)
    (hc : (D.map fun δ => pinnedX .E6 K δ (c δ)).prod * (e6ASRep K 1 : ModGL .E6 K) =
      (e6ASRep K 1 : ModGL .E6 K) * (D.map fun δ => pinnedX .E6 K δ (c δ)).prod) :
    c (yGam k) = c (yGamP k) := by
  set P := (D.map fun δ => pinnedX .E6 K δ (c δ)).prod with hP
  obtain ⟨wα, hwα, eα⟩ := conj_listProd_pinnedX hk (Or.inl rfl) hα0 c 1 D hnd hD hDα
  obtain ⟨wβ, hwβ, eβ⟩ := conj_listProd_pinnedX hk (Or.inr rfl) hβ0 c 1 D hnd hD hDβ
  rw [ite_eq_left_iff.2 (fun h => absurd hmα h)] at eα
  rw [ite_eq_left_iff.2 (fun h => absurd hmβ h)] at eβ
  obtain ⟨hzk, hzkh⟩ := yHighWeights_check.2.2.1 k hk
  have hzk5 := mem_yU5_of_mem_yHigh hzk
  have hzr := mem_rootFinset.1 (yU5_check.1 _ hzk5).1
  have hα5 : yAlphaAS ∈ yU5 := by simp [yU5]
  have hβ5 : yBetaAS ∈ yU5 := by simp [yU5]
  set Z := pinnedX .E6 K (yZeta k) (c (yGamP k) * 1) with hZ
  set Z' := pinnedX .E6 K (yZeta k) (c (yGam k) * 1) with hZ'
  have c1 : Commute Z (pinnedX .E6 K yBetaAS 1) :=
    classD4_commute_pinnedX e6_simplyLaced hzr (mem_rootFinset.1 (yU5_check.1 _ hβ5).1)
      (yU5_check.2.2.1 _ hzk5 _ hβ5) _ _
  have c2 : Commute wα (pinnedX .E6 K yBetaAS 1) :=
    commute_of_mem_yHighSpan (heightSeries_le_yHighSpan k hwα) hβ5 1
  have c3 : Commute wα Z' := commute_of_mem_yHighSpan (heightSeries_le_yHighSpan k hwα) hzk5 _
  have hy : P * (e6ASRep K 1 : ModGL .E6 K) * P⁻¹ = (e6ASRep K 1 : ModGL .E6 K) := by
    rw [hc]; group
  have key : (e6ASRep K 1 : ModGL .E6 K) * (Z * Z' * (wα * wβ)) =
      (e6ASRep K 1 : ModGL .E6 K) := by
    calc (e6ASRep K 1 : ModGL .E6 K) * (Z * Z' * (wα * wβ))
        = pinnedX .E6 K yAlphaAS 1 * pinnedX .E6 K yBetaAS 1 * (Z * Z' * (wα * wβ)) := by
          rw [coe_e6ASRep_one_eq]
      _ = pinnedX .E6 K yAlphaAS 1 * (Z * wα) * pinnedX .E6 K yBetaAS 1 * (Z' * wβ) := by
          rw [show Z * Z' * (wα * wβ) = Z * (wα * Z') * wβ by rw [c3.eq]; group]
          rw [show pinnedX .E6 K yAlphaAS 1 * pinnedX .E6 K yBetaAS 1 * (Z * (wα * Z') * wβ) =
            pinnedX .E6 K yAlphaAS 1 * (pinnedX .E6 K yBetaAS 1 * Z) * wα * Z' * wβ by group]
          rw [← c1.eq]
          rw [show pinnedX .E6 K yAlphaAS 1 * (Z * pinnedX .E6 K yBetaAS 1) * wα * Z' * wβ =
            pinnedX .E6 K yAlphaAS 1 * Z * (pinnedX .E6 K yBetaAS 1 * wα) * Z' * wβ by group]
          rw [← c2.eq]
          group
      _ = (P * pinnedX .E6 K yAlphaAS 1 * P⁻¹) * (P * pinnedX .E6 K yBetaAS 1 * P⁻¹) := by
          rw [eα, eβ]; group
      _ = P * (e6ASRep K 1 : ModGL .E6 K) * P⁻¹ := by rw [coe_e6ASRep_one_eq]; group
      _ = _ := hy
  have hZZ : Z * Z' = (wα * wβ)⁻¹ := by
    have := mul_left_cancel (a := (e6ASRep K 1 : ModGL .E6 K))
      (key.trans (mul_one (e6ASRep K 1 : ModGL .E6 K)).symm)
    exact eq_inv_of_mul_eq_one_left this
  have hmem : pinnedX .E6 K (yZeta k) (c (yGamP k) * 1 + c (yGam k) * 1) ∈
      heightSeries .E6 K (9 + k) := by
    rw [pinnedX_add, ← hZ, ← hZ', hZZ]
    exact inv_mem (mul_mem hwα hwβ)
  have h0 := eq_zero_of_pinnedX_mem_heightSeries hzr hzkh hmem
  rw [mul_one, mul_one] at h0
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have e2 : c (yGam k) = c (yGamP k) + (c (yGamP k) + c (yGam k)) - 2 * c (yGamP k) := by ring
  rw [e2, h0, h2]
  ring

end Product

section Main

variable {K : Type} [Field K]

theorem yLeviF4_le_centralizer [CharP K 2] :
    yLeviF4 K ≤ centralizer ({(e6ASRep K 1 : ModGL .E6 K)} : Set (ModGL .E6 K)) := by
  intro m hm
  set n := (e6RepConj K 1 : ModGL .E6 K) with hn
  have hyD : (e6Rep K 1 : ModGL .E6 K) = n * (e6ASRep K 1 : ModGL .E6 K) * n⁻¹ :=
    (congrArg Subtype.val (e6RepConj_mul_e6ASRep_mul_inv (K := K) 1)).symm
  have h1 : n * m * n⁻¹ ∈ yLeviGL K := by
    rw [yLeviGL_eq_map_yLeviF4]
    exact ⟨m, hm, rfl⟩
  have h2 := mem_centralizer_singleton_iff.1 (yLeviGL_le_centralizer h1)
  rw [hyD] at h2
  refine mem_centralizer_singleton_iff.2 ?_
  have h3 : n * (m * (e6ASRep K 1 : ModGL .E6 K)) * n⁻¹ =
      n * ((e6ASRep K 1 : ModGL .E6 K) * m) * n⁻¹ := by
    calc n * (m * (e6ASRep K 1 : ModGL .E6 K)) * n⁻¹
        = n * m * n⁻¹ * (n * (e6ASRep K 1 : ModGL .E6 K) * n⁻¹) := by group
      _ = n * (e6ASRep K 1 : ModGL .E6 K) * n⁻¹ * (n * m * n⁻¹) := h2
      _ = _ := by group
  simpa using h3

theorem parabolicPosRoots_nodes16_eq :
    parabolicPosRoots .E6 nodes16 = {γ | γ ∈ yD4Pos} := by
  ext γ
  simp only [parabolicPosRoots, parabolicRoots, Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨hr, h⟩, -, hpos⟩
    refine (yD4Pos_check.1 γ (mem_rootFinset.2 hr)).1 ⟨h 0 ?_, h 5 ?_, hpos⟩
    · simp [nodes16]
    · simp [nodes16]
  · intro h
    obtain ⟨hr, h0, h5, hpos⟩ := yD4Pos_check.2.2.1 γ h
    refine ⟨⟨mem_rootFinset.1 hr, fun i hi => ?_⟩, mem_rootFinset.1 hr, hpos⟩
    have hi' : i = 0 ∨ i = 5 := by
      simp only [nodes16, Set.mem_ofPred_eq, not_and_or, not_not] at hi
      exact hi
    rcases hi' with rfl | rfl
    · exact h0
    · exact h5

theorem mem_yLeviF4_of_mem_parabolicLeviUnipotent [CharP K 2] {u : ModGL .E6 K}
    (hu : u ∈ parabolicLeviUnipotent .E6 K nodes16)
    (hc : u * (e6ASRep K 1 : ModGL .E6 K) = (e6ASRep K 1 : ModGL .E6 K) * u) :
    u ∈ yLeviF4 K := by
  obtain ⟨hcov, hnd, hmem, h2, h3, h4, h8⟩ := yD4Pos_check
  obtain ⟨z1a, z1b, z2a, z2b, z3a, z3b⟩ := yD4Zeta_check
  obtain ⟨⟨g1, g1', g2, g2', g3, g3'⟩, hgk, p1, p2, p3, ⟨s1a, s1b⟩, ⟨s2a, s2b⟩, ⟨s3a, s3b⟩⟩ :=
    yGam_check
  have hpos : ∀ δ ∈ yD4Pos, IsRoot .E6 δ ∧ 0 < height δ := fun δ h =>
    ⟨mem_rootFinset.1 (hmem δ h).1, (hmem δ h).2.2.2⟩
  have hclosed : ∀ α ∈ parabolicPosRoots .E6 nodes16, ∀ β ∈ parabolicPosRoots .E6 nodes16,
      ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → IsRoot .E6 (a • α + b • β) →
        a • α + b • β ∈ parabolicPosRoots .E6 nodes16 := by
    intro α hα β hβ a b ha hb hr
    obtain ⟨⟨-, hαJ⟩, -, hαp⟩ := hα
    obtain ⟨⟨-, hβJ⟩, -, hβp⟩ := hβ
    obtain ⟨-, hp, -⟩ := nsmul_add_nsmul_mem_heightSet (τ := .E6) (h := 1) (k := 1)
      ⟨hαp, by omega⟩ ⟨hβp, by omega⟩ ha hb hr
    refine ⟨⟨hr, fun i hi => ?_⟩, hr, hp⟩
    simp only [Pi.add_apply, Pi.smul_apply, hαJ i hi, hβJ i hi, smul_zero, add_zero]
  obtain ⟨-, hsurj, -⟩ := CFSG.LieType.Ree.list_prod_pinnedX_bijective (K := K)
    (S := parabolicPosRoots .E6 nodes16) (fun δ hδ => ⟨hδ.1.1, hδ.2.2⟩) hclosed hnd
    parabolicPosRoots_nodes16_eq.symm
  obtain ⟨c, rfl⟩ := hsurj u hu
  set f : (Fin Tag.E6.rank → ℤ) → ModGL .E6 K := fun δ => pinnedX .E6 K δ (c δ) with hf
  have hL0 := yLeviF4_le_centralizer (K := K)
  have hdrop : ∀ (n : ℕ) (L : List (Fin Tag.E6.rank → ℤ)),
      (L.map f).prod = ((L.take n).map f).prod * ((L.drop n).map f).prod := fun n L => by
    rw [← List.prod_take_mul_prod_drop (L.map f) n, List.map_take, List.map_drop]
  have hfix : ∀ i ∈ [0, 1, 2, 3, 4, 5], f (yFix i) ∈ yLeviF4 K := fun i hi => by
    obtain ⟨hr, h1, h2⟩ := yFix_check i hi
    exact pinnedX_mem_yLeviF4_of_mem_yFixedRootsAS ⟨mem_rootFinset.1 hr, h1, h2⟩ _
  have hpair : ∀ k ∈ [1, 2, 3], c (yGam k) = c (yGamP k) →
      f (yGam k) * f (yGamP k) ∈ yLeviF4 K := fun k hk he => by
    obtain ⟨hr, h1, h2⟩ := hgk k hk
    have hP : yPartnerAS (yGam k) = yGamP k := by
      rcases List.mem_cons.1 hk with rfl | hk
      · exact p1
      rcases List.mem_cons.1 hk with rfl | hk
      · exact p2
      rcases List.mem_cons.1 hk with rfl | hk
      · exact p3
      · exact absurd hk List.not_mem_nil
    have := pinnedX_mul_pinnedX_mem_yLeviF4_of_mem_yPairRootsAS (K := K)
      ⟨mem_rootFinset.1 hr, h1, h2⟩ (c (yGam k))
    rw [hP] at this
    show pinnedX .E6 K (yGam k) (c (yGam k)) * pinnedX .E6 K (yGamP k) (c (yGamP k)) ∈ yLeviF4 K
    rw [← he]
    exact this
  have hsub : ∀ (n : ℕ) (m : ℕ), (∀ γ ∈ yD4Pos.drop n, (m : ℤ) ≤ height γ) →
      ∀ δ ∈ yD4Pos.drop n, IsRoot .E6 δ ∧ 0 < height δ ∧ (m : ℤ) ≤ height δ ∧ height δ < 8 :=
    fun n m hm δ hδ => by
      have hδ' := List.mem_of_mem_drop hδ
      exact ⟨(hpos δ hδ').1, (hpos δ hδ').2, hm δ hδ, h8 δ hδ'⟩
  have hc1 : c (yGam 1) = c (yGamP 1) := coeff_eq_of_commute (by simp) yD4Pos hnd
    (hsub 0 1 (fun γ hγ => by have := (hpos γ hγ).2; omega)) z1a z1b s1a s1b
    g1' g1 c hc
  have hP1 : ((yD4Pos.take 4).map f).prod ∈ yLeviF4 K := by
    have e : ((yD4Pos.take 4).map f).prod =
        f (yFix 0) * (f (yFix 1) * (f (yGam 1) * (f (yGamP 1) * 1))) := rfl
    rw [e, mul_one]
    exact mul_mem (hfix 0 (by simp)) (mul_mem (hfix 1 (by simp)) (hpair 1 (by simp) hc1))
  have hu2 : ((yD4Pos.drop 4).map f).prod * (e6ASRep K 1 : ModGL .E6 K) =
      (e6ASRep K 1 : ModGL .E6 K) * ((yD4Pos.drop 4).map f).prod := by
    have e : ((yD4Pos.drop 4).map f).prod = (((yD4Pos.take 4).map f).prod)⁻¹ * (yD4Pos.map f).prod := by
      rw [hdrop 4 yD4Pos]; group
    have h' := mul_mem (inv_mem (hL0 hP1)) (mem_centralizer_singleton_iff.2 hc)
    rw [← e] at h'
    exact mem_centralizer_singleton_iff.1 h'
  have hc2 : c (yGam 2) = c (yGamP 2) := coeff_eq_of_commute (by simp) _ (hnd.sublist
    (List.drop_sublist _ _)) (hsub 4 2 h2) z2a z2b s2a s2b g2' g2 c hu2
  have hP2 : (((yD4Pos.drop 4).take 3).map f).prod ∈ yLeviF4 K := by
    have e : (((yD4Pos.drop 4).take 3).map f).prod =
        f (yFix 2) * (f (yGam 2) * (f (yGamP 2) * 1)) := rfl
    rw [e, mul_one]
    exact mul_mem (hfix 2 (by simp)) (hpair 2 (by simp) hc2)
  have hd47 : (yD4Pos.drop 4).drop 3 = yD4Pos.drop 7 := by rw [List.drop_drop]
  have hu3 : ((yD4Pos.drop 7).map f).prod * (e6ASRep K 1 : ModGL .E6 K) =
      (e6ASRep K 1 : ModGL .E6 K) * ((yD4Pos.drop 7).map f).prod := by
    have e : ((yD4Pos.drop 7).map f).prod =
        ((((yD4Pos.drop 4).take 3).map f).prod)⁻¹ * ((yD4Pos.drop 4).map f).prod := by
      rw [hdrop 3 (yD4Pos.drop 4), hd47]; group
    have h' := mul_mem (inv_mem (hL0 hP2)) (mem_centralizer_singleton_iff.2 hu2)
    rw [← e] at h'
    exact mem_centralizer_singleton_iff.1 h'
  have hc3 : c (yGam 3) = c (yGamP 3) := coeff_eq_of_commute (by simp) _ (hnd.sublist
    (List.drop_sublist _ _)) (hsub 7 3 h3) z3a z3b s3a s3b g3' g3 c hu3
  have hP3 : (((yD4Pos.drop 7).take 3).map f).prod ∈ yLeviF4 K := by
    have e : (((yD4Pos.drop 7).take 3).map f).prod =
        f (yGam 3) * (f (yGamP 3) * (f (yFix 3) * 1)) := rfl
    rw [e, mul_one, ← mul_assoc]
    exact mul_mem (hpair 3 (by simp) hc3) (hfix 3 (by simp))
  have hd710 : (yD4Pos.drop 7).drop 3 = yD4Pos.drop 10 := by rw [List.drop_drop]
  have hP4 : ((yD4Pos.drop 10).map f).prod ∈ yLeviF4 K := by
    have e : ((yD4Pos.drop 10).map f).prod =
        f (yFix 4) * (f (yFix 5) * 1) := rfl
    rw [e, mul_one]
    exact mul_mem (hfix 4 (by simp)) (hfix 5 (by simp))
  rw [hdrop 4 yD4Pos, hdrop 3 (yD4Pos.drop 4), hd47, hdrop 3 (yD4Pos.drop 7), hd710]
  exact mul_mem hP1 (mul_mem hP2 (mul_mem hP3 hP4))

end Main

end CFSG.SeitzReduction.E6Pilot
