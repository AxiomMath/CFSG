module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Om

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks
open CFSG.LocalAnalysis.GLTheoremA.Y10F.OmEngine (blockSpace_polar_nondegenerate
  polarBilin_isAlt two_le_finrank_blockSpace)
open QuadraticMap (polarBilin)
open LinearMap (BilinForm)

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] (X : Subgroup (V ≃ₗ[F] V))
  [Fintype X]

private theorem eq_one_of_forall_blockSpace (hpF : ((3 : ℕ) : F) ≠ 0)
    (hX : IsElemAbelian 3 X) {a : ↥X}
    (ha : ∀ D : Hyperplane X 3, blockSpace X D.1 ≠ ⊥ → a ∈ D.1) : a = 1 := by
  have hle : fixedSpaceOf X ⊔ (⨆ D : Hyperplane X 3, blockSpace X D.1) ≤
      LinearMap.ker ((a : V ≃ₗ[F] V).toLinearMap - LinearMap.id) := by
    refine sup_le (fun v hv => ?_) (iSup_le fun D => ?_)
    · simp [sub_eq_zero, (mem_fixedSpaceOf X).1 hv a]
    · by_cases hD : blockSpace X D.1 = ⊥
      · rw [hD]
        exact bot_le
      · intro v hv
        simp [sub_eq_zero, ((mem_blockSpace X).1 hv).1 a (ha D hD)]
  rw [sup_fixedSpaceOf_iSup_blockSpace X Nat.prime_three hpF hX] at hle
  refine Subtype.ext (LinearEquiv.ext fun v => ?_)
  simpa [sub_eq_zero] using hle (Submodule.mem_top (x := v))

private theorem exists_blockSpace_not_le (hpF : ((3 : ℕ) : F) ≠ 0) (hX : IsElemAbelian 3 X)
    {H : Subgroup ↥X} (hH : H.index < Nat.card X) :
    ∃ D : Hyperplane X 3, blockSpace X D.1 ≠ ⊥ ∧ ¬ H ≤ D.1 := by
  rcases H.bot_or_exists_ne_one with rfl | ⟨a, haH, ha1⟩
  · rw [Subgroup.index_bot] at hH
    exact absurd hH (lt_irrefl _)
  by_contra hcon
  exact ha1 (eq_one_of_forall_blockSpace X hpF hX fun D hD =>
    not_not.1 (fun hn => hcon ⟨D, hD, fun hle => hn (hle haH)⟩))

private theorem exists_three_blockSpace (hpF : ((3 : ℕ) : F) ≠ 0) (hX : IsElemAbelian 3 X)
    (hcard : Nat.card X = 3 ^ 3) :
    ∃ D₁ D₂ D₃ : Hyperplane X 3, D₁ ≠ D₂ ∧ D₁ ≠ D₃ ∧ D₂ ≠ D₃ ∧ blockSpace X D₁.1 ≠ ⊥ ∧
      blockSpace X D₂.1 ≠ ⊥ ∧ blockSpace X D₃.1 ≠ ⊥ := by
  obtain ⟨D₁, h₁, -⟩ := exists_blockSpace_not_le X hpF hX (H := ⊤)
    (by rw [Subgroup.index_top, hcard]; norm_num)
  obtain ⟨D₂, h₂, h₁₂⟩ := exists_blockSpace_not_le X hpF hX (H := D₁.1)
    (by rw [D₁.2, hcard]; norm_num)
  obtain ⟨D₃, h₃, h₁₂₃⟩ := exists_blockSpace_not_le X hpF hX (H := D₁.1 ⊓ D₂.1)
    (lt_of_le_of_lt Subgroup.index_inf_le (by rw [D₁.2, D₂.2, hcard]; norm_num))
  refine ⟨D₁, D₂, D₃, fun h => h₁₂ (by rw [h]), fun h => h₁₂₃ ?_, fun h => h₁₂₃ ?_, h₁, h₂, h₃⟩
  · rw [← h]
    exact inf_le_left
  · rw [← h]
    exact inf_le_right

theorem SG.exists_blockPair (hpF : ((3 : ℕ) : F) ≠ 0) (hX : IsElemAbelian 3 X)
    (hcard : Nat.card X = 3 ^ 3) (d : ↥X) :
    ∃ D E : Hyperplane X 3, D ≠ E ∧ blockSpace X D.1 ≠ ⊥ ∧ blockSpace X E.1 ≠ ⊥ ∧
      (d ∈ D.1 ↔ d ∈ E.1) := by
  obtain ⟨D₁, D₂, D₃, h₁₂, h₁₃, h₂₃, h₁, h₂, h₃⟩ := exists_three_blockSpace X hpF hX hcard
  by_cases e₁₂ : d ∈ D₁.1 ↔ d ∈ D₂.1
  · exact ⟨D₁, D₂, h₁₂, h₁, h₂, e₁₂⟩
  by_cases e₁₃ : d ∈ D₁.1 ↔ d ∈ D₃.1
  · exact ⟨D₁, D₃, h₁₃, h₁, h₃, e₁₃⟩
  exact ⟨D₂, D₃, h₂₃, h₂, h₃, by tauto⟩

theorem SG.blockPair_spec [FiniteDimensional F V] [CharP F 2] {Q : QuadraticForm F V}
    (hQ : (polarBilin Q).Nondegenerate) (hXO : X ≤ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hX : IsElemAbelian 3 X) {D E : Hyperplane X 3} (hDE : D ≠ E)
    (hD : blockSpace X D.1 ≠ ⊥) (hE : blockSpace X E.1 ≠ ⊥) :
    4 ≤ Module.finrank F ↥(blockSpace X D.1 ⊔ blockSpace X E.1) ∧
      (BilinForm.restrict (polarBilin Q) (blockSpace X D.1 ⊔ blockSpace X E.1)).Nondegenerate ∧
      (∀ (a : ↥X) (n : ℕ), ∀ u ∈ blockSpace X D.1 ⊔ blockSpace X E.1,
        ((a : V ≃ₗ[F] V) ^ n) u ∈ blockSpace X D.1 ⊔ blockSpace X E.1) ∧
      (∀ a : ↥X, a ∉ D.1 → a ∉ E.1 → ∀ u ∈ blockSpace X D.1 ⊔ blockSpace X E.1,
        (a : V ≃ₗ[F] V) u = u → u = 0) ∧
      ∀ l ∈ D.1 ⊓ E.1, ∀ u ∈ blockSpace X D.1 ⊔ blockSpace X E.1, (l : V ≃ₗ[F] V) u = u := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hpF : ((3 : ℕ) : F) ≠ 0 := fun h =>
    absurd ((CharP.cast_eq_zero_iff F 2 3).1 h) (by norm_num)
  have hB : ∀ a : ↥X, ∀ u v : V,
      polarBilin Q ((a : V ≃ₗ[F] V) u) ((a : V ≃ₗ[F] V) v) = polarBilin Q u v := fun a u v =>
    TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup (hXO a.2) u v
  have hdisj : Disjoint (blockSpace X D.1) (blockSpace X E.1) :=
    (iSupIndep_blockSpace X Nat.prime_three hpF hX).pairwiseDisjoint hDE
  have hort : ∀ {D' E' : Hyperplane X 3}, D' ≠ E' → ∀ {u v : V}, u ∈ blockSpace X D'.1 →
      v ∈ blockSpace X E'.1 → polarBilin Q u v = 0 := fun {_ _} hne {_ _} hu hv =>
    blockSpace_bilinear_orthogonal X Nat.prime_three hpF hX _ hB hne hu hv
  refine ⟨?_, ?_, fun a n u hu => ?_, fun a haD haE u hu hfix => ?_, fun l hl u hu => ?_⟩
  · have h := Submodule.finrank_sup_add_finrank_inf_eq (blockSpace X D.1) (blockSpace X E.1)
    rw [hdisj.eq_bot, finrank_bot] at h
    have h₁ := two_le_finrank_blockSpace X h2 hQ Nat.prime_three hpF hX hB D hD
    have h₂ := two_le_finrank_blockSpace X h2 hQ Nat.prime_three hpF hX hB E hE
    omega
  · refine BilinForm.nondegenerate_restrict_of_disjoint_orthogonal _ (polarBilin_isAlt h2 Q).isRefl
      (Submodule.disjoint_def.2 fun u hu hperp => ?_)
    obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := Submodule.mem_sup.1 hu
    rw [BilinForm.mem_orthogonal_iff] at hperp
    have k₁ := (blockSpace_polar_nondegenerate X hQ Nat.prime_three hpF hX hB D).2 ⟨u₁, hu₁⟩
      fun w => by
        have h := hperp w (Submodule.mem_sup_left w.2)
        rw [map_add, hort hDE w.2 hu₂, add_zero] at h
        exact h
    have k₂ := (blockSpace_polar_nondegenerate X hQ Nat.prime_three hpF hX hB E).2 ⟨u₂, hu₂⟩
      fun w => by
        have h := hperp w (Submodule.mem_sup_right w.2)
        rw [map_add, hort hDE.symm w.2 hu₁, zero_add] at h
        exact h
    rw [show u₁ = 0 from congrArg Subtype.val k₁, show u₂ = 0 from congrArg Subtype.val k₂,
      add_zero]
  · obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := Submodule.mem_sup.1 hu
    rw [map_add]
    exact Submodule.add_mem_sup (blockSpace_pow_mem X Nat.prime_three hpF hX a hu₁)
      (blockSpace_pow_mem X Nat.prime_three hpF hX a hu₂)
  · obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := Submodule.mem_sup.1 hu
    rw [map_add] at hfix
    have ha₁ := blockSpace_invariant X Nat.prime_three hpF hX (a := a) hu₁
    have ha₂ := blockSpace_invariant X Nat.prime_three hpF hX (a := a) hu₂
    have hmem : (a : V ≃ₗ[F] V) u₁ - u₁ = u₂ - (a : V ≃ₗ[F] V) u₂ := by
      rw [sub_eq_sub_iff_add_eq_add, hfix, add_comm]
    have h0 : (a : V ≃ₗ[F] V) u₁ - u₁ = 0 := Submodule.disjoint_def.1 hdisj _
      (Submodule.sub_mem _ ha₁ hu₁) (by rw [hmem]; exact Submodule.sub_mem _ hu₂ ha₂)
    have k₁ := eq_zero_of_fixed_mem_blockSpace X Nat.prime_three hpF hX haD hu₁ (sub_eq_zero.1 h0)
    rw [hmem, sub_eq_zero] at h0
    rw [k₁, eq_zero_of_fixed_mem_blockSpace X Nat.prime_three hpF hX haE hu₂ h0.symm, add_zero]
  · obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := Submodule.mem_sup.1 hu
    rw [map_add, ((mem_blockSpace X).1 hu₁).1 l hl.1, ((mem_blockSpace X).1 hu₂).1 l hl.2]

end CFSG.LocalAnalysis.GLTheoremA.S265

end
