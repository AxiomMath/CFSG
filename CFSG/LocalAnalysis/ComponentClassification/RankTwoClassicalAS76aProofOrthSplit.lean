module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOrthDual
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofHermitian
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalDefs

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Module Matrix QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open scoped Matrix

variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]

omit [DecidableEq ι] in
theorem rank_eq_sub_two_of_split {N E₁ E₂ : Matrix ι ι K} (hsum : N = E₁ + E₂)
    (h1 : E₁.rank = 2) (hker : ∀ v, N *ᵥ v = 0 → E₂ *ᵥ v = 0) {x y : ι → K}
    (hx : E₂ *ᵥ x = 0) (hy : E₂ *ᵥ y = 0)
    (hxy : ∀ a b : K, a • (N *ᵥ x) + b • (N *ᵥ y) = 0 → a = 0 ∧ b = 0) :
    E₂.rank = N.rank - 2 := by
  rw [rank_eq_finrank_range, rank_eq_finrank_range] at *
  have hle : LinearMap.range N.mulVecLin ≤
      LinearMap.range E₁.mulVecLin ⊔ LinearMap.range E₂.mulVecLin := by
    rintro _ ⟨v, rfl⟩
    rw [hsum, Matrix.mulVecLin_add, LinearMap.add_apply]
    exact Submodule.add_mem_sup ⟨v, rfl⟩ ⟨v, rfl⟩
  have h2 := (Submodule.finrank_mono hle).trans
    (Submodule.finrank_add_le_finrank_add_finrank _ _)
  set S := Submodule.span K (Set.range ![x, y]) with hS
  have hmemS : ∀ v ∈ S, ∃ a b : K, v = a • x + b • y := by
    intro v hv
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hv
    exact ⟨c 0, c 1, by simp [Fin.sum_univ_two]⟩
  have hli : LinearIndependent K ![x, y] := by
    refine LinearIndependent.pair_iff.mpr fun a b hab => hxy a b ?_
    rw [← mulVec_smul, ← mulVec_smul, ← mulVec_add, hab, mulVec_zero]
  have hSdim : finrank K S = 2 := by rw [hS, finrank_span_eq_card hli, Fintype.card_fin]
  have hkle : LinearMap.ker N.mulVecLin ⊔ S ≤ LinearMap.ker E₂.mulVecLin := by
    refine sup_le (fun v hv => hker v hv) fun v hv => ?_
    obtain ⟨a, b, rfl⟩ := hmemS v hv
    change E₂ *ᵥ (a • x + b • y) = 0
    rw [mulVec_add, mulVec_smul, mulVec_smul, hx, hy, smul_zero, smul_zero, add_zero]
  have hdis : LinearMap.ker N.mulVecLin ⊓ S = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    obtain ⟨hvN, hvS⟩ := Submodule.mem_inf.mp hv
    obtain ⟨a, b, rfl⟩ := hmemS v hvS
    have h3 : a • (N *ᵥ x) + b • (N *ᵥ y) = 0 := by
      have : N *ᵥ (a • x + b • y) = 0 := hvN
      rwa [mulVec_add, mulVec_smul, mulVec_smul] at this
    obtain ⟨rfl, rfl⟩ := hxy a b h3
    simp
  have h5 := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.ker N.mulVecLin) S
  rw [hdis, finrank_bot, add_zero, hSdim] at h5
  have h6 := Submodule.finrank_mono hkle
  have h7 := LinearMap.finrank_range_add_finrank_ker N.mulVecLin
  have h8 := LinearMap.finrank_range_add_finrank_ker E₂.mulVecLin
  omega

omit [DecidableEq ι] in
theorem polarBilin_mulVec_of_isometry (Q : QuadraticForm K (ι → K)) {D : Matrix ι ι K}
    (hD : ∀ v, Q (D *ᵥ v) = Q v) (u v : ι → K) :
    Q.polarBilin (D *ᵥ u) (D *ᵥ v) = Q.polarBilin u v := by
  rw [polarBilin_apply_apply, polarBilin_apply_apply, polar, polar, ← mulVec_add, hD, hD, hD]

theorem one_add_two_smul_mul {P P' : Matrix ι ι K} (hPP : P * P = P) (hP'P' : P' * P' = P')
    (hPP' : P * P' = 0) (hP'P : P' * P = 0) {a b a' b' : K} (ha : a + a' + a * a' = 0)
    (hb : b + b' + b * b' = 0) : (1 + a • P + b • P') * (1 + a' • P + b' • P') = 1 := by
  simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_smul_comm, hPP, hP'P', hPP', hP'P,
    smul_zero, add_zero]
  calc (1 : Matrix ι ι K) + a • P + b • P' + (a' • P + (a * a') • P) + (b' • P' + (b * b') • P')
      = 1 + (a + a' + a * a') • P + (b + b' + b * b') • P' := by
        simp only [add_smul]; abel
    _ = 1 := by rw [ha, hb, zero_smul, zero_smul, add_zero, add_zero]

variable [CharP K 2]

theorem exists_orth_split [Finite K] (Q : QuadraticForm K (ι → K))
    (hQ : Q.polarBilin.Nondegenerate) (N : Matrix ι ι K) (hN : N * N = 0) (hN0 : N ≠ 0)
    (hiso : ∀ v, Q (v + N *ᵥ v) = Q v) (hsing : ∀ v, Q (N *ᵥ v) = 0) :
    ∃ E₁ E₂ : Matrix ι ι K, N = E₁ + E₂ ∧ E₁ * E₁ = 0 ∧ E₁ * E₂ = 0 ∧ E₂ * E₁ = 0 ∧
      E₂ * E₂ = 0 ∧ (∀ v, Q (E₁ *ᵥ v) = 0) ∧ (∀ v, Q (E₂ *ᵥ v) = 0) ∧
      (∀ v, Q.polarBilin v (E₁ *ᵥ v) = 0) ∧ (∀ v, Q.polarBilin v (E₂ *ᵥ v) = 0) ∧
      E₁.rank = 2 ∧ E₂.rank = N.rank - 2 ∧ (∃ v, E₁ *ᵥ v ≠ 0 ∧ E₂ *ᵥ v = 0) ∧
      ∀ c : K, c ≠ 0 → ∃ D : GL ι K, (∀ v, Q ((D : Matrix ι ι K) *ᵥ v) = Q v) ∧
        Even (commRank D) ∧ ((D⁻¹ : GL ι K) : Matrix ι ι K) * E₁ * D = E₁ ∧
        ((D⁻¹ : GL ι K) : Matrix ι ι K) * E₂ * D = c • E₂ := by
  classical
  set B := Q.polarBilin with hBdef
  have hBs : ∀ x y, B x y = B y x := polarBilin_comm Q
  have hnd : ∀ w, (∀ z, B z w = 0) → w = 0 := hQ.2
  have hNN : ∀ v, N *ᵥ (N *ᵥ v) = 0 := fun v => by rw [mulVec_mulVec, hN, zero_mulVec]
  have hB0 : ∀ v, B v (N *ᵥ v) = 0 := fun v => by
    have h := hiso v
    rwa [quad_add, hsing, add_zero, add_eq_left] at h
  have hNadj : ∀ u v, B (N *ᵥ u) v = B u (N *ᵥ v) := fun u v => by
    have h := hB0 (u + v)
    simp only [mulVec_add, map_add, LinearMap.add_apply, hB0, zero_add, add_zero] at h
    rw [add_eq_zero_iff_eq_neg, CharTwo.neg_eq] at h
    rw [hBs, h]
  have hBNN : ∀ u v, B (N *ᵥ u) (N *ᵥ v) = 0 := fun u v => by
    rw [hNadj, hNN, map_zero]
  obtain ⟨y₀, hy₀⟩ : ∃ y, N *ᵥ y ≠ 0 := by
    by_contra! h
    exact hN0 (Matrix.ext_iff_mulVec.mpr fun v => by rw [h v, zero_mulVec])
  obtain ⟨x₀, hxy⟩ : ∃ x₀, B x₀ (N *ᵥ y₀) = 1 := by
    obtain ⟨x, hx⟩ : ∃ x, B x (N *ᵥ y₀) ≠ 0 := by
      by_contra! h
      exact hy₀ (hnd _ h)
    refine ⟨(B x (N *ᵥ y₀))⁻¹ • x, ?_⟩
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hx]
  have hyx : B y₀ (N *ᵥ x₀) = 1 := by rw [← hNadj, hBs, hxy]
  have hxx : B x₀ (N *ᵥ x₀) = 0 := hB0 x₀
  have hyy : B y₀ (N *ᵥ y₀) = 0 := hB0 y₀
  have hNx₀ : N *ᵥ x₀ ≠ 0 := fun h => by rw [h, map_zero] at hyx; exact zero_ne_one hyx
  set e₁ : (ι → K) →ₗ[K] (ι → K) :=
    (B.flip (N *ᵥ y₀)).smulRight (N *ᵥ x₀) + (B.flip (N *ᵥ x₀)).smulRight (N *ᵥ y₀) with he₁
  set E₁ := LinearMap.toMatrix' e₁ with hE₁
  have hE₁v : ∀ v, E₁ *ᵥ v = B v (N *ᵥ y₀) • (N *ᵥ x₀) + B v (N *ᵥ x₀) • (N *ᵥ y₀) := fun v => by
    rw [hE₁, LinearMap.toMatrix'_mulVec, he₁]
    rfl
  have hE₁N' : ∀ v, E₁ *ᵥ v = N *ᵥ (B v (N *ᵥ y₀) • x₀ + B v (N *ᵥ x₀) • y₀) := fun v => by
    rw [hE₁v, mulVec_add, mulVec_smul, mulVec_smul]
  set E₂ := N - E₁ with hE₂
  have hE₂v : ∀ v, E₂ *ᵥ v = N *ᵥ v - E₁ *ᵥ v := fun v => by rw [hE₂, sub_mulVec]
  have hE₂N' : ∀ v, E₂ *ᵥ v = N *ᵥ (v - (B v (N *ᵥ y₀) • x₀ + B v (N *ᵥ x₀) • y₀)) := fun v => by
    rw [hE₂v, hE₁N', mulVec_sub]
  have hE₁N : E₁ * N = 0 := Matrix.ext_iff_mulVec.mpr fun v => by
    rw [← mulVec_mulVec, hE₁v, hBNN, hBNN, zero_smul, zero_smul, add_zero, zero_mulVec]
  have hNE₁ : N * E₁ = 0 := Matrix.ext_iff_mulVec.mpr fun v => by
    rw [← mulVec_mulVec, hE₁N', hNN, zero_mulVec]
  have h11 : E₁ * E₁ = 0 := Matrix.ext_iff_mulVec.mpr fun v => by
    rw [← mulVec_mulVec, hE₁N' v, mulVec_mulVec, hE₁N, zero_mulVec, zero_mulVec]
  have h12 : E₁ * E₂ = 0 := by rw [hE₂, mul_sub, hE₁N, h11, sub_zero]
  have h21 : E₂ * E₁ = 0 := by rw [hE₂, sub_mul, hNE₁, h11, sub_zero]
  have hNE₂ : N * E₂ = 0 := by rw [hE₂, mul_sub, hN, hNE₁, sub_zero]
  have h22 : E₂ * E₂ = 0 := by rw [hE₂, sub_mul, hNE₂, h12, sub_zero]
  have hQE₁ : ∀ v, Q (E₁ *ᵥ v) = 0 := fun v => by rw [hE₁N']; exact hsing _
  have hQE₂ : ∀ v, Q (E₂ *ᵥ v) = 0 := fun v => by rw [hE₂N']; exact hsing _
  have hBE₁ : ∀ v, B v (E₁ *ᵥ v) = 0 := fun v => by
    rw [hE₁v, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, mul_comm (B v (N *ᵥ x₀)),
      CharTwo.add_self_eq_zero]
  have hBE₂ : ∀ v, B v (E₂ *ᵥ v) = 0 := fun v => by
    rw [hE₂v, map_sub, hB0, hBE₁, sub_zero]
  have hE₁x₀ : E₁ *ᵥ x₀ = N *ᵥ x₀ := by
    rw [hE₁v, hxy, hxx, one_smul, zero_smul, add_zero]
  have hE₁y₀ : E₁ *ᵥ y₀ = N *ᵥ y₀ := by
    rw [hE₁v, hyy, hyx, one_smul, zero_smul, zero_add]
  have hE₂x₀ : E₂ *ᵥ x₀ = 0 := by rw [hE₂v, hE₁x₀, sub_self]
  have hE₂y₀ : E₂ *ᵥ y₀ = 0 := by rw [hE₂v, hE₁y₀, sub_self]
  have hpair : ∀ a b : K, a • (N *ᵥ x₀) + b • (N *ᵥ y₀) = 0 → a = 0 ∧ b = 0 := by
    intro a b hab
    have h1 := congrArg (B x₀) hab
    have h2 := congrArg (B y₀) hab
    simp only [map_add, map_smul, smul_eq_mul, hxx, hxy, hyx, hyy, map_zero, mul_zero, mul_one,
      zero_add, add_zero] at h1 h2
    exact ⟨h2, h1⟩
  have hrank₁ : E₁.rank = 2 := by
    rw [rank_eq_finrank_range]
    have hR : LinearMap.range E₁.mulVecLin = Submodule.span K (Set.range ![N *ᵥ x₀, N *ᵥ y₀]) := by
      apply le_antisymm
      · rintro _ ⟨v, rfl⟩
        rw [Matrix.mulVecLin_apply, hE₁v]
        refine Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
          (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
      · rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        fin_cases i
        · exact ⟨x₀, hE₁x₀⟩
        · exact ⟨y₀, hE₁y₀⟩
    rw [hR, finrank_span_eq_card (LinearIndependent.pair_iff.mpr hpair), Fintype.card_fin]
  have hker : ∀ v, N *ᵥ v = 0 → E₂ *ᵥ v = 0 := fun v hv => by
    have h1 : B v (N *ᵥ y₀) = 0 := by rw [← hNadj, hv, map_zero, LinearMap.zero_apply]
    have h2 : B v (N *ᵥ x₀) = 0 := by rw [← hNadj, hv, map_zero, LinearMap.zero_apply]
    rw [hE₂v, hv, hE₁v, h1, h2, zero_smul, zero_smul, add_zero, sub_zero]
  have hrank₂ : E₂.rank = N.rank - 2 :=
    rank_eq_sub_two_of_split (by rw [hE₂, add_sub_cancel]) hrank₁ hker hE₂x₀ hE₂y₀ hpair
  refine ⟨E₁, E₂, by rw [hE₂, add_sub_cancel], h11, h12, h21, h22, hQE₁, hQE₂, hBE₁, hBE₂,
    hrank₁, hrank₂, ⟨x₀, by rw [hE₁x₀]; exact hNx₀, hE₂x₀⟩, fun c hc => ?_⟩
  set U := LinearMap.range E₂.mulVecLin with hU
  set k := finrank K U with hk
  let bU := Module.finBasis K U
  set u : Fin k → ι → K := fun i => (bU i : ι → K) with hu
  have huU : ∀ i, u i ∈ U := fun i => (bU i).2
  have hUN : ∀ w ∈ U, ∃ z, w = N *ᵥ z := by
    rintro _ ⟨z, rfl⟩
    exact ⟨_, hE₂N' z⟩
  have hQU : ∀ w ∈ U, Q w = 0 := fun w hw => by
    obtain ⟨z, rfl⟩ := hUN w hw
    exact hsing z
  have hBUU : ∀ w ∈ U, ∀ w' ∈ U, B w w' = 0 := fun w hw w' hw' => by
    obtain ⟨z, rfl⟩ := hUN w hw
    obtain ⟨z', rfl⟩ := hUN w' hw'
    exact hBNN z z'
  have hBNU : ∀ w ∈ U, B (N *ᵥ x₀) w = 0 ∧ B (N *ᵥ y₀) w = 0 := fun w hw => by
    obtain ⟨z, rfl⟩ := hUN w hw
    exact ⟨hBNN _ _, hBNN _ _⟩
  have hBxU : ∀ w ∈ U, B x₀ w = 0 ∧ B y₀ w = 0 := by
    rintro _ ⟨z, rfl⟩
    change B x₀ (E₂ *ᵥ z) = 0 ∧ B y₀ (E₂ *ᵥ z) = 0
    rw [hE₂v, hE₁v]
    simp only [map_sub, map_add, map_smul, smul_eq_mul, hxx, hxy, hyx, hyy, mul_zero, mul_one,
      add_zero, zero_add]
    constructor
    · rw [← hNadj, hBs, sub_self]
    · rw [← hNadj, hBs, sub_self]
  have hu_li : LinearIndependent K u := bU.linearIndependent.map' U.subtype U.ker_subtype
  have hspanU : Submodule.span K (Set.range u) ≤ U :=
    Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact huU i)
  let g : Fin k ⊕ Fin 2 → ι → K := Sum.elim u ![N *ᵥ x₀, N *ᵥ y₀]
  have hg : LinearIndependent K g := by
    refine hu_li.sum_type (LinearIndependent.pair_iff.mpr hpair) ?_
    rw [Submodule.disjoint_def]
    intro w hw hw'
    obtain ⟨h1, h2⟩ := hBxU _ (hspanU hw)
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hw'
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, map_add, map_smul,
      smul_eq_mul, hxx, hxy, hyx, hyy, mul_zero, mul_one, zero_add, add_zero] at h1 h2
    simp [Fin.sum_univ_two, h1, h2]
  obtain ⟨w, hw⟩ := exists_polar_dual Q hQ g hg
  rw [← hBdef] at hw
  set u' : Fin k → ι → K := fun j => w (.inl j) with hu'
  have hdual : ∀ i j, B (u i) (u' j) = if i = j then 1 else 0 := fun i j => by
    have := hw (.inl i) (.inl j)
    simp only [g, Sum.elim_inl, Sum.inl.injEq] at this
    exact this
  have hNxu' : ∀ j, B (N *ᵥ x₀) (u' j) = 0 := fun j => by
    have := hw (.inr 0) (.inl j)
    simp only [g, Sum.elim_inr, Matrix.cons_val_zero, reduceCtorEq, ↓reduceIte] at this
    exact this
  have hNyu' : ∀ j, B (N *ᵥ y₀) (u' j) = 0 := fun j => by
    have := hw (.inr 1) (.inl j)
    simp only [g, Sum.elim_inr, Matrix.cons_val_one, Matrix.cons_val_zero, reduceCtorEq,
      ↓reduceIte] at this
    exact this
  have huu : ∀ i j, B (u i) (u j) = 0 := fun i j => hBUU _ (huU i) _ (huU j)
  obtain ⟨u'', hdual'', hiso'', hsing'', hcomb⟩ :=
    exists_singular_dual Q u u' (fun i => hQU _ (huU i)) huu hdual
  rw [← hBdef] at hdual'' hiso''
  have hNxu'' : ∀ j, B (N *ᵥ x₀) (u'' j) = 0 := fun j => by
    obtain ⟨cj, hcj⟩ := hcomb j
    rw [hcj, map_add, map_sum, hNxu', zero_add]
    exact Finset.sum_eq_zero fun m _ => by rw [map_smul, (hBNU _ (huU m)).1, smul_zero]
  have hNyu'' : ∀ j, B (N *ᵥ y₀) (u'' j) = 0 := fun j => by
    obtain ⟨cj, hcj⟩ := hcomb j
    rw [hcj, map_add, map_sum, hNyu', zero_add]
    exact Finset.sum_eq_zero fun m _ => by rw [map_smul, (hBNU _ (huU m)).2, smul_zero]
  have hu''u : ∀ i j, B (u'' i) (u j) = if i = j then 1 else 0 := fun i j => by
    rw [hBs, hdual'']
    by_cases h : i = j
    · subst h
      simp
    · simp [h, Ne.symm h]
  set P := LinearMap.toMatrix' (∑ i, (B (u'' i)).smulRight (u i)) with hP
  set P' := LinearMap.toMatrix' (∑ i, (B (u i)).smulRight (u'' i)) with hP'
  have hPv : ∀ v, P *ᵥ v = ∑ i, B (u'' i) v • u i := fun v => by
    rw [hP, LinearMap.toMatrix'_mulVec]
    simp only [LinearMap.sum_apply, LinearMap.smulRight_apply]
  have hP'v : ∀ v, P' *ᵥ v = ∑ i, B (u i) v • u'' i := fun v => by
    rw [hP', LinearMap.toMatrix'_mulVec]
    simp only [LinearMap.sum_apply, LinearMap.smulRight_apply]
  have hPu : ∀ j, P *ᵥ u j = u j := fun j => by
    rw [hPv]
    simp [hu''u]
  have hPu'' : ∀ j, P *ᵥ u'' j = 0 := fun j => by
    rw [hPv]
    simp [hiso'']
  have hP'u : ∀ j, P' *ᵥ u j = 0 := fun j => by
    rw [hP'v]
    simp [huu]
  have hP'u'' : ∀ j, P' *ᵥ u'' j = u'' j := fun j => by
    rw [hP'v]
    simp [hdual'']
  have hPP : P * P = P := ext_iff_mulVec.mpr fun v => by
    rw [← mulVec_mulVec, hPv v, mulVec_sum]
    simp only [mulVec_smul, hPu]
  have hP'P' : P' * P' = P' := ext_iff_mulVec.mpr fun v => by
    rw [← mulVec_mulVec, hP'v v, mulVec_sum]
    simp only [mulVec_smul, hP'u'']
  have hPP' : P * P' = 0 := ext_iff_mulVec.mpr fun v => by
    rw [← mulVec_mulVec, hP'v v, mulVec_sum]
    simp [mulVec_smul, hPu'']
  have hP'P : P' * P = 0 := ext_iff_mulVec.mpr fun v => by
    rw [← mulVec_mulVec, hPv v, mulVec_sum]
    simp [mulVec_smul, hP'u]
  have hrepr : ∀ v, E₂ *ᵥ v = ∑ j, bU.repr ⟨E₂ *ᵥ v, ⟨v, rfl⟩⟩ j • u j := fun v => by
    have h1 := congrArg Subtype.val (bU.sum_repr ⟨E₂ *ᵥ v, ⟨v, rfl⟩⟩)
    rw [Submodule.coe_sum] at h1
    simp only [Submodule.coe_smul] at h1
    exact h1.symm
  have hE₂u : ∀ i, E₂ *ᵥ u i = 0 := fun i => by
    obtain ⟨z, hz⟩ := hUN _ (huU i)
    rw [hz, mulVec_mulVec, hE₂, sub_mul, hN, hE₁N, sub_zero, zero_mulVec]
  have hE₂P : E₂ * P = 0 := ext_iff_mulVec.mpr fun v => by
    rw [← mulVec_mulVec, hPv v, mulVec_sum]
    simp [mulVec_smul, hE₂u]
  have hPE₂ : P * E₂ = E₂ := ext_iff_mulVec.mpr fun v => by
    rw [← mulVec_mulVec, hrepr v, mulVec_sum]
    simp only [mulVec_smul, hPu]
  have hP'E₂ : P' * E₂ = 0 := ext_iff_mulVec.mpr fun v => by
    have h1 : ∀ i, B (u i) (E₂ *ᵥ v) = 0 := fun i => hBUU _ (huU i) _ ⟨v, rfl⟩
    rw [← mulVec_mulVec, hP'v]
    simp [h1]
  have hE₂adj : ∀ a b, B (E₂ *ᵥ a) b = B a (E₂ *ᵥ b) := fun a b => by
    rw [hE₂v, hE₂v, hE₁v, hE₁v]
    simp only [map_sub, LinearMap.sub_apply, map_add, LinearMap.add_apply, map_smul,
      LinearMap.smul_apply, smul_eq_mul]
    rw [hNadj, hBs (N *ᵥ x₀) b, hBs (N *ᵥ y₀) b]
    ring
  have hE₂P' : E₂ * P' = E₂ := ext_iff_mulVec.mpr fun v => by
    rw [← mulVec_mulVec, ← sub_eq_zero, ← mulVec_sub]
    refine hnd _ fun z => ?_
    rw [← hE₂adj, hrepr z, map_sum, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [map_smul, LinearMap.smul_apply, map_sub, hP'v, map_sum]
    simp [hdual'', Finset.sum_ite_eq]
  obtain ⟨α, hα⟩ := isSquare_of_charTwo' c⁻¹
  have hα0 : α ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hα
    exact inv_ne_zero hc hα
  have hab : (α - 1) + (α⁻¹ - 1) + (α - 1) * (α⁻¹ - 1) = 0 := by
    field_simp
    ring
  have hab' : (α⁻¹ - 1) + (α - 1) + (α⁻¹ - 1) * (α - 1) = 0 := by
    rw [show (α⁻¹ - 1) + (α - 1) + (α⁻¹ - 1) * (α - 1) =
      (α - 1) + (α⁻¹ - 1) + (α - 1) * (α⁻¹ - 1) by ring]
    exact hab
  set X := 1 + (α - 1) • P + (α⁻¹ - 1) • P' with hX
  set X' := 1 + (α⁻¹ - 1) • P + (α - 1) • P' with hX'
  have hXX' : X * X' = 1 := one_add_two_smul_mul hPP hP'P' hPP' hP'P hab hab'
  have hX'X : X' * X = 1 := one_add_two_smul_mul hPP hP'P' hPP' hP'P hab' hab
  let D : GL ι K := ⟨X, X', hXX', hX'X⟩
  have hDinv : ((D⁻¹ : GL ι K) : Matrix ι ι K) = X' := rfl
  have hXv : ∀ v, X *ᵥ v = v + (α - 1) • (P *ᵥ v) + (α⁻¹ - 1) • (P' *ᵥ v) := fun v => by
    rw [hX, add_mulVec, add_mulVec, one_mulVec, smul_mulVec, smul_mulVec]
  have hX'v : ∀ v, X' *ᵥ v = v + (α⁻¹ - 1) • (P *ᵥ v) + (α - 1) • (P' *ᵥ v) := fun v => by
    rw [hX', add_mulVec, add_mulVec, one_mulVec, smul_mulVec, smul_mulVec]
  have hQP : ∀ v, Q (P *ᵥ v) = 0 := fun v => by
    rw [hPv]
    exact hQU _ (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (huU i))
  have hQP' : ∀ v, Q (P' *ᵥ v) = 0 := fun v => by
    rw [hP'v]
    exact apply_sum_smul_eq_zero Q u'' hsing'' hiso'' _
  have hBPv : ∀ v, B v (P *ᵥ v) = ∑ i, B (u'' i) v * B (u i) v := fun v => by
    rw [hPv, map_sum]
    simp only [map_smul, smul_eq_mul, hBs v (u _)]
  have hBP'v : ∀ v, B v (P' *ᵥ v) = ∑ i, B (u'' i) v * B (u i) v := fun v => by
    rw [hP'v, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, smul_eq_mul, hBs v (u'' i), mul_comm]
  have hBPP' : ∀ v, B (P *ᵥ v) (P' *ᵥ v) = ∑ i, B (u'' i) v * B (u i) v := fun v => by
    rw [hPv, hP'v]
    simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
      hdual'', mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hDQ : ∀ v, Q (X *ᵥ v) = Q v := fun v => by
    set S := ∑ i, B (u'' i) v * B (u i) v with hS
    calc Q (X *ᵥ v) = Q v + ((α - 1) + (α⁻¹ - 1) + (α - 1) * (α⁻¹ - 1)) * S := by
          rw [hXv, quad_add, quad_add, QuadraticMap.map_smul, QuadraticMap.map_smul, hQP, hQP',
            smul_zero, smul_zero, add_zero, add_zero, ← hBdef]
          simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
            hBPv, hBP'v, hBPP']
          ring
      _ = Q v := by rw [hab, zero_mul, add_zero]
  have hPNx : P *ᵥ (N *ᵥ x₀) = 0 := by
    rw [hPv]
    exact Finset.sum_eq_zero fun i _ => by rw [hBs, hNxu'', zero_smul]
  have hPNy : P *ᵥ (N *ᵥ y₀) = 0 := by
    rw [hPv]
    exact Finset.sum_eq_zero fun i _ => by rw [hBs, hNyu'', zero_smul]
  have hP'Nx : P' *ᵥ (N *ᵥ x₀) = 0 := by
    rw [hP'v]
    exact Finset.sum_eq_zero fun i _ => by rw [hBs, (hBNU _ (huU i)).1, zero_smul]
  have hP'Ny : P' *ᵥ (N *ᵥ y₀) = 0 := by
    rw [hP'v]
    exact Finset.sum_eq_zero fun i _ => by rw [hBs, (hBNU _ (huU i)).2, zero_smul]
  have hXNx : X *ᵥ (N *ᵥ x₀) = N *ᵥ x₀ := by
    rw [hXv, hPNx, hP'Nx, smul_zero, smul_zero, add_zero, add_zero]
  have hXNy : X *ᵥ (N *ᵥ y₀) = N *ᵥ y₀ := by
    rw [hXv, hPNy, hP'Ny, smul_zero, smul_zero, add_zero, add_zero]
  have hX'Nx : X' *ᵥ (N *ᵥ x₀) = N *ᵥ x₀ := by
    rw [hX'v, hPNx, hP'Nx, smul_zero, smul_zero, add_zero, add_zero]
  have hX'Ny : X' *ᵥ (N *ᵥ y₀) = N *ᵥ y₀ := by
    rw [hX'v, hPNy, hP'Ny, smul_zero, smul_zero, add_zero, add_zero]
  have hBX : ∀ v w, X *ᵥ w = w → B (X *ᵥ v) w = B v w := fun v w hw => by
    rw [← polarBilin_mulVec_of_isometry Q hDQ v w, hw]
  have hev : Even (commRank D) := by
    change Even ((X - 1).rank)
    by_cases hα1 : α = 1
    · have hX1 : X = 1 := by
        rw [hX, hα1, inv_one, sub_self, zero_smul, zero_smul, add_zero, add_zero]
      rw [hX1, sub_self, Matrix.rank_zero]
      exact ⟨0, rfl⟩
    · have hα1' : α⁻¹ - 1 ≠ 0 := fun h => hα1 (by rwa [sub_eq_zero, inv_eq_one] at h)
      have hα1'' : α - 1 ≠ 0 := sub_ne_zero.mpr hα1
      have hX1v : ∀ v, (X - 1) *ᵥ v = (α - 1) • (P *ᵥ v) + (α⁻¹ - 1) • (P' *ᵥ v) := fun v => by
        rw [sub_mulVec, hXv, one_mulVec, add_assoc, add_sub_cancel_left]
      have hu''_li : LinearIndependent K u'' := by
        rw [linearIndependent_iff']
        intro s c hc i hi
        have h := congrArg (B (u i)) hc
        rw [map_sum, map_zero] at h
        simpa [hdual'', Finset.sum_ite_eq, hi] using h
      have hdisj :
          Disjoint (Submodule.span K (Set.range u)) (Submodule.span K (Set.range u'')) := by
        rw [Submodule.disjoint_def]
        intro w hw hw'
        have hwU := hspanU hw
        obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hw'
        have hc : ∀ m, c m = 0 := fun m => by
          have h := hBUU _ (huU m) _ hwU
          rw [map_sum] at h
          simpa [hdual''] using h
        simp [hc]
      have hli : LinearIndependent K (Sum.elim u u'') := hu_li.sum_type hu''_li hdisj
      have hR : LinearMap.range (X - 1).mulVecLin =
          Submodule.span K (Set.range (Sum.elim u u'')) := by
        apply le_antisymm
        · rintro _ ⟨v, rfl⟩
          rw [Matrix.mulVecLin_apply, hX1v, hPv, hP'v]
          exact Submodule.add_mem _
            (Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ =>
              Submodule.smul_mem _ _ (Submodule.subset_span ⟨.inl i, rfl⟩)))
            (Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ =>
              Submodule.smul_mem _ _ (Submodule.subset_span ⟨.inr i, rfl⟩)))
        · rw [Submodule.span_le]
          rintro _ ⟨i | i, rfl⟩
          · refine ⟨(α - 1)⁻¹ • u i, ?_⟩
            rw [Matrix.mulVecLin_apply, mulVec_smul, hX1v, hPu, hP'u, smul_zero, add_zero,
              smul_smul, inv_mul_cancel₀ hα1'', one_smul]
            rfl
          · refine ⟨(α⁻¹ - 1)⁻¹ • u'' i, ?_⟩
            rw [Matrix.mulVecLin_apply, mulVec_smul, hX1v, hPu'', hP'u'', smul_zero, zero_add,
              smul_smul, inv_mul_cancel₀ hα1', one_smul]
            rfl
      rw [rank_eq_finrank_range, hR, finrank_span_eq_card hli, Fintype.card_sum,
        Fintype.card_fin]
      exact ⟨k, rfl⟩
  refine ⟨D, hDQ, hev, ?_, ?_⟩
  ·
    have hE₁X : E₁ * X = E₁ := ext_iff_mulVec.mpr fun v => by
      rw [← mulVec_mulVec, hE₁v, hE₁v, hBX v _ hXNy, hBX v _ hXNx]
    have hX'E₁ : X' * E₁ = E₁ := ext_iff_mulVec.mpr fun v => by
      rw [← mulVec_mulVec, hE₁v, mulVec_add, mulVec_smul, mulVec_smul, hX'Nx, hX'Ny]
    rw [hDinv]
    change X' * E₁ * X = E₁
    rw [mul_assoc, hE₁X, hX'E₁]
  ·
    have hmod : E₂ + (α⁻¹ - 1) • E₂ = α⁻¹ • E₂ := by
      nth_rewrite 1 [← one_smul K E₂]
      rw [← add_smul, add_sub_cancel]
    have h1 : E₂ * X = α⁻¹ • E₂ := by
      rw [hX, mul_add, mul_add, mul_one, Matrix.mul_smul, Matrix.mul_smul, hE₂P, hE₂P', smul_zero,
        add_zero, hmod]
    have h2 : X' * E₂ = α⁻¹ • E₂ := by
      rw [hX', add_mul, add_mul, one_mul, Matrix.smul_mul, Matrix.smul_mul, hPE₂, hP'E₂,
        smul_zero, add_zero, hmod]
    rw [hDinv]
    change X' * E₂ * X = c • E₂
    rw [mul_assoc, h1, Matrix.mul_smul, h2, smul_smul, ← mul_inv, ← hα, inv_inv]

end CFSG.ComponentClassification.RankTwoClassical
