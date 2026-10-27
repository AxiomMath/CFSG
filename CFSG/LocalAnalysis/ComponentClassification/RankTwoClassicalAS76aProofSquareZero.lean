module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Determinant

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Module

section Basis

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem exists_basis_sq_eq_zero (N : V →ₗ[K] V) (hN : N ∘ₗ N = 0) :
    ∃ (r : ℕ) (b : Basis (Fin (finrank K (LinearMap.range N)) ⊕
      (Fin (finrank K (LinearMap.range N)) ⊕ Fin r)) K V),
      (∀ i, N (b (.inl i)) = b (.inr (.inl i))) ∧ ∀ k, N (b (.inr k)) = 0 := by
  classical
  set ℓ := finrank K (LinearMap.range N) with hℓ
  have hNN : ∀ v, N (N v) = 0 := fun v => by
    rw [← LinearMap.comp_apply, hN, LinearMap.zero_apply]
  have hRK : LinearMap.range N ≤ LinearMap.ker N := by
    rintro _ ⟨v, rfl⟩
    exact hNN v
  obtain ⟨X, hX⟩ := (LinearMap.ker N).exists_isCompl
  have hXdim : finrank K X = ℓ := by
    have h1 := Submodule.finrank_add_eq_of_isCompl hX
    have h2 := LinearMap.finrank_range_add_finrank_ker N
    omega
  let bX : Basis (Fin ℓ) K X := Module.finBasisOfFinrankEq K X hXdim
  set R' := (LinearMap.range N).comap (LinearMap.ker N).subtype with hR'
  obtain ⟨Y₀, hY₀⟩ := R'.exists_isCompl
  have hR'dim : finrank K R' = ℓ :=
    (Submodule.comapSubtypeEquivOfLe hRK).finrank_eq
  let bY := Module.finBasis K Y₀
  set r := finrank K Y₀ with hr
  let f₁ : Fin ℓ → V := fun i => (bX i : V)
  let f₂ : Fin ℓ → V := fun i => N (bX i)
  let f₃ : Fin r → V := fun j => ((bY j : LinearMap.ker N) : V)
  have hf₁ : LinearIndependent K f₁ := bX.linearIndependent.map' X.subtype X.ker_subtype
  have hspan₁ : Submodule.span K (Set.range f₁) = X := by
    have : f₁ = X.subtype ∘ bX := rfl
    rw [this, Set.range_comp, ← Submodule.map_span, bX.span_eq, Submodule.map_top,
      Submodule.range_subtype]
  have hf₂ : LinearIndependent K f₂ := hf₁.map (f := N) (by rw [hspan₁]; exact hX.disjoint.symm)
  have hf₃ : LinearIndependent K f₃ :=
    (bY.linearIndependent.map' Y₀.subtype Y₀.ker_subtype).map' (LinearMap.ker N).subtype
      (LinearMap.ker N).ker_subtype
  have hf₂R : Submodule.span K (Set.range f₂) ≤ LinearMap.range N :=
    Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact ⟨_, rfl⟩)
  have hf₃Y : Submodule.span K (Set.range f₃) ≤ Y₀.map (LinearMap.ker N).subtype := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨j, rfl⟩
    exact ⟨(bY j : LinearMap.ker N), (bY j).2, rfl⟩
  have hdis₂₃ : Disjoint (Submodule.span K (Set.range f₂)) (Submodule.span K (Set.range f₃)) := by
    refine Disjoint.mono hf₂R hf₃Y ?_
    rw [Submodule.disjoint_def]
    intro z hzR hzY
    obtain ⟨y, hy, rfl⟩ := hzY
    have hyR : y ∈ R' := hzR
    have hy0 : y = 0 := Submodule.disjoint_def.mp hY₀.disjoint _ hyR hy
    rw [hy0, map_zero]
  have hf₂₃ : LinearIndependent K (Sum.elim f₂ f₃) := hf₂.sum_type hf₃ hdis₂₃
  have hf₂₃K : Submodule.span K (Set.range (Sum.elim f₂ f₃)) ≤ LinearMap.ker N := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨k, rfl⟩
    rcases k with i | j
    · exact hNN _
    · exact (bY j : LinearMap.ker N).2
  have hdis : Disjoint (Submodule.span K (Set.range f₁))
      (Submodule.span K (Set.range (Sum.elim f₂ f₃))) := by
    rw [hspan₁]
    exact Disjoint.mono_right hf₂₃K hX.disjoint.symm
  have hli : LinearIndependent K (Sum.elim f₁ (Sum.elim f₂ f₃)) := hf₁.sum_type hf₂₃ hdis
  have hcard : Fintype.card (Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) = finrank K V := by
    have h1 := Submodule.finrank_add_eq_of_isCompl hX
    have h2 := Submodule.finrank_add_eq_of_isCompl hY₀
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  by_cases hne : Nonempty (Fin ℓ ⊕ (Fin ℓ ⊕ Fin r))
  · refine ⟨r, basisOfLinearIndependentOfCardEqFinrank hli hcard, fun i => ?_, fun k => ?_⟩
    · simp [coe_basisOfLinearIndependentOfCardEqFinrank, f₁, f₂]
    · rw [coe_basisOfLinearIndependentOfCardEqFinrank]
      rcases k with i | j
      · exact hNN _
      · exact (bY j : LinearMap.ker N).2
  ·
    have hV : finrank K V = 0 := by
      rw [← hcard]
      exact Fintype.card_eq_zero_iff.mpr (not_nonempty_iff.mp hne)
    have : Subsingleton V := Module.finrank_zero_iff.mp hV
    have hemp : IsEmpty (Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) := not_nonempty_iff.mp hne
    refine ⟨r, Basis.empty V, fun i => Subsingleton.elim _ _, fun k => Subsingleton.elim _ _⟩

end Basis

section Split

variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]

open scoped Matrix

theorem rank_toMatrix' (f : (ι → K) →ₗ[K] (ι → K)) :
    (LinearMap.toMatrix' f).rank = finrank K (LinearMap.range f) := by
  rw [Matrix.rank, ← Matrix.toLin'_apply', Matrix.toLin'_toMatrix']

theorem exists_split_sq_eq_zero [Finite K] [CharP K 2] (N : Matrix ι ι K) (hN : N * N = 0)
    (hℓ : 2 ≤ N.rank) :
    ∃ E₁ E₂ : Matrix ι ι K, N = E₁ + E₂ ∧ E₁ * E₁ = 0 ∧ E₁ * E₂ = 0 ∧ E₂ * E₁ = 0 ∧
      E₂ * E₂ = 0 ∧ E₁.rank = 1 ∧ E₂.rank = N.rank - 1 ∧ (∃ v, E₁ *ᵥ v ≠ 0 ∧ E₂ *ᵥ v = 0) ∧
      ∀ c : K, c ≠ 0 → ∃ D : GL ι K, (D : Matrix ι ι K).det = 1 ∧
        ((D⁻¹ : GL ι K) : Matrix ι ι K) * E₁ * D = E₁ ∧
        ((D⁻¹ : GL ι K) : Matrix ι ι K) * E₂ * D = c • E₂ := by
  classical
  set Nl := Matrix.toLin' N with hNl
  have hNl2 : Nl ∘ₗ Nl = 0 := by rw [hNl, ← Matrix.toLin'_mul, hN, map_zero]
  have hrank : N.rank = finrank K (LinearMap.range Nl) := by
    rw [Matrix.rank, hNl, Matrix.toLin'_apply']
  obtain ⟨r, b, hb1, hb2⟩ := exists_basis_sq_eq_zero Nl hNl2
  rw [hrank] at hℓ ⊢
  generalize hℓdef : finrank K (LinearMap.range Nl) = ℓ at b hb1 hb2 hℓ ⊢
  set i₀ : Fin ℓ := ⟨0, by omega⟩ with hi₀
  set w := b (.inr (.inl i₀)) with hw
  have hw0 : w ≠ 0 := b.ne_zero _
  have hcoord : ∀ k k', b.coord k' (b k) = if k = k' then 1 else 0 := by
    intro k k'
    rw [Basis.coord_apply, Basis.repr_self, Finsupp.single_apply]
  set E₁l : (ι → K) →ₗ[K] (ι → K) := (b.coord (.inl i₀)).smulRight w with hE₁l
  set E₂l := Nl - E₁l with hE₂l
  have hE₁b : ∀ k, E₁l (b k) = if k = .inl i₀ then w else 0 := by
    intro k
    rw [hE₁l, LinearMap.smulRight_apply, hcoord]
    split_ifs <;> simp
  have hE₂inl : ∀ i, E₂l (b (.inl i)) = if i = i₀ then 0 else b (.inr (.inl i)) := by
    intro i
    rw [hE₂l, LinearMap.sub_apply, hb1, hE₁b]
    by_cases h : i = i₀
    · subst h
      simp [hw]
    · simp [h]
  have hE₂inr : ∀ k, E₂l (b (.inr k)) = 0 := by
    intro k
    rw [hE₂l, LinearMap.sub_apply, hb2, hE₁b, ite_eq_right Sum.inr_ne_inl, sub_zero]
  have hE₁w : E₁l w = 0 := by rw [hw, hE₁b, ite_eq_right Sum.inr_ne_inl]
  have hE₂w : E₂l w = 0 := by rw [hw, hE₂inr]
  have h11 : E₁l ∘ₗ E₁l = 0 := b.ext fun k => by
    rw [LinearMap.comp_apply, hE₁b, LinearMap.zero_apply]
    split_ifs
    · exact hE₁w
    · exact map_zero _
  have h21 : E₂l ∘ₗ E₁l = 0 := b.ext fun k => by
    rw [LinearMap.comp_apply, hE₁b, LinearMap.zero_apply]
    split_ifs
    · exact hE₂w
    · exact map_zero _
  have h12 : E₁l ∘ₗ E₂l = 0 := b.ext fun k => by
    rw [LinearMap.comp_apply, LinearMap.zero_apply]
    rcases k with i | k
    · rw [hE₂inl]
      split_ifs
      · exact map_zero _
      · rw [hE₁b, ite_eq_right Sum.inr_ne_inl]
    · rw [hE₂inr, map_zero]
  have h22 : E₂l ∘ₗ E₂l = 0 := b.ext fun k => by
    rw [LinearMap.comp_apply, LinearMap.zero_apply]
    rcases k with i | k
    · rw [hE₂inl]
      split_ifs
      · exact map_zero _
      · rw [hE₂inr]
    · rw [hE₂inr, map_zero]
  have hrank₁ : finrank K (LinearMap.range E₁l) = 1 := by
    have hR : LinearMap.range E₁l = K ∙ w := by
      apply le_antisymm
      · rintro _ ⟨v, rfl⟩
        rw [hE₁l, LinearMap.smulRight_apply]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self w)
      · rw [Submodule.span_singleton_le_iff_mem]
        exact ⟨b (.inl i₀), by rw [hE₁b, ite_eq_left rfl]⟩
    rw [hR, finrank_span_singleton hw0]
  have hrank₂ : finrank K (LinearMap.range E₂l) = ℓ - 1 := by
    let g : {i : Fin ℓ // i ≠ i₀} → (ι → K) := fun i => b (.inr (.inl i.1))
    have hg : LinearIndependent K g :=
      b.linearIndependent.comp _ fun i j h => Subtype.ext (by simpa using h)
    have hR : LinearMap.range E₂l = Submodule.span K (Set.range g) := by
      apply le_antisymm
      · rintro _ ⟨v, rfl⟩
        rw [← b.sum_repr v, map_sum]
        refine Submodule.sum_mem _ fun k _ => ?_
        rw [map_smul]
        refine Submodule.smul_mem _ _ ?_
        rcases k with i | k
        · rw [hE₂inl]
          split_ifs with h
          · exact Submodule.zero_mem _
          · exact Submodule.subset_span ⟨⟨i, h⟩, rfl⟩
        · rw [hE₂inr]
          exact Submodule.zero_mem _
      · rw [Submodule.span_le]
        rintro _ ⟨⟨i, hi⟩, rfl⟩
        exact ⟨b (.inl i), by rw [hE₂inl, ite_eq_right hi]⟩
    rw [hR, finrank_span_eq_card hg, Fintype.card_subtype_compl, Fintype.card_subtype_eq,
      Fintype.card_fin]
  refine ⟨LinearMap.toMatrix' E₁l, LinearMap.toMatrix' E₂l, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_add, hE₂l, add_sub_cancel, hNl, LinearMap.toMatrix'_toLin']
  · rw [← LinearMap.toMatrix'_comp, h11, map_zero]
  · rw [← LinearMap.toMatrix'_comp, h12, map_zero]
  · rw [← LinearMap.toMatrix'_comp, h21, map_zero]
  · rw [← LinearMap.toMatrix'_comp, h22, map_zero]
  · rw [rank_toMatrix', hrank₁]
  · rw [rank_toMatrix', hrank₂]
  · refine ⟨b (.inl i₀), ?_, ?_⟩
    · rw [LinearMap.toMatrix'_mulVec, hE₁b, ite_eq_left rfl]
      exact hw0
    · rw [LinearMap.toMatrix'_mulVec, hE₂inl, ite_eq_left rfl]
  · intro c hc
    obtain ⟨μ, hμ⟩ := isSquare_of_charTwo' c
    have hμ0 : μ ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hμ
      exact hc hμ
    let d : Fin ℓ ⊕ (Fin ℓ ⊕ Fin r) → K := fun k => match k with
      | .inl i => if i = i₀ then 1 else μ
      | .inr (.inl i) => if i = i₀ then 1 else μ⁻¹
      | .inr (.inr _) => 1
    have hd0 : ∀ k, d k ≠ 0 := by
      intro k
      rcases k with i | i | j
      · simp only [d]; split_ifs <;> simp [hμ0]
      · simp only [d]; split_ifs <;> simp [hμ0]
      · simp [d]
    set Dl : (ι → K) →ₗ[K] (ι → K) := b.constr K fun k => d k • b k with hDl
    set Dl' : (ι → K) →ₗ[K] (ι → K) := b.constr K fun k => (d k)⁻¹ • b k with hDl'
    have hDb : ∀ k, Dl (b k) = d k • b k := fun k => by rw [hDl, Basis.constr_basis]
    have hDb' : ∀ k, Dl' (b k) = (d k)⁻¹ • b k := fun k => by rw [hDl', Basis.constr_basis]
    have hDD' : Dl ∘ₗ Dl' = LinearMap.id := b.ext fun k => by
      rw [LinearMap.comp_apply, hDb', map_smul, hDb, smul_smul, inv_mul_cancel₀ (hd0 k),
        one_smul, LinearMap.id_apply]
    have hD'D : Dl' ∘ₗ Dl = LinearMap.id := b.ext fun k => by
      rw [LinearMap.comp_apply, hDb, map_smul, hDb', smul_smul, mul_inv_cancel₀ (hd0 k),
        one_smul, LinearMap.id_apply]
    let D : GL ι K :=
      ⟨LinearMap.toMatrix' Dl, LinearMap.toMatrix' Dl',
        by rw [← LinearMap.toMatrix'_comp, hDD', LinearMap.toMatrix'_id],
        by rw [← LinearMap.toMatrix'_comp, hD'D, LinearMap.toMatrix'_id]⟩
    have hDinv : ((D⁻¹ : GL ι K) : Matrix ι ι K) = LinearMap.toMatrix' Dl' := rfl
    refine ⟨D, ?_, ?_, ?_⟩
    ·
      change (LinearMap.toMatrix' Dl).det = 1
      rw [LinearMap.det_toMatrix', ← LinearMap.det_toMatrix b Dl]
      have hdiag : LinearMap.toMatrix b b Dl = Matrix.diagonal d := by
        ext i j
        rw [LinearMap.toMatrix_apply, hDb, map_smul, b.repr_self, Finsupp.smul_single,
          smul_eq_mul, mul_one, Finsupp.single_apply, Matrix.diagonal_apply]
        by_cases h : i = j
        · subst h
          simp
        · simp [h, Ne.symm h]
      rw [hdiag, Matrix.det_diagonal, Fintype.prod_sum_type, Fintype.prod_sum_type,
        ← mul_assoc, ← Finset.prod_mul_distrib]
      have h1 : ∀ i : Fin ℓ, d (.inl i) * d (.inr (.inl i)) = 1 := by
        intro i
        simp only [d]
        split_ifs
        · rw [one_mul]
        · exact mul_inv_cancel₀ hμ0
      simp [h1, d]
    · rw [hDinv, ← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_comp]
      congr 1
      refine b.ext fun k => ?_
      rw [LinearMap.comp_apply, LinearMap.comp_apply, hDb, map_smul, map_smul, hE₁b]
      split_ifs with h
      · subst h
        rw [hw, hDb']
        simp [d]
      · simp
    · rw [hDinv, ← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_comp, ← map_smul]
      congr 1
      refine b.ext fun k => ?_
      rw [LinearMap.comp_apply, LinearMap.comp_apply, hDb, map_smul, map_smul,
        LinearMap.smul_apply]
      rcases k with i | k
      · rw [hE₂inl]
        split_ifs with h
        · simp
        · rw [hDb', smul_smul]
          simp only [d, ite_eq_right h, inv_inv]
          rw [hμ]
      · rw [hE₂inr, map_zero, smul_zero, smul_zero]

end Split

end CFSG.ComponentClassification.RankTwoClassical
