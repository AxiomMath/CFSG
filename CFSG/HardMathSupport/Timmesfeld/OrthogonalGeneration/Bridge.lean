module

public import CFSG.ClassicalGroups.Orthogonal.Matrix
public import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.Odd
public import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.Std

public section

namespace CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration

open Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.Orthogonal QuadraticMap Module
  CFSG.LieType.Universal.Spin

@[expose] noncomputable def glEquivStd (ι : Type) [Fintype ι] [DecidableEq ι] :
    GL ι (ZMod 2) ≃* ((ι → ZMod 2) ≃ₗ[ZMod 2] (ι → ZMod 2)) :=
  toLinEquiv ι (ZMod 2)

@[simp]
theorem glEquivStd_apply {ι : Type} [Fintype ι] [DecidableEq ι] (g : GL ι (ZMod 2))
    (v : ι → ZMod 2) : glEquivStd ι g v = (g : Matrix ι ι (ZMod 2)) *ᵥ v :=
  rfl

@[expose] def conjAut {K : Type*} [Semiring K] {V W : Type*} [AddCommMonoid V] [Module K V]
    [AddCommMonoid W] [Module K W] (φ : V ≃ₗ[K] W) : (V ≃ₗ[K] V) ≃* (W ≃ₗ[K] W) where
  toFun g := φ.symm.trans (g.trans φ)
  invFun h := φ.trans (h.trans φ.symm)
  left_inv g := by ext v; simp
  right_inv h := by ext w; simp
  map_mul' g h := by ext w; simp

@[simp]
theorem conjAut_apply {K : Type*} [Semiring K] {V W : Type*} [AddCommMonoid V] [Module K V]
    [AddCommMonoid W] [Module K W] (φ : V ≃ₗ[K] W) (g : V ≃ₗ[K] V) (w : W) :
    conjAut φ g w = φ (g (φ.symm w)) := rfl

@[simp]
theorem conjAut_symm_apply {K : Type*} [Semiring K] {V W : Type*} [AddCommMonoid V] [Module K V]
    [AddCommMonoid W] [Module K W] (φ : V ≃ₗ[K] W) (h : W ≃ₗ[K] W) (v : V) :
    (conjAut φ).symm h v = φ.symm (h (φ v)) := rfl

section Stated

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] {V : Type*} [AddCommGroup V]
  [Module K V]

theorem statedOmega_eq_comap_conjAut {Q : QuadraticForm K V} {Q₀ : (ι → K) → K}
    (φ : V ≃ₗ[K] (ι → K)) (hφ : ∀ v, Q₀ (φ v) = Q v) :
    StatedOmega Q₀ =
      ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆.comap
        ((toLinEquiv ι K).trans (conjAut φ).symm).toMonoidHom := by
  set ψ : GL ι K ≃* (V ≃ₗ[K] V) := (toLinEquiv ι K).trans (conjAut φ).symm with hψ
  have hS : {A : GL ι K | ∀ v, Q₀ ((A : Matrix ι ι K) *ᵥ v) = Q₀ v} =
      ((TauCeti.QuadraticMap.orthogonalGroup Q).comap ψ.toMonoidHom : Set (GL ι K)) := by
    ext A
    simp only [Set.mem_ofPred_eq, SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom,
      TauCeti.QuadraticMap.mem_orthogonalGroup_iff, hψ, MulEquiv.trans_apply, conjAut_symm_apply,
      toLinEquiv_apply]
    constructor
    · intro h v
      rw [← hφ, LinearEquiv.apply_symm_apply, ← hφ v]
      exact h _
    · intro h w
      have := h (φ.symm w)
      simp only [LinearEquiv.apply_symm_apply] at this
      rw [← hφ, ← hφ (φ.symm w)] at this
      simpa using this
  have key : ∀ H : Subgroup (V ≃ₗ[K] V),
      H.comap ψ.toMonoidHom = H.map ψ.symm.toMonoidHom := fun H =>
    Subgroup.comap_equiv_eq_map_symm ψ H
  unfold StatedOmega
  rw [hS, Subgroup.closure_eq, key, key, Subgroup.map_commutator]

theorem statedOmega_map_toLinEquiv_eq {Q : QuadraticForm K V} {Q₀ : (ι → K) → K}
    (φ : V ≃ₗ[K] (ι → K)) (hφ : ∀ v, Q₀ (φ v) = Q v) :
    (StatedOmega Q₀).map (toLinEquiv ι K).toMonoidHom =
      ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆.map
        (conjAut φ).toMonoidHom := by
  rw [statedOmega_eq_comap_conjAut φ hφ]
  ext x
  simp only [Subgroup.mem_map, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulEquiv.trans_apply]
  constructor
  · rintro ⟨A, hA, rfl⟩
    exact ⟨_, hA, by simp⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨(toLinEquiv ι K).symm (conjAut φ g), by simpa using hg, by simp⟩

end Stated

section Transport

variable {K : Type*} [Field K] {V W : Type*} [AddCommGroup V] [Module K V] [AddCommGroup W]
  [Module K W]

theorem polar_isometry {Q : QuadraticForm K V} {Q' : QuadraticForm K W} (φ : V ≃ₗ[K] W)
    (h : ∀ v, Q' (φ v) = Q v) (x y : V) : polar Q' (φ x) (φ y) = polar Q x y := by
  simp only [polar, ← map_add, h]

theorem nondegenerate_polarBilin_of_isometry {Q : QuadraticForm K V} {Q' : QuadraticForm K W}
    (φ : V ≃ₗ[K] W) (h : ∀ v, Q' (φ v) = Q v) (hQ' : (polarBilin Q').Nondegenerate) :
    (polarBilin Q).Nondegenerate := by
  refine nondegenerate_polarBilin_of_forall fun v hv => ?_
  have : φ v = 0 := by
    refine eq_zero_of_polar_eq_zero hQ' fun w => ?_
    have := hv (φ.symm w)
    rwa [← polar_isometry φ h, LinearEquiv.apply_symm_apply] at this
  exact (map_eq_zero_iff φ φ.injective).mp this

theorem not_exists_totallySingular_plane_of_isometry {Q : QuadraticForm K V}
    {Q' : QuadraticForm K W} (φ : V ≃ₗ[K] W) (h : ∀ v, Q' (φ v) = Q v)
    (hW : ¬ ∃ W' : Submodule K W, finrank K W' = 2 ∧ ∀ w ∈ W', Q' w = 0) :
    ¬ ∃ V' : Submodule K V, finrank K V' = 2 ∧ ∀ v ∈ V', Q v = 0 := by
  rintro ⟨V', hV', hQ⟩
  refine hW ⟨V'.map φ.toLinearMap, ?_, ?_⟩
  · rw [LinearEquiv.finrank_map_eq]
    exact hV'
  · rintro _ ⟨v, hv, rfl⟩
    rw [LinearEquiv.coe_coe, h]
    exact hQ v hv

end Transport

section Std

variable {K : Type} [Field K] [IsF2 K]

omit [IsF2 K] in
theorem finrank_plus (m : ℕ) : finrank K (Fin m ⊕ Fin m → K) = 2 * m := by
  rw [Module.finrank_fintype_fun_eq_card]
  simp [Fintype.card_sum]
  omega

omit [IsF2 K] in
theorem finrank_minus {m : ℕ} (hm : 1 ≤ m) :
    finrank K (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K) = 2 * m := by
  rw [Module.finrank_fintype_fun_eq_card]
  simp [Fintype.card_sum]
  omega

theorem irreducible_one_one : ∀ s : K, s ^ 2 + 1 * s + 1 ≠ 0 := by
  intro s
  rcases IsF2.eq_zero_or_one s with rfl | rfl
  · simp
  · rw [one_pow, one_mul, IsF2.one_add_one, zero_add]
    exact one_ne_zero

omit [IsF2 K] in
theorem quadMinus_two_val (x : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K) :
    quadMinus 2 K 1 1 x =
      x (.inl 0) * x (.inr (.inl 0)) + x (.inr (.inr 0)) ^ 2 +
        x (.inr (.inr 0)) * x (.inr (.inr 1)) + x (.inr (.inr 1)) ^ 2 := by
  rw [coe_quadMinus]
  simp [StatedQuadMinus]

omit [IsF2 K] in
theorem coords_zero (x : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K) :
    x = 0 ↔ x (.inl 0) = 0 ∧ x (.inr (.inl 0)) = 0 ∧ x (.inr (.inr 0)) = 0 ∧
      x (.inr (.inr 1)) = 0 := by
  constructor
  · rintro rfl
    simp
  · rintro ⟨h1, h2, h3, h4⟩
    funext i
    rcases i with i | i | i
    · fin_cases i
      exact h1
    · fin_cases i
      exact h2
    · fin_cases i
      · exact h3
      · exact h4

theorem finite_check : ∀ a b c d a' b' c' d' : K,
    a * b + c ^ 2 + c * d + d ^ 2 = 0 → a' * b' + c' ^ 2 + c' * d' + d' ^ 2 = 0 →
    (a + a') * (b + b') + (c + c') ^ 2 + (c + c') * (d + d') + (d + d') ^ 2 = 0 →
    (a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0) ∨ (a' = 0 ∧ b' = 0 ∧ c' = 0 ∧ d' = 0) ∨
      (a = a' ∧ b = b' ∧ c = c' ∧ d = d') := by
  have h2 : (1 : K) + 1 = 0 := IsF2.one_add_one
  intro a b c d a' b' c' d'
  rcases IsF2.eq_zero_or_one a with rfl | rfl <;> rcases IsF2.eq_zero_or_one b with rfl | rfl <;>
  rcases IsF2.eq_zero_or_one c with rfl | rfl <;> rcases IsF2.eq_zero_or_one d with rfl | rfl <;>
  rcases IsF2.eq_zero_or_one a' with rfl | rfl <;> rcases IsF2.eq_zero_or_one b' with rfl | rfl <;>
  rcases IsF2.eq_zero_or_one c' with rfl | rfl <;> rcases IsF2.eq_zero_or_one d' with rfl | rfl <;>
  simp [h2]

theorem not_exists_totallySingular_plane_quadMinus_two :
    ¬ ∃ W : Submodule K (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K),
      finrank K W = 2 ∧ ∀ w ∈ W, quadMinus 2 K 1 1 w = 0 := by
  rintro ⟨W, hW, hQ⟩
  let b := Module.finBasisOfFinrankEq K W hW
  have hli := b.linearIndependent
  have hx0 : (b 0 : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K) ≠ 0 := fun h =>
    hli.ne_zero 0 (Subtype.ext h)
  have hy0 : (b 1 : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K) ≠ 0 := fun h =>
    hli.ne_zero 1 (Subtype.ext h)
  have hxy : (b 0 : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K) ≠ b 1 := fun h =>
    absurd (hli.injective (Subtype.ext h)) (by decide)
  have h1 := hQ _ (b 0).2
  have h2 := hQ _ (b 1).2
  have h3 := hQ _ (W.add_mem (b 0).2 (b 1).2)
  rw [quadMinus_two_val] at h1 h2 h3
  simp only [Pi.add_apply] at h3
  rcases finite_check _ _ _ _ _ _ _ _ h1 h2 h3 with h | h | h
  · exact hx0 ((coords_zero _).mpr h)
  · exact hy0 ((coords_zero _).mpr h)
  · refine hxy (funext fun i => ?_)
    rcases i with i | i | i
    · fin_cases i
      exact h.1
    · fin_cases i
      exact h.2.1
    · fin_cases i
      · exact h.2.2.1
      · exact h.2.2.2

variable {V : Type*} [AddCommGroup V] [Module K V]

theorem commutator_orthogonalGroup_eq_of_isometry_plus {Q : QuadraticForm K V} {m : ℕ}
    (hm : 3 ≤ m) (φ : V ≃ₗ[K] (Fin m ⊕ Fin m → K)) (hφ : ∀ v, quadPlus m K (φ v) = Q v) :
    ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q := by
  have hfd : FiniteDimensional K V := LinearEquiv.finiteDimensional φ.symm
  have hd : finrank K V = 2 * m := by rw [φ.finrank_eq, finrank_plus]
  exact commutator_orthogonalGroup_eq_elementaryGroup_f2
    (nondegenerate_polarBilin_of_isometry φ hφ (nondegenerate_polarBilin_quadPlus m K))
    (by omega) (Or.inl (by omega))

theorem commutator_orthogonalGroup_eq_of_isometry_minus {Q : QuadraticForm K V} {m : ℕ}
    (hm : 2 ≤ m) (φ : V ≃ₗ[K] (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K))
    (hφ : ∀ v, quadMinus m K 1 1 (φ v) = Q v) :
    ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q := by
  have hfd : FiniteDimensional K V := LinearEquiv.finiteDimensional φ.symm
  have hd : finrank K V = 2 * m := by rw [φ.finrank_eq, finrank_minus (by omega)]
  refine commutator_orthogonalGroup_eq_elementaryGroup_f2
    (nondegenerate_polarBilin_of_isometry φ hφ
      (nondegenerate_polarBilin_quadMinus_of_finite m K irreducible_one_one)) (by omega) ?_
  by_cases h3 : 3 ≤ m
  · exact Or.inl (by omega)
  · obtain rfl : m = 2 := by omega
    exact Or.inr (not_exists_totallySingular_plane_of_isometry φ hφ
      not_exists_totallySingular_plane_quadMinus_two)

omit [IsF2 K] in
theorem isometry_plus_facts {Q : QuadraticForm K V} {m : ℕ} (φ : V ≃ₗ[K] (Fin m ⊕ Fin m → K))
    (hφ : ∀ v, quadPlus m K (φ v) = Q v) :
    FiniteDimensional K V ∧ finrank K V = 2 * m ∧ (polarBilin Q).Nondegenerate :=
  ⟨LinearEquiv.finiteDimensional φ.symm, by rw [φ.finrank_eq, finrank_plus],
    nondegenerate_polarBilin_of_isometry φ hφ (nondegenerate_polarBilin_quadPlus m K)⟩

theorem isometry_minus_facts {Q : QuadraticForm K V} {m : ℕ} (hm : 1 ≤ m)
    (φ : V ≃ₗ[K] (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K))
    (hφ : ∀ v, quadMinus m K 1 1 (φ v) = Q v) :
    FiniteDimensional K V ∧ finrank K V = 2 * m ∧ (polarBilin Q).Nondegenerate :=
  ⟨LinearEquiv.finiteDimensional φ.symm, by rw [φ.finrank_eq, finrank_minus hm],
    nondegenerate_polarBilin_of_isometry φ hφ
      (nondegenerate_polarBilin_quadMinus_of_finite m K irreducible_one_one)⟩

theorem mem_elementaryGroup_of_odd_pow_of_isometry_plus {Q : QuadraticForm K V} {m : ℕ}
    (hm : 3 ≤ m) (φ : V ≃ₗ[K] (Fin m ⊕ Fin m → K)) (hφ : ∀ v, quadPlus m K (φ v) = Q v)
    {g : V ≃ₗ[K] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {N : ℕ} (hN : Odd N)
    (hgN : g ^ N = 1) : g ∈ elementaryGroup Q := by
  obtain ⟨hfd, hd, hnd⟩ := isometry_plus_facts φ hφ
  exact mem_elementaryGroup_of_pow_eq_one_of_odd hnd (by omega) (Or.inl (by omega)) hg hN hgN

theorem mem_elementaryGroup_of_odd_pow_of_isometry_minus {Q : QuadraticForm K V} {m : ℕ}
    (hm : 2 ≤ m) (φ : V ≃ₗ[K] (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K))
    (hφ : ∀ v, quadMinus m K 1 1 (φ v) = Q v) {g : V ≃ₗ[K] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {N : ℕ} (hN : Odd N) (hgN : g ^ N = 1) :
    g ∈ elementaryGroup Q := by
  obtain ⟨hfd, hd, hnd⟩ := isometry_minus_facts (by omega) φ hφ
  refine mem_elementaryGroup_of_pow_eq_one_of_odd hnd (by omega) ?_ hg hN hgN
  by_cases h3 : 3 ≤ m
  · exact Or.inl (by omega)
  · obtain rfl : m = 2 := by omega
    exact Or.inr (not_exists_totallySingular_plane_of_isometry φ hφ
      not_exists_totallySingular_plane_quadMinus_two)

theorem eq_one_of_commute_elementaryGroup_of_isometry_plus {Q : QuadraticForm K V} {m : ℕ}
    (hm : 3 ≤ m) (φ : V ≃ₗ[K] (Fin m ⊕ Fin m → K)) (hφ : ∀ v, quadPlus m K (φ v) = Q v)
    {g : V ≃ₗ[K] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hc : ∀ x ∈ elementaryGroup Q, g * x = x * g) : g = 1 := by
  obtain ⟨hfd, hd, hnd⟩ := isometry_plus_facts φ hφ
  exact eq_one_of_commute_elementaryGroup hnd (by omega) hg hc

theorem eq_one_of_commute_elementaryGroup_of_isometry_minus {Q : QuadraticForm K V} {m : ℕ}
    (hm : 3 ≤ m) (φ : V ≃ₗ[K] (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K))
    (hφ : ∀ v, quadMinus m K 1 1 (φ v) = Q v) {g : V ≃ₗ[K] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hc : ∀ x ∈ elementaryGroup Q, g * x = x * g) : g = 1 := by
  obtain ⟨hfd, hd, hnd⟩ := isometry_minus_facts (by omega) φ hφ
  exact eq_one_of_commute_elementaryGroup hnd (by omega) hg hc

end Std

section Final

variable {K : Type} [Field K] [IsF2 K]

theorem statedOmega_quadPlus_eq_map_elementaryGroup {m : ℕ} (hm : 3 ≤ m) :
    (StatedOmega (StatedQuadPlus m K)).map (toLinEquiv (Fin m ⊕ Fin m) K).toMonoidHom =
      elementaryGroup (quadPlus m K) := by
  have h := commutator_orthogonalGroup_eq_of_isometry_plus (Q := quadPlus m K) hm
    (LinearEquiv.refl K _) fun v => rfl
  rw [statedOmega_eq_comap (coe_quadPlus m K), h]
  exact Subgroup.map_comap_eq_self_of_surjective (toLinEquiv _ K).surjective _

theorem statedOmega_quadMinus_eq_map_elementaryGroup {m : ℕ} (hm : 2 ≤ m) :
    (StatedOmega (StatedQuadMinus m K 1 1)).map
        (toLinEquiv (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K).toMonoidHom =
      elementaryGroup (quadMinus m K 1 1) := by
  have h := commutator_orthogonalGroup_eq_of_isometry_minus (Q := quadMinus m K 1 1) hm
    (LinearEquiv.refl K _) fun v => rfl
  rw [statedOmega_eq_comap (coe_quadMinus m K 1 1), h]
  exact Subgroup.map_comap_eq_self_of_surjective (toLinEquiv _ K).surjective _

end Final

section ZModTwo

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}

theorem statedOmega_map_glEquiv_plus {m : ℕ} (hm : 3 ≤ m)
    (φ : V ≃ₗ[ZMod 2] (Fin m ⊕ Fin m → ZMod 2)) (hφ : ∀ v, quadPlus m (ZMod 2) (φ v) = Q v) :
    (StatedOmega (StatedQuadPlus m (ZMod 2))).map (glEquivStd (Fin m ⊕ Fin m)).toMonoidHom =
      (elementaryGroup Q).map (conjAut φ).toMonoidHom := by
  have hφ' : ∀ v, StatedQuadPlus m (ZMod 2) (φ v) = Q v := fun v => by
    rw [← coe_quadPlus]; exact hφ v
  rw [← commutator_orthogonalGroup_eq_of_isometry_plus hm φ hφ]
  exact statedOmega_map_toLinEquiv_eq φ hφ'

theorem statedOmega_map_glEquiv_minus {m : ℕ} (hm : 2 ≤ m)
    (φ : V ≃ₗ[ZMod 2] (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → ZMod 2))
    (hφ : ∀ v, quadMinus m (ZMod 2) 1 1 (φ v) = Q v) :
    (StatedOmega (StatedQuadMinus m (ZMod 2) 1 1)).map
        (glEquivStd (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2)).toMonoidHom =
      (elementaryGroup Q).map (conjAut φ).toMonoidHom := by
  have hφ' : ∀ v, StatedQuadMinus m (ZMod 2) 1 1 (φ v) = Q v := fun v => by
    rw [← coe_quadMinus]; exact hφ v
  rw [← commutator_orthogonalGroup_eq_of_isometry_minus hm φ hφ]
  exact statedOmega_map_toLinEquiv_eq φ hφ'

theorem commutator_orthogonalGroup_eq_of_isPlusSpace {m : ℕ} (hm : 3 ≤ m)
    (h : IsPlusSpace Q m) :
    ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q := by
  obtain ⟨φ, hφ⟩ := h
  exact commutator_orthogonalGroup_eq_of_isometry_plus hm φ hφ

theorem commutator_orthogonalGroup_eq_of_isMinusSpace {m : ℕ} (hm : 2 ≤ m)
    (h : IsMinusSpace Q m) :
    ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q := by
  obtain ⟨φ, hφ⟩ := h
  exact commutator_orthogonalGroup_eq_of_isometry_minus hm φ hφ

theorem mem_elementaryGroup_of_odd_pow_of_isPlusSpace {m : ℕ} (hm : 3 ≤ m) (h : IsPlusSpace Q m)
    {g : V ≃ₗ[ZMod 2] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {N : ℕ} (hN : Odd N)
    (hgN : g ^ N = 1) : g ∈ elementaryGroup Q := by
  obtain ⟨φ, hφ⟩ := h
  exact mem_elementaryGroup_of_odd_pow_of_isometry_plus hm φ hφ hg hN hgN

theorem mem_elementaryGroup_of_odd_pow_of_isMinusSpace {m : ℕ} (hm : 2 ≤ m)
    (h : IsMinusSpace Q m) {g : V ≃ₗ[ZMod 2] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {N : ℕ} (hN : Odd N) (hgN : g ^ N = 1) :
    g ∈ elementaryGroup Q := by
  obtain ⟨φ, hφ⟩ := h
  exact mem_elementaryGroup_of_odd_pow_of_isometry_minus hm φ hφ hg hN hgN

theorem eq_one_of_commute_elementaryGroup_of_isPlusSpace {m : ℕ} (hm : 3 ≤ m)
    (h : IsPlusSpace Q m) {g : V ≃ₗ[ZMod 2] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hc : ∀ x ∈ elementaryGroup Q, g * x = x * g) : g = 1 := by
  obtain ⟨φ, hφ⟩ := h
  exact eq_one_of_commute_elementaryGroup_of_isometry_plus hm φ hφ hg hc

theorem eq_one_of_commute_elementaryGroup_of_isMinusSpace {m : ℕ} (hm : 3 ≤ m)
    (h : IsMinusSpace Q m) {g : V ≃ₗ[ZMod 2] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hc : ∀ x ∈ elementaryGroup Q, g * x = x * g) : g = 1 := by
  obtain ⟨φ, hφ⟩ := h
  exact eq_one_of_commute_elementaryGroup_of_isometry_minus hm φ hφ hg hc

end ZModTwo

end CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration
