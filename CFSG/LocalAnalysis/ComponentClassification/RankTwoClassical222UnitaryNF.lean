module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222Linear

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Module Matrix CFSG.LocalAnalysis.ComponentInitial
open scoped Matrix

section Gram

variable {K : Type} [Field K] {ℓ r : ℕ}

@[expose] def swapXW : Fin ℓ ⊕ (Fin ℓ ⊕ Fin r) → Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)
  | .inl i => .inr (.inl i)
  | .inr (.inl i) => .inl i
  | .inr (.inr k) => .inr (.inr k)

theorem swapXW_swapXW (p : Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) : swapXW (swapXW p) = p := by
  rcases p with i | i | k <;> rfl

variable (K ℓ r) in
@[expose] def unitGram : Matrix (Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) (Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) K :=
  Matrix.of fun p q => if q = swapXW p then 1 else 0

end Gram

section Transport

variable {ι κ K : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Field K]
  {σ : K →+* K}

theorem adjM_mul_self_of_gram (b : Module.Basis κ K (ι → K)) {G : Matrix κ κ K}
    (hG : ∀ p q, hform σ (b p) (b q) = G p q) {B : Matrix κ κ K}
    (hB : adjM σ B * G * B = G) :
    adjM σ ((Matrix.toLinAlgEquiv'.trans (LinearMap.toMatrixAlgEquiv b)).symm B) *
      (Matrix.toLinAlgEquiv'.trans (LinearMap.toMatrixAlgEquiv b)).symm B = 1 := by
  set φ : Matrix ι ι K ≃ₐ[K] Matrix κ κ K :=
    Matrix.toLinAlgEquiv'.trans (LinearMap.toMatrixAlgEquiv b) with hφ
  set Z := φ.symm B with hZ
  have h1 : Z = LinearMap.toMatrix' (Matrix.toLin b b B) := by
    apply φ.injective
    rw [hZ, AlgEquiv.apply_symm_apply]
    simp only [φ, AlgEquiv.trans_apply]
    rw [show Matrix.toLinAlgEquiv' (LinearMap.toMatrix' (Matrix.toLin b b B)) =
      Matrix.toLin b b B from LinearMap.ext fun v => by
        rw [Matrix.toLinAlgEquiv'_apply, LinearMap.toMatrix'_mulVec]]
    exact ((LinearMap.toMatrixAlgEquiv_toLinAlgEquiv b B)).symm
  have hZb : ∀ q, Z *ᵥ b q = ∑ p, B p q • b p := fun q => by
    rw [h1, LinearMap.toMatrix'_mulVec, Matrix.toLin_self]
  have hZG : ∀ p q, hform σ (Z *ᵥ b p) (Z *ᵥ b q) = G p q := by
    intro p q
    have h2 := congrFun (congrFun hB p) q
    rw [← h2, hZb, hZb]
    simp only [hform_sum_left, hform_sum_right, hform_smul_left, hform_smul_right, hG,
      Matrix.mul_apply, adjM, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hZuv : ∀ u v, hform σ (Z *ᵥ u) (Z *ᵥ v) = hform σ u v := by
    intro u v
    rw [← b.sum_repr u, ← b.sum_repr v]
    simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, hform_sum_left, hform_sum_right,
      hform_smul_left, hform_smul_right, hZG, hG]
  rw [Matrix.ext_iff_mulVec]
  intro v
  have h4 : ∀ u, hform σ u ((adjM σ Z * Z) *ᵥ v - v) = 0 := by
    intro u
    rw [hform_sub_right, ← Matrix.mulVec_mulVec, ← hform_mulVec, hZuv, sub_self]
  rw [sub_eq_zero.mp (eq_zero_of_hform_left h4), Matrix.one_mulVec]

end Transport

section XFamily

variable {n m : ℕ} {K : Type} [Field K]

theorem exists_xfamily (hU : UnitaryFieldData 2 m K) {N : Matrix (Fin n) (Fin n) K}
    (hN : N * N = 0) (hNh : adjM hU.bar N = N) :
    ∃ x : Fin (finrank K (LinearMap.range N.mulVecLin)) → Fin n → K,
      (∀ i j, hform hU.bar (x i) (x j) = 0) ∧
      ∀ i j, hform hU.bar (x i) (N *ᵥ x j) = if i = j then 1 else 0 := by
  classical
  have : CharP K 2 := hU.charP
  have : Finite K := hU.finite
  set σ := hU.bar with hσdef
  have hσ : ∀ x, σ (σ x) = x := hU.bar_bar
  have htr : ∀ c, σ c = c → ∃ d, d + σ d = c := by
    intro c hc
    obtain ⟨d, hd⟩ := hU.traceLin_surjective ⟨c, (hU.mem_fixedField).mpr hc⟩
    exact ⟨d, congrArg Subtype.val hd⟩
  have hNadj : ∀ u v, hform σ (N *ᵥ u) v = hform σ u (N *ᵥ v) := fun u v => by
    rw [hform_mulVec, hNh]
  set U := LinearMap.range N.mulVecLin with hU'
  set k := finrank K U with hk
  let bU := Module.finBasis K U
  set u : Fin k → Fin n → K := fun i => (bU i : Fin n → K) with hu
  have hmemU : ∀ w ∈ U, ∃ z, w = N *ᵥ z := by
    rintro _ ⟨z, rfl⟩
    exact ⟨z, rfl⟩
  have huU : ∀ i, u i ∈ U := fun i => (bU i).2
  have hisoU : ∀ w ∈ U, ∀ w' ∈ U, hform σ w w' = 0 := by
    intro w hw w' hw'
    obtain ⟨z, rfl⟩ := hmemU w hw
    obtain ⟨z', rfl⟩ := hmemU w' hw'
    rw [hNadj, Matrix.mulVec_mulVec, hN, Matrix.zero_mulVec, hform_zero_right]
  have hli : LinearIndependent K u := bU.linearIndependent.map' U.subtype U.ker_subtype
  obtain ⟨u', hdual⟩ := exists_hform_dual hσ u hli
  obtain ⟨u'', hdual'', hiso'', -⟩ := exists_isotropic_dual hσ htr u u'
    (fun i j => hisoU _ (huU i) _ (huU j)) hdual
  have hu''u : ∀ i j, hform σ (u'' i) (u j) = if i = j then 1 else 0 := fun i j => by
    rw [hform_comm hσ, hdual'']
    by_cases h : i = j
    · subst h
      simp
    · simp [h, Ne.symm h]
  have hexpU : ∀ z ∈ U, z = ∑ i, hform σ (u'' i) z • u i := by
    intro z hz
    have h1 : ∑ x, bU.repr ⟨z, hz⟩ x • u x = z := by
      have h0 := congrArg Subtype.val (bU.sum_repr ⟨z, hz⟩)
      rw [Submodule.coe_sum] at h0
      simp only [Submodule.coe_smul] at h0
      exact h0
    have h2 : ∀ i, hform σ (u'' i) z = bU.repr ⟨z, hz⟩ i := by
      intro i
      conv_lhs => rw [← h1]
      rw [hform_sum_right]
      simp [hform_smul_right, hu''u]
    simp only [h2]
    exact h1.symm
  let L : (Fin k → K) →ₗ[K] (Fin n → K) := Fintype.linearCombination K u''
  have hL : ∀ c, L c = ∑ i, c i • u'' i := fun c => Fintype.linearCombination_apply K u'' c
  let B : (Fin k → K) →ₛₗ[σ] (Fin k → K) →ₗ[K] K :=
    LinearMap.mk₂'ₛₗ σ (RingHom.id K) (fun c c' => hform σ (L c) (N *ᵥ L c'))
      (fun a b c => by rw [map_add, hform_add_left])
      (fun t a b => by rw [map_smul, hform_smul_left, smul_eq_mul])
      (fun a b c => by rw [map_add, Matrix.mulVec_add, hform_add_right])
      (fun t a b => by
        rw [map_smul, Matrix.mulVec_smul, hform_smul_right, smul_eq_mul, RingHom.id_apply])
  have hBapp : ∀ c c', B c c' = hform σ (L c) (N *ᵥ L c') := fun c c' => rfl
  have hLs : ∀ i, L (Pi.single i 1) = u'' i := fun i => by
    rw [hL]
    simp [Pi.single_apply]
  have hB : B.IsSymm := ⟨fun c c' => by
    rw [hBapp, hBapp, ← hform_comm hσ, hNadj]⟩
  have hBl : B.SeparatingLeft := by
    intro c hc
    have hz : N *ᵥ L c = 0 := by
      have hzU : N *ᵥ L c ∈ U := ⟨L c, rfl⟩
      rw [hexpU _ hzU]
      refine Finset.sum_eq_zero fun i _ => ?_
      have h1 := hc (Pi.single i 1)
      rw [hBapp, hLs] at h1
      rw [hform_comm hσ, hNadj, h1, map_zero, zero_smul]
    ext i
    obtain ⟨z, hzi⟩ := hmemU (u i) (huU i)
    have h2 : hform σ (u i) (L c) = c i := by
      rw [hL, hform_sum_right]
      simp [hform_smul_right, hdual'']
    rw [← h2, hzi, hNadj, hz, hform_zero_right, Pi.zero_apply]
  obtain ⟨c₀, hc₀⟩ := hU.exists_bar_ne
  have hnorm : ∀ d : K, σ d = d → d ≠ 0 → ∃ c, σ c * c = d := fun d hd _ => by
    obtain ⟨c, hc⟩ := hU.normHom_surjective ⟨d, hd⟩
    exact ⟨c, by rw [mul_comm]; exact congrArg Subtype.val hc⟩
  obtain ⟨cfam, hcfam⟩ := exists_orthonormal_family hB hBl hc₀ hnorm (r := k)
    (by rw [Module.finrank_fin_fun])
  refine ⟨fun i => L (cfam i), fun i j => ?_, fun i j => ?_⟩
  · show hform σ (L (cfam i)) (L (cfam j)) = 0
    rw [hL, hL, hform_sum_left]
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [hform_smul_left, hform_sum_right]
    simp [hform_smul_right, hiso'']
  · show hform σ (L (cfam i)) (N *ᵥ L (cfam j)) = _
    rw [← hBapp]
    exact hcfam i j

end XFamily

section Adapted

variable {n m : ℕ} {K : Type} [Field K]

theorem exists_unitary_adapted (hU : UnitaryFieldData 2 m K) {N : Matrix (Fin n) (Fin n) K}
    (hN : N * N = 0) (hNh : adjM hU.bar N = N) (hN0 : N ≠ 0) :
    ∃ (ℓ r : ℕ) (φ : Matrix (Fin n) (Fin n) K ≃ₐ[K]
      Matrix (Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) (Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) K),
      ℓ ≠ 0 ∧ n = 2 * ℓ + r ∧ φ N = sqZeroStd ℓ r ∧ (∀ Y, (φ.symm Y).det = Y.det) ∧
        ∀ B, adjM hU.bar B * unitGram K ℓ r * B = unitGram K ℓ r →
          adjM hU.bar (φ.symm B) * φ.symm B = 1 := by
  classical
  have : CharP K 2 := hU.charP
  have : Finite K := hU.finite
  set σ := hU.bar with hσdef
  have hσ : ∀ x, σ (σ x) = x := hU.bar_bar
  have hNadj : ∀ u v, hform σ (N *ᵥ u) v = hform σ u (N *ᵥ v) := fun u v => by
    rw [hform_mulVec, hNh]
  have hℓ0 : finrank K (LinearMap.range N.mulVecLin) ≠ 0 := by
    intro h
    apply hN0
    rw [Submodule.finrank_eq_zero, LinearMap.range_eq_bot] at h
    refine Matrix.ext_iff_mulVec.mpr fun v => ?_
    have h1 := LinearMap.congr_fun h v
    simp only [Matrix.mulVecLin_apply, LinearMap.zero_apply] at h1
    rw [h1, Matrix.zero_mulVec]
  have h2ℓ : 2 * finrank K (LinearMap.range N.mulVecLin) ≤ n := by
    have hle : LinearMap.range N.mulVecLin ≤ LinearMap.ker N.mulVecLin := by
      rintro _ ⟨v, rfl⟩
      simp [LinearMap.mem_ker, Matrix.mulVec_mulVec, hN]
    have h1 := Submodule.finrank_mono hle
    have h2 := LinearMap.finrank_range_add_finrank_ker N.mulVecLin
    rw [Module.finrank_fin_fun] at h2
    omega
  obtain ⟨x, hxx, hxN⟩ := exists_xfamily hU hN hNh
  generalize hℓ : finrank K (LinearMap.range N.mulVecLin) = ℓ at x hxx hxN hℓ0 h2ℓ
  replace hxx : ∀ i j, hform σ (x i) (x j) = 0 := hxx
  set w : Fin ℓ → Fin n → K := fun i => N *ᵥ x i with hw
  have hww : ∀ i j, hform σ (w i) (w j) = 0 := fun i j => by
    rw [hw, hNadj, Matrix.mulVec_mulVec, hN, Matrix.zero_mulVec, hform_zero_right]
  have hxw : ∀ i j, hform σ (x i) (w j) = if i = j then 1 else 0 := hxN
  have hwx : ∀ i j, hform σ (w i) (x j) = if i = j then 1 else 0 := fun i j => by
    rw [hform_comm hσ, hxw]
    by_cases h : i = j
    · subst h
      simp
    · simp [h, Ne.symm h]
  let Φ : (Fin n → K) →ₗ[K] (Fin ℓ ⊕ Fin ℓ → K) :=
    Matrix.toLin' (Matrix.of fun (p : Fin ℓ ⊕ Fin ℓ) i => σ (Sum.elim x w p i))
  have hΦ : ∀ v p, Φ v p = hform σ (Sum.elim x w p) v := fun v p => by
    simp only [Φ, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Matrix.of_apply, hform,
      Function.comp]
  set Y := LinearMap.ker Φ with hYdef
  have hmemY : ∀ y, y ∈ Y ↔ (∀ i, hform σ (x i) y = 0) ∧ ∀ i, hform σ (w i) y = 0 := by
    intro y
    rw [hYdef, LinearMap.mem_ker, funext_iff]
    constructor
    · intro h
      exact ⟨fun i => by simpa [hΦ] using h (.inl i), fun i => by simpa [hΦ] using h (.inr i)⟩
    · rintro ⟨h1, h2⟩ p
      rcases p with i | i
      · rw [hΦ]; exact h1 i
      · rw [hΦ]; exact h2 i
  set r := n - 2 * ℓ with hr
  have hrY : r ≤ finrank K Y := by
    have h1 := LinearMap.finrank_range_add_finrank_ker Φ
    have h2 := Submodule.finrank_le (LinearMap.range Φ)
    rw [Module.finrank_fin_fun, ← hYdef] at h1
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin] at h2
    omega
  have hπ : ∀ v, v - ∑ i, hform σ (w i) v • x i - ∑ i, hform σ (x i) v • w i ∈ Y := by
    intro v
    rw [hmemY]
    refine ⟨fun k => ?_, fun k => ?_⟩
    · rw [hform_sub_right, hform_sub_right, hform_sum_right, hform_sum_right]
      simp [hform_smul_right, hxx, hxw]
    · rw [hform_sub_right, hform_sub_right, hform_sum_right, hform_sum_right]
      simp [hform_smul_right, hwx, hww]
  let BY : Y →ₛₗ[σ] Y →ₗ[K] K :=
    LinearMap.mk₂'ₛₗ σ (RingHom.id K) (fun a b => hform σ (a : Fin n → K) b)
      (fun a b c => by rw [Submodule.coe_add, hform_add_left])
      (fun t a b => by rw [Submodule.coe_smul, hform_smul_left, smul_eq_mul])
      (fun a b c => by rw [Submodule.coe_add, hform_add_right])
      (fun t a b => by rw [Submodule.coe_smul, hform_smul_right, smul_eq_mul, RingHom.id_apply])
  have hBYapp : ∀ a b : Y, BY a b = hform σ (a : Fin n → K) b := fun a b => rfl
  have hBY : BY.IsSymm := ⟨fun a b => by rw [hBYapp, hBYapp, ← hform_comm hσ]⟩
  have hBYl : BY.SeparatingLeft := by
    intro a ha
    have hax : ∀ i, hform σ (a : Fin n → K) (x i) = 0 := fun i => by
      rw [hform_comm hσ, ((hmemY a).mp a.2).1 i, map_zero]
    have haw : ∀ i, hform σ (a : Fin n → K) (w i) = 0 := fun i => by
      rw [hform_comm hσ, ((hmemY a).mp a.2).2 i, map_zero]
    have hav : ∀ v, hform σ (a : Fin n → K) v = 0 := by
      intro v
      have h1 := ha ⟨_, hπ v⟩
      rw [hBYapp] at h1
      simp only [hform_sub_right, hform_sum_right, hform_smul_right, hax, haw, mul_zero,
        Finset.sum_const_zero, sub_zero] at h1
      exact h1
    exact Subtype.ext (eq_zero_of_hform_right hσ hav)
  obtain ⟨c₀, hc₀⟩ := hU.exists_bar_ne
  have hnorm : ∀ d : K, σ d = d → d ≠ 0 → ∃ c, σ c * c = d := fun d hd _ => by
    obtain ⟨c, hc⟩ := hU.normHom_surjective ⟨d, hd⟩
    exact ⟨c, by rw [mul_comm]; exact congrArg Subtype.val hc⟩
  obtain ⟨yfam, hyfam⟩ := exists_orthonormal_family hBY hBYl hc₀ hnorm hrY
  let b0 : Fin ℓ ⊕ (Fin ℓ ⊕ Fin r) → Fin n → K :=
    Sum.elim x (Sum.elim w fun k => (yfam k : Fin n → K))
  have hyx : ∀ k i, hform σ (yfam k : Fin n → K) (x i) = 0 := fun k i => by
    rw [hform_comm hσ, ((hmemY _).mp (yfam k).2).1 i, map_zero]
  have hyw : ∀ k i, hform σ (yfam k : Fin n → K) (w i) = 0 := fun k i => by
    rw [hform_comm hσ, ((hmemY _).mp (yfam k).2).2 i, map_zero]
  have hG : ∀ p q, hform σ (b0 p) (b0 q) = unitGram K ℓ r p q := by
    intro p q
    rcases p with i | i | k <;> rcases q with j | j | l
    · simp [b0, unitGram, swapXW, hxx]
    · simp [b0, unitGram, swapXW, hxw, eq_comm]
    · simp [b0, unitGram, swapXW, ((hmemY _).mp (yfam l).2).1 i]
    · simp [b0, unitGram, swapXW, hwx, eq_comm]
    · simp [b0, unitGram, swapXW, hww]
    · simp [b0, unitGram, swapXW, ((hmemY _).mp (yfam l).2).2 i]
    · simp [b0, unitGram, swapXW, hyx]
    · simp [b0, unitGram, swapXW, hyw]
    · have := hyfam k l
      rw [hBYapp] at this
      simp [b0, unitGram, swapXW, this, eq_comm]
  have hli : LinearIndependent K b0 := by
    rw [Fintype.linearIndependent_iff]
    intro g hg p
    have h1 := congrArg (hform σ (b0 (swapXW p))) hg
    rw [hform_sum_right, hform_zero_right] at h1
    simp only [hform_smul_right, hG, unitGram, Matrix.of_apply, swapXW_swapXW, mul_ite,
      mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at h1
    exact h1
  have hcard : Fintype.card (Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) = finrank K (Fin n → K) := by
    rw [Module.finrank_fin_fun]
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  let bas := basisOfLinearIndependentOfCardEqFinrank' b0 hli hcard
  have hbas : ∀ p, bas p = b0 p := fun p => by
    simp [bas]
  have hliw : LinearIndependent K w := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have h1 := congrArg (hform σ (x i)) hg
    rw [hform_sum_right, hform_zero_right] at h1
    simpa [hform_smul_right, hxw] using h1
  have hspanw : Submodule.span K (Set.range w) = LinearMap.range N.mulVecLin := by
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact ⟨x i, rfl⟩
    · rw [finrank_span_eq_card hliw, Fintype.card_fin, hℓ]
  have hNY : ∀ y ∈ Y, N *ᵥ y = 0 := by
    intro y hy
    refine eq_zero_of_hform_left (σ := σ) fun v => ?_
    rw [← hNadj]
    have key : ∀ z ∈ Submodule.span K (Set.range w), hform σ z y = 0 := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨i, rfl⟩ := hz
        exact ((hmemY y).mp hy).2 i
      | zero => exact hform_zero_left _
      | add a b _ _ ha hb => rw [hform_add_left, ha, hb, add_zero]
      | smul t a _ ha => rw [hform_smul_left, ha, mul_zero]
    refine key _ ?_
    rw [hspanw]
    exact ⟨v, rfl⟩
  let φ : Matrix (Fin n) (Fin n) K ≃ₐ[K]
      Matrix (Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) (Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) K :=
    Matrix.toLinAlgEquiv'.trans (LinearMap.toMatrixAlgEquiv bas)
  refine ⟨ℓ, r, φ, hℓ0, by omega, ?_, fun Z => ?_, fun B hB => ?_⟩
  · ext p q
    simp only [φ, AlgEquiv.trans_apply, LinearMap.toMatrixAlgEquiv_apply,
      Matrix.toLinAlgEquiv'_apply, sqZeroStd_apply]
    rcases q with c | c | k
    · have h1 : N *ᵥ bas (Sum.inl c) = bas (Sum.inr (Sum.inl c)) := by
        rw [hbas, hbas]
        rfl
      rw [h1, bas.repr_self, Finsupp.single_apply]
      simp [eq_comm]
    · have h1 : N *ᵥ bas (Sum.inr (Sum.inl c)) = 0 := by
        rw [hbas]
        show N *ᵥ (N *ᵥ x c) = 0
        rw [Matrix.mulVec_mulVec, hN, Matrix.zero_mulVec]
      rw [h1, map_zero]
      rfl
    · have h1 : N *ᵥ bas (Sum.inr (Sum.inr k)) = 0 := by
        rw [hbas]
        exact hNY _ (yfam k).2
      rw [h1, map_zero]
      rfl
  · have h1 : φ.symm Z = LinearMap.toMatrix' (Matrix.toLin bas bas Z) := by
      apply φ.injective
      rw [AlgEquiv.apply_symm_apply]
      simp only [φ, AlgEquiv.trans_apply]
      rw [show Matrix.toLinAlgEquiv' (LinearMap.toMatrix' (Matrix.toLin bas bas Z)) =
        Matrix.toLin bas bas Z from LinearMap.ext fun v => by
          rw [Matrix.toLinAlgEquiv'_apply, LinearMap.toMatrix'_mulVec]]
      exact ((LinearMap.toMatrixAlgEquiv_toLinAlgEquiv bas Z)).symm
    rw [h1, LinearMap.det_toMatrix', LinearMap.det_toLin]
  · exact adjM_mul_self_of_gram bas (fun p q => by rw [hbas, hbas]; exact hG p q) hB

end Adapted

end CFSG.ComponentClassification.RankTwoClassical
