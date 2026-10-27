module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222Alpha
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAlpha

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Module Matrix Subgroup CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.RankTwoStandard
open scoped Matrix

section Torus

variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] [Finite K] [CharP K 2]

theorem exists_det_one_conj_eq_smul (N : Matrix ι ι K) (hN : N * N = 0) {l : K} (hl : l ≠ 0) :
    ∃ d : GL ι K, (d : Matrix ι ι K).det = 1 ∧
      (d : Matrix ι ι K) * N * ((d⁻¹ : GL ι K) : Matrix ι ι K) = l • N := by
  classical
  set Nl := Matrix.toLin' N with hNl
  have hNl2 : Nl ∘ₗ Nl = 0 := by rw [hNl, ← Matrix.toLin'_mul, hN, map_zero]
  obtain ⟨r, b, hb1, hb2⟩ := exists_basis_sq_eq_zero Nl hNl2
  generalize finrank K (LinearMap.range Nl) = ℓ at b hb1 hb2
  obtain ⟨μ, hμ⟩ := isSquare_of_charTwo' l
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hμ
    exact hl hμ
  let dv : Fin ℓ ⊕ (Fin ℓ ⊕ Fin r) → K := fun k => match k with
    | .inl _ => μ⁻¹
    | .inr (.inl _) => μ
    | .inr (.inr _) => 1
  have hd0 : ∀ k, dv k ≠ 0 := by
    intro k
    rcases k with i | i | j
    · exact inv_ne_zero hμ0
    · exact hμ0
    · exact one_ne_zero
  set Dl : (ι → K) →ₗ[K] (ι → K) := b.constr K fun k => dv k • b k with hDl
  set Dl' : (ι → K) →ₗ[K] (ι → K) := b.constr K fun k => (dv k)⁻¹ • b k with hDl'
  have hDb : ∀ k, Dl (b k) = dv k • b k := fun k => by rw [hDl, Basis.constr_basis]
  have hDb' : ∀ k, Dl' (b k) = (dv k)⁻¹ • b k := fun k => by rw [hDl', Basis.constr_basis]
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
  refine ⟨D, ?_, ?_⟩
  · change (LinearMap.toMatrix' Dl).det = 1
    rw [LinearMap.det_toMatrix', ← LinearMap.det_toMatrix b Dl]
    have hdiag : LinearMap.toMatrix b b Dl = Matrix.diagonal dv := by
      ext i j
      rw [LinearMap.toMatrix_apply, hDb, map_smul, b.repr_self, Finsupp.smul_single,
        smul_eq_mul, mul_one, Finsupp.single_apply, Matrix.diagonal_apply]
      by_cases h : i = j
      · subst h
        simp
      · simp [h, Ne.symm h]
    rw [hdiag, Matrix.det_diagonal, Fintype.prod_sum_type, Fintype.prod_sum_type,
      ← mul_assoc, ← Finset.prod_mul_distrib]
    simp [dv, inv_mul_cancel₀ hμ0]
  · have hN' : N = LinearMap.toMatrix' Nl := by rw [hNl, LinearMap.toMatrix'_toLin']
    rw [hDinv, hN', ← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_comp, ← map_smul]
    congr 1
    refine b.ext fun k => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hDb', map_smul, map_smul,
      LinearMap.smul_apply]
    rcases k with i | k
    · rw [hb1, hDb, smul_smul]
      simp only [dv, inv_inv]
      rw [hμ]
    · rw [hb2, map_zero, smul_zero, smul_zero]

end Torus

section Commutant

variable {κ K : Type} [Fintype κ] [DecidableEq κ] [Field K]

theorem entries_of_commute_single {B : Matrix κ κ K} {k k' : κ}
    (h : B * Matrix.single k k' 1 = Matrix.single k k' 1 * B) :
    (∀ m, m ≠ k → B m k = 0) ∧ (∀ m', m' ≠ k' → B k' m' = 0) ∧ B k k = B k' k' := by
  refine ⟨fun m hm => ?_, fun m' hm' => ?_, ?_⟩
  · have h1 := congrFun (congrFun h m) k'
    rw [mul_single_apply_same, single_mul_apply_of_ne _ _ _ _ _ hm, mul_one] at h1
    exact h1
  · have h1 := congrFun (congrFun h k) m'
    rw [single_mul_apply_same, mul_single_apply_of_ne _ _ _ _ _ hm', one_mul] at h1
    exact h1.symm
  · have h1 := congrFun (congrFun h k) k'
    rw [mul_single_apply_same, single_mul_apply_same, mul_one, one_mul] at h1
    exact h1

end Commutant

section CommutantKappa

variable {K : Type} [Field K]

@[expose] def sqZeroStd (ℓ r : ℕ) : Matrix (Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) (Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) K :=
  Matrix.of fun m m' => Sum.elim (fun c => if m = .inr (.inl c) then 1 else 0) (fun _ => 0) m'

theorem sqZeroStd_apply {ℓ r : ℕ} (m m' : Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) :
    sqZeroStd (K := K) ℓ r m m' =
      Sum.elim (fun c => if m = .inr (.inl c) then 1 else 0) (fun _ => 0) m' := rfl

theorem commutant_kappa {ℓ r : ℕ} (hℓ0 : ℓ ≠ 0) (hcard : 3 ≤ 2 * ℓ + r)
    {B : Matrix (Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) (Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) K}
    (hBN : B * sqZeroStd ℓ r = sqZeroStd ℓ r * B)
    (hC1 : ∀ i j : Fin ℓ, i ≠ j →
      B * Matrix.single (.inr (.inl i)) (.inl j) 1 =
        Matrix.single (.inr (.inl i)) (.inl j) 1 * B)
    (hC2 : ∀ (k : Fin r) (j : Fin ℓ),
      B * Matrix.single (.inr (.inr k)) (.inl j) 1 =
        Matrix.single (.inr (.inr k)) (.inl j) 1 * B)
    (hC3 : ∀ (i : Fin ℓ) (k : Fin r),
      B * Matrix.single (.inr (.inl i)) (.inr (.inr k)) 1 =
        Matrix.single (.inr (.inl i)) (.inr (.inr k)) 1 * B)
    (hC4 : ∀ i j : Fin ℓ, i ≠ j →
      B * (Matrix.single (.inl i) (.inl j) 1 + Matrix.single (.inr (.inl i)) (.inr (.inl j)) 1) =
        (Matrix.single (.inl i) (.inl j) 1 +
          Matrix.single (.inr (.inl i)) (.inr (.inl j)) 1) * B) :
    ∃ c d : K, B = c • 1 + d • sqZeroStd ℓ r := by
  have hC0 : ∀ a : Fin ℓ, B (.inr (.inl a)) (.inr (.inl a)) = B (.inl a) (.inl a) := by
    intro a
    have h := congrFun (congrFun hBN (.inr (.inl a))) (.inl a)
    rw [Matrix.mul_apply, Matrix.mul_apply] at h
    rw [Fintype.sum_eq_single (.inr (.inl a)) (fun k hk => by
        rw [sqZeroStd_apply, Sum.elim_inl, ite_eq_right hk, mul_zero])] at h
    rw [Fintype.sum_eq_single (.inl a) (fun k hk => by
        rw [sqZeroStd_apply]
        rcases k with c | c
        · rw [Sum.elim_inl, ite_eq_right (by intro h'; apply hk; simpa [eq_comm] using h'),
            zero_mul]
        · rw [Sum.elim_inr, zero_mul])] at h
    simpa [sqZeroStd_apply] using h
  have hC4' : ∀ i j : Fin ℓ, i ≠ j → ∀ a : Fin ℓ,
      B (.inr (.inl a)) (.inl i) = if a = i then B (.inr (.inl j)) (.inl j) else 0 := by
    intro i j hij a
    have h := congrFun (congrFun (hC4 i j hij) (.inr (.inl a))) (.inl j)
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.add_apply, Matrix.add_apply,
      mul_single_apply_same, mul_single_apply_of_ne _ _ _ _ _ (by simp),
      single_mul_apply_of_ne _ _ _ _ _ (by simp), mul_one, add_zero, zero_add] at h
    by_cases ha : a = i
    · subst ha
      rw [single_mul_apply_same, one_mul] at h
      rw [ite_eq_left rfl, h]
    · rw [single_mul_apply_of_ne _ _ _ _ _ (by simpa using ha)] at h
      rw [ite_eq_right ha, h]
  have hℓ1 : 0 < ℓ := Nat.pos_of_ne_zero hℓ0
  set j₀ : Fin ℓ := ⟨0, hℓ1⟩ with hj₀
  have hother : 2 ≤ ℓ → ∀ i : Fin ℓ, ∃ j : Fin ℓ, j ≠ i := by
    intro h2 i
    by_cases hi : i.val = 0
    · exact ⟨⟨1, by omega⟩, fun h => by rw [← h] at hi; simp at hi⟩
    · exact ⟨⟨0, by omega⟩, fun h => hi (by rw [← h])⟩
  have hr0 : r = 0 → 2 ≤ ℓ := fun hr => by omega
  set lam := B (.inl j₀) (.inl j₀) with hlam
  set mu := B (.inr (.inl j₀)) (.inl j₀) with hmu
  have hRowX : ∀ (a : Fin ℓ) m', m' ≠ .inl a → B (.inl a) m' = 0 := by
    intro a m' hm'
    rcases Nat.eq_zero_or_pos r with hr | hr
    · obtain ⟨i, hi⟩ := hother (hr0 hr) a
      exact (entries_of_commute_single (hC1 i a hi)).2.1 m' hm'
    · exact (entries_of_commute_single (hC2 ⟨0, hr⟩ a)).2.1 m' hm'
  have hRowY : ∀ (k : Fin r) m', m' ≠ .inr (.inr k) → B (.inr (.inr k)) m' = 0 :=
    fun k m' hm' => (entries_of_commute_single (hC3 j₀ k)).2.1 m' hm'
  have hColW : ∀ (c : Fin ℓ) m, m ≠ .inr (.inl c) → B m (.inr (.inl c)) = 0 := by
    intro c m hm
    rcases Nat.eq_zero_or_pos r with hr | hr
    · obtain ⟨j, hj⟩ := hother (hr0 hr) c
      exact (entries_of_commute_single (hC1 c j (Ne.symm hj))).1 m hm
    · exact (entries_of_commute_single (hC3 c ⟨0, hr⟩)).1 m hm
  have hColY : ∀ (k : Fin r) m, m ≠ .inr (.inr k) → B m (.inr (.inr k)) = 0 :=
    fun k m hm => (entries_of_commute_single (hC2 k j₀)).1 m hm
  have hDiagX : ∀ a : Fin ℓ, B (.inl a) (.inl a) = lam := by
    intro a
    rcases Nat.eq_zero_or_pos r with hr | hr
    · by_cases ha : a = j₀
      · rw [ha]
      · have h1 := (entries_of_commute_single (hC1 j₀ a (Ne.symm ha))).2.2
        rw [← h1, hC0]
    · rw [← (entries_of_commute_single (hC2 ⟨0, hr⟩ a)).2.2,
        (entries_of_commute_single (hC2 ⟨0, hr⟩ j₀)).2.2]
  have hDiag : ∀ k, B k k = lam := by
    intro k
    rcases k with a | a | k
    · exact hDiagX a
    · rw [hC0]
      exact hDiagX a
    · rw [(entries_of_commute_single (hC2 k j₀)).2.2]
  have hBeta : ∀ a c : Fin ℓ, B (.inr (.inl a)) (.inl c) = if a = c then mu else 0 := by
    intro a c
    by_cases h2 : 2 ≤ ℓ
    · by_cases hc : c = j₀
      · rw [hc]
        by_cases ha : a = j₀
        · simp [ha, hmu]
        · obtain ⟨j, hj⟩ := hother h2 j₀
          rw [hC4' j₀ j (Ne.symm hj) a]
          simp [ha]
      · rw [hC4' c j₀ hc a]
    · have h1 : ∀ i : Fin ℓ, i = j₀ := fun i => Fin.ext (by omega)
      rw [h1 a, h1 c]
      simp [hmu]
  refine ⟨lam, mu, ?_⟩
  ext m m'
  rw [Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, sqZeroStd_apply, Matrix.one_apply,
    smul_eq_mul, smul_eq_mul]
  rcases m' with c | c | k
  · rw [Sum.elim_inl]
    rcases m with a | a | k
    · by_cases hac : a = c
      · subst hac
        simp [hDiagX]
      · rw [hRowX a _ (by simpa using Ne.symm hac)]
        simp [hac]
    · rw [hBeta]
      by_cases hac : a = c
      · subst hac
        simp
      · simp [hac]
    · rw [hRowY k _ (by simp)]
      simp
  · rw [Sum.elim_inr, mul_zero, add_zero]
    by_cases hm : m = .inr (.inl c)
    · subst hm
      rw [hDiag, ite_eq_left rfl, mul_one]
    · rw [hColW c m hm, ite_eq_right hm, mul_zero]
  · rw [Sum.elim_inr, mul_zero, add_zero]
    by_cases hm : m = .inr (.inr k)
    · subst hm
      rw [hDiag, ite_eq_left rfl, mul_one]
    · rw [hColY k m hm, ite_eq_right hm, mul_zero]

end CommutantKappa

section CommutantSq

variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]

theorem commutant_of_sq_eq_zero {N X : Matrix ι ι K} (hN : N * N = 0) (hN0 : N ≠ 0)
    (h3 : 3 ≤ Fintype.card ι) (hXN : X * N = N * X)
    (hD : ∀ (a : ι → K) (α : (ι → K) →ₗ[K] K), α a = 0 → α (N *ᵥ a) = 0 →
      X * (LinearMap.toMatrix' (α.smulRight a) * N + N * LinearMap.toMatrix' (α.smulRight a)) =
        (LinearMap.toMatrix' (α.smulRight a) * N + N * LinearMap.toMatrix' (α.smulRight a)) * X) :
    ∃ c d : K, X = c • 1 + d • N := by
  classical
  set Nl := Matrix.toLin' N with hNl
  have hNl2 : Nl ∘ₗ Nl = 0 := by rw [hNl, ← Matrix.toLin'_mul, hN, map_zero]
  obtain ⟨r, b, hb1, hb2⟩ := exists_basis_sq_eq_zero Nl hNl2
  have hcard : Fintype.card ι = 2 * finrank K (LinearMap.range Nl) + r := by
    have h := Module.finrank_eq_card_basis b
    rw [Module.finrank_fintype_fun_eq_card] at h
    simp only [Fintype.card_sum, Fintype.card_fin] at h
    omega
  have hℓ0 : finrank K (LinearMap.range Nl) ≠ 0 := by
    intro h
    apply hN0
    rw [Submodule.finrank_eq_zero, LinearMap.range_eq_bot] at h
    rw [← LinearMap.toMatrix'_toLin' N, ← hNl, h, map_zero]
  generalize finrank K (LinearMap.range Nl) = ℓ at b hb1 hb2 hcard hℓ0
  let φ : Matrix ι ι K ≃ₐ[K] Matrix (Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) (Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) K :=
    Matrix.toLinAlgEquiv'.trans (LinearMap.toMatrixAlgEquiv b)
  have hφ : ∀ (Y : Matrix ι ι K) (m m' : Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)),
      φ Y m m' = b.coord m (Y *ᵥ b m') := fun Y m m' => by
    simp only [φ, AlgEquiv.trans_apply, LinearMap.toMatrixAlgEquiv_apply,
      Matrix.toLinAlgEquiv'_apply, Basis.coord_apply]
  have hcoord : ∀ k k' : Fin ℓ ⊕ (Fin ℓ ⊕ Fin r), b.coord k (b k') = if k' = k then 1 else 0 :=
    fun k k' => by rw [Basis.coord_apply, Basis.repr_self, Finsupp.single_apply]
  have hNv : ∀ v, N *ᵥ v = Nl v := fun v => by rw [hNl, Matrix.toLin'_apply]
  set B := φ X with hB
  have hS : ∀ k k' : Fin ℓ ⊕ (Fin ℓ ⊕ Fin r), b.coord k' (b k) = 0 →
      b.coord k' (Nl (b k)) = 0 → ∀ S, (∀ m m', S m m' =
        b.coord k' (Nl (b m')) * (if k = m then 1 else 0) +
          b.coord k' (b m') * b.coord m (Nl (b k))) → B * S = S * B := by
    intro k k' h1 h2 S hSe
    have hSφ : S = φ (LinearMap.toMatrix' ((b.coord k').smulRight (b k)) * N +
        N * LinearMap.toMatrix' ((b.coord k').smulRight (b k))) := by
      ext m m'
      rw [hSe, hφ, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        LinearMap.toMatrix'_mulVec, LinearMap.toMatrix'_mulVec, LinearMap.smulRight_apply,
        LinearMap.smulRight_apply, Matrix.mulVec_smul, map_add, map_smul, map_smul, hNv, hNv,
        hcoord, hcoord m k, smul_eq_mul, smul_eq_mul]
    rw [hSφ, hB, ← map_mul, ← map_mul, hD (b k) (b.coord k') h1 (by rwa [hNv])]
  have hNb : ∀ m m', φ N m m' = b.coord m (Nl (b m')) := fun m m' => by rw [hφ, hNv]
  have hBN : B * φ N = φ N * B := by rw [hB, ← map_mul, ← map_mul, hXN]
  have hC1 : ∀ i j : Fin ℓ, i ≠ j →
      B * Matrix.single (.inr (.inl i)) (.inl j) 1 =
        Matrix.single (.inr (.inl i)) (.inl j) 1 * B := by
    intro i j hij
    refine hS (.inr (.inl i)) (.inr (.inl j)) (by rw [hcoord]; simp [hij])
      (by rw [hb2, map_zero]) _ fun m m' => ?_
    rw [hb2, map_zero, mul_zero, add_zero, Matrix.single_apply]
    rcases m' with c | c
    · rw [hb1, hcoord]
      by_cases hc : c = j
      · subst hc
        simp
      · simp [hc, Ne.symm hc]
    · simp [hb2]
  have hC2 : ∀ (k : Fin r) (j : Fin ℓ),
      B * Matrix.single (.inr (.inr k)) (.inl j) 1 =
        Matrix.single (.inr (.inr k)) (.inl j) 1 * B := by
    intro k j
    refine hS (.inr (.inr k)) (.inr (.inl j)) (by rw [hcoord]; simp)
      (by rw [hb2, map_zero]) _ fun m m' => ?_
    rw [hb2, map_zero, mul_zero, add_zero, Matrix.single_apply]
    rcases m' with c | c
    · rw [hb1, hcoord]
      by_cases hc : c = j
      · subst hc
        simp
      · simp [hc, Ne.symm hc]
    · simp [hb2]
  have hC3 : ∀ (i : Fin ℓ) (k : Fin r),
      B * Matrix.single (.inr (.inl i)) (.inr (.inr k)) 1 =
        Matrix.single (.inr (.inl i)) (.inr (.inr k)) 1 * B := by
    intro i k
    refine hS (.inl i) (.inr (.inr k)) (by rw [hcoord]; simp)
      (by rw [hb1, hcoord]; simp) _ fun m m' => ?_
    rw [hb1, hcoord m, Matrix.single_apply]
    rcases m' with c | c
    · rw [hb1, hcoord, hcoord]
      simp
    · rw [hb2, map_zero, zero_mul, zero_add, hcoord]
      by_cases hc : c = .inr k
      · subst hc
        by_cases hm : m = .inr (.inl i)
        · subst hm
          simp
        · simp [Ne.symm hm]
      · simp [hc, Ne.symm hc]
  have hC4 : ∀ i j : Fin ℓ, i ≠ j →
      B * (Matrix.single (.inl i) (.inl j) 1 + Matrix.single (.inr (.inl i)) (.inr (.inl j)) 1) =
        (Matrix.single (.inl i) (.inl j) 1 +
          Matrix.single (.inr (.inl i)) (.inr (.inl j)) 1) * B := by
    intro i j hij
    refine hS (.inl i) (.inr (.inl j)) (by rw [hcoord]; simp)
      (by rw [hb1, hcoord]; simp [hij]) _ fun m m' => ?_
    rw [hb1, hcoord m, Matrix.add_apply, Matrix.single_apply, Matrix.single_apply]
    rcases m' with c | c | c
    · rw [hb1, hcoord, hcoord]
      by_cases hc : c = j
      · subst hc
        simp
      · simp [hc, Ne.symm hc]
    · rw [hb2, map_zero, zero_mul, zero_add, hcoord]
      by_cases hc : c = j
      · subst hc
        by_cases hm : m = .inr (.inl i)
        · subst hm
          simp
        · simp [Ne.symm hm]
      · simp [hc, Ne.symm hc]
    · rw [hb2, map_zero, zero_mul, zero_add, hcoord]
      simp
  have hNstd : φ N = sqZeroStd ℓ r := by
    ext m m'
    rw [hNb, sqZeroStd_apply]
    rcases m' with c | c
    · rw [hb1, hcoord]
      simp [eq_comm]
    · rw [hb2, map_zero]
      rfl
  obtain ⟨c, d, hcd⟩ := commutant_kappa hℓ0 (by omega) (by rw [← hNstd]; exact hBN)
    hC1 hC2 hC3 hC4
  refine ⟨c, d, φ.injective ?_⟩
  rw [← hB, hcd, map_add, map_smul, map_smul, map_one, hNstd]

end CommutantSq

section Transvection

variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] [CharP K 2]

theorem conj_unipGL_eq {M : GL ι K}
    (hE : ((M : Matrix ι ι K) - 1) * ((M : Matrix ι ι K) - 1) = 0)
    {a : ι → K} {α : (ι → K) →ₗ[K] K} (h1 : α a = 0)
    (h2 : α (((M : Matrix ι ι K) - 1) *ᵥ a) = 0) :
    ∃ hEE : LinearMap.toMatrix' (α.smulRight a) * LinearMap.toMatrix' (α.smulRight a) = 0,
      ((unipGL _ hEE 1 * M * (unipGL _ hEE 1)⁻¹ : GL ι K) : Matrix ι ι K) =
        (M : Matrix ι ι K) + (LinearMap.toMatrix' (α.smulRight a) * ((M : Matrix ι ι K) - 1) +
          ((M : Matrix ι ι K) - 1) * LinearMap.toMatrix' (α.smulRight a)) ∧
      unipGL _ hEE 1 * M * (unipGL _ hEE 1)⁻¹ * M =
        M * (unipGL _ hEE 1 * M * (unipGL _ hEE 1)⁻¹) := by
  set N := (M : Matrix ι ι K) - 1 with hNdef
  set E := LinearMap.toMatrix' (α.smulRight a) with hEdef
  have hEv : ∀ v, E *ᵥ v = α v • a := fun v => by
    rw [hEdef, LinearMap.toMatrix'_mulVec, LinearMap.smulRight_apply]
  have hEE : E * E = 0 := Matrix.ext_iff_mulVec.mpr fun v => by
    rw [← Matrix.mulVec_mulVec, hEv, hEv, map_smul, h1, smul_zero, zero_smul,
      Matrix.zero_mulVec]
  have hENE : E * N * E = 0 := Matrix.ext_iff_mulVec.mpr fun v => by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hEv, hEv, Matrix.mulVec_smul, map_smul,
      h2, smul_zero, zero_smul, Matrix.zero_mulVec]
  have hMN : (M : Matrix ι ι K) = 1 + N := by rw [hNdef, add_sub_cancel]
  have hneg : -(N * E) = N * E := neg_eq_of_add_eq_zero_right (matrix_add_self (N * E))
  have hconj : ((unipGL E hEE 1 * M * (unipGL E hEE 1)⁻¹ : GL ι K) : Matrix ι ι K) =
      (M : Matrix ι ι K) + (E * N + N * E) := by
    rw [Units.val_mul, Units.val_mul, coe_unipGL, one_smul]
    have hinv : (((unipGL E hEE 1)⁻¹ : GL ι K) : Matrix ι ι K) = 1 - E := by
      simp [unipGL]
    rw [hinv, hMN]
    calc (1 + E) * (1 + N) * (1 - E) = 1 + N + (E * N + -(N * E)) - E * E - E * N * E := by
          noncomm_ring
      _ = 1 + N + (E * N + N * E) := by rw [hEE, hENE, hneg, sub_zero, sub_zero]
  refine ⟨hEE, hconj, Units.ext ?_⟩
  rw [Units.val_mul (unipGL E hEE 1 * M * (unipGL E hEE 1)⁻¹) M,
    Units.val_mul M (unipGL E hEE 1 * M * (unipGL E hEE 1)⁻¹), hconj, hMN]
  have hNNE : N * (N * E) = 0 := by rw [← Matrix.mul_assoc, hE, Matrix.zero_mul]
  simp only [add_mul, mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc, hE, hNNE,
    Matrix.mul_zero, add_zero]
  abel

end Transvection

section Linear

variable {G : Type} [Group G] [Finite G] {A : Subgroup G}

theorem autAlpha_linear : AutAlpha .linear := by
  intro G _ _ A D hD _ hZ _ p hp
  cases D with
  | linear n m hn hm hnm K hK e =>
    have := charP_two_of_card hK
    obtain ⟨ℓ, -, M, hpM, hM2, -⟩ := hp
    have hMsq : M ^ 2 = 1 := by rw [← hM2]; exact pow_orderOf_eq_one M
    have hE := sub_one_mul_self hMsq
    have hSL : ∀ X : GL (Fin n) K, (X : Matrix (Fin n) (Fin n) K).det = 1 →
        X ∈ StatedSL n K := fun X hX => subset_closure hX
    obtain ⟨φ, hinj, hrange, hφ⟩ := exists_alphaHom hZ hpM hM2 hE
      (fun a => hSL _ (det_unipGL hE a))
    have h := regularOn_autCyclic_alpha_of (ιF := RingHom.id K) hZ hM2 hinj hrange hφ
      fun l hl => by
        obtain ⟨d, hd1, hd⟩ := exists_det_one_conj_eq_smul _ hE hl
        exact ⟨d, hSL d hd1, hd⟩
    show RegularOn A (alphaGroup e p) (nonidentity (alphaGroup e p)) ∧
      AutCyclic A (alphaGroup e p) (2 ^ m - 1)
    rwa [← hK]
  | unitary => simp [ClassicalModel.family] at hD
  | symplectic => simp [ClassicalModel.family] at hD
  | orthPlus => simp [ClassicalModel.family] at hD
  | orthMinus => simp [ClassicalModel.family] at hD

omit [Finite G] in
theorem deltaCentral_alpha_linear (D : ClassicalModel A) (hD : D.family = .linear)
    (hZ : Odd (Nat.card (center ↥A))) {p : G} (hp : D.IsAlphaClass p) :
    DeltaCentral A p (D.alpha p) := by
  cases D with
  | linear n m hn hm hnm K hK e =>
    have := charP_two_of_card hK
    obtain ⟨ℓ, hp2, M, hpM, hM2, -⟩ := hp
    have hp2' : p ^ 2 = 1 := by rw [← hp2]; exact pow_orderOf_eq_one p
    have hMsq : M ^ 2 = 1 := by rw [← hM2]; exact pow_orderOf_eq_one M
    have hE := sub_one_mul_self hMsq
    have hM1 : M ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hM2
      omega
    have hN0 := sub_one_ne_zero hM1
    have hSL : ∀ X : GL (Fin n) K, (X : Matrix (Fin n) (Fin n) K).det = 1 →
        X ∈ StatedSL n K := fun X hX => subset_closure hX
    show DeltaCentral A p (alphaGroup e p)
    refine deltaCentral_alpha_of hZ hp2' hpM hM2 fun X _ hXM hXg => ?_
    set N := (M : Matrix (Fin n) (Fin n) K) - 1 with hNdef
    have hXM' : (X : Matrix (Fin n) (Fin n) K) * M = M * X := by
      rw [← Units.val_mul, hXM, Units.val_mul]
    have hXN : (X : Matrix (Fin n) (Fin n) K) * N = N * X := by
      rw [hNdef, mul_sub, sub_mul, hXM', mul_one, one_mul]
    have hD : ∀ (a : Fin n → K) (α : (Fin n → K) →ₗ[K] K), α a = 0 → α (N *ᵥ a) = 0 →
        (X : Matrix (Fin n) (Fin n) K) * (LinearMap.toMatrix' (α.smulRight a) * N +
          N * LinearMap.toMatrix' (α.smulRight a)) =
        (LinearMap.toMatrix' (α.smulRight a) * N + N * LinearMap.toMatrix' (α.smulRight a)) *
          X := by
      intro a α h1 h2
      obtain ⟨hEE, hconj, hcomm⟩ := conj_unipGL_eq hE h1 h2
      have h := congrArg (fun Y : GL (Fin n) K => (Y : Matrix (Fin n) (Fin n) K))
        (hXg _ (hSL _ (det_unipGL hEE 1)) hcomm)
      simp only [Units.val_mul] at h
      rw [← Units.val_mul (unipGL _ hEE 1) M, ← Units.val_mul (unipGL _ hEE 1 * M), hconj,
        Matrix.mul_add, Matrix.add_mul, hXM'] at h
      exact add_left_cancel h
    obtain ⟨c, d, hcd⟩ := commutant_of_sq_eq_zero hE hN0 (by simp; omega) hXN hD
    have hc0 : c ≠ 0 := by
      rintro rfl
      have hXX : (X : Matrix (Fin n) (Fin n) K) * X = 0 := by
        rw [hcd, zero_smul, zero_add, smul_mul_smul_comm, hE, smul_zero]
      have hu : IsUnit ((X : Matrix (Fin n) (Fin n) K) * X) :=
        (Units.isUnit X).mul (Units.isUnit X)
      rw [hXX] at hu
      have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
      exact not_isUnit_zero hu
    refine ⟨unipGL N hE (d / c), hSL _ (det_unipGL hE _), ⟨Units.mk0 c hc0, Units.ext ?_⟩,
      d / c, by rw [coe_unipGL, add_sub_cancel_left]⟩
    rw [hcd, Units.val_mul, coe_unipGL, Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0,
      Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, add_mul, Matrix.one_mul,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, smul_smul]
    have hcd' : c * (d / c) = d := by field_simp
    rw [hcd']
  | unitary => simp [ClassicalModel.family] at hD
  | symplectic => simp [ClassicalModel.family] at hD
  | orthPlus => simp [ClassicalModel.family] at hD
  | orthMinus => simp [ClassicalModel.family] at hD

theorem deltaAlpha_linear : DeltaAlpha .linear := fun _ _ _ _ D hD _ hZ _ _ hp =>
  deltaCentral_alpha_linear D hD hZ hp

end Linear

end CFSG.ComponentClassification.RankTwoClassical
