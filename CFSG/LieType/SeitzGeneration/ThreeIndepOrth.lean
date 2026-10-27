module

public import CFSG.LieType.SeitzGeneration.ThreeIndepOrthBlock
public import CFSG.LieType.SeitzGeneration.InnerOrthogonal

public section

namespace CFSG.LieType.SeitzGeneration

open Module QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne.CTP CFSG.Open
open CFSG.RankThree.Classical2 (orthDerived)

section M2

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  (P P' : HypPair Q)

@[expose] def m2Emb : Matrix (Fin 2) (Fin 2) K →ₗ[K] V where
  toFun X := (X 0 0 • P.e + X 1 1 • P.f) + (X 0 1 • (-P'.e) + X 1 0 • P'.f)
  map_add' X Y := by simp only [Matrix.add_apply, add_smul]; abel
  map_smul' c X := by
    simp only [Matrix.smul_apply, smul_eq_mul, RingHom.id_apply, smul_add, smul_smul]

@[expose] def m2Proj : V →ₗ[K] Matrix (Fin 2) (Fin 2) K where
  toFun v := !![polar Q v P.f, -polar Q v P'.f; polar Q v P'.e, polar Q v P.e]
  map_add' v w := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [QuadraticMap.polar_add_left, neg_add_rev, add_comm]
  map_smul' c v := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [QuadraticMap.polar_smul_left]

variable {P P'}

theorem m2Proj_emb (h : P.Orth P') (X : Matrix (Fin 2) (Fin 2) K) :
    m2Proj P P' (m2Emb P P' X) = X := by
  have h1 : polar Q P.e P'.e = 0 := h.ee
  have h2 : polar Q P.e P'.f = 0 := h.ef
  have h3 : polar Q P.f P'.e = 0 := h.fe
  have h4 : polar Q P.f P'.f = 0 := h.ff
  have h1' : polar Q P'.e P.e = 0 := by rw [polar_comm]; exact h1
  have h2' : polar Q P'.f P.e = 0 := by rw [polar_comm]; exact h2
  have h3' : polar Q P'.e P.f = 0 := by rw [polar_comm]; exact h3
  have h4' : polar Q P'.f P.f = 0 := by rw [polar_comm]; exact h4
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [m2Proj, m2Emb, QuadraticMap.polar_add_left, QuadraticMap.polar_smul_left, h1, h2, h3, h4,
      h1', h2', h3', h4', P.Q_e, P.Q_f, P'.Q_e, P'.Q_f, P.polar_ef, P.polar_fe, P'.polar_ef,
      P'.polar_fe]

theorem Q_pair (R : HypPair Q) (a b : K) : Q (a • R.e + b • R.f) = a * b := by
  rw [QuadraticMap.map_add Q, QuadraticMap.map_smul, QuadraticMap.map_smul, R.Q_e, R.Q_f,
    QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right, R.polar_ef]
  simp

theorem polar_pairs (h : P.Orth P') (a b c d : K) :
    polar Q (a • P.e + b • P.f) (c • P'.e + d • P'.f) = 0 := by
  have h1 : polar Q P.e P'.e = 0 := h.ee
  have h2 : polar Q P.e P'.f = 0 := h.ef
  have h3 : polar Q P.f P'.e = 0 := h.fe
  have h4 : polar Q P.f P'.f = 0 := h.ff
  simp [QuadraticMap.polar_add_left, QuadraticMap.polar_add_right, QuadraticMap.polar_smul_left,
    QuadraticMap.polar_smul_right, h1, h2, h3, h4]

theorem Q_m2Emb (h : P.Orth P') (X : Matrix (Fin 2) (Fin 2) K) :
    Q (m2Emb P P' X) = X.det := by
  have e1 : X 0 1 • (-P'.e) + X 1 0 • P'.f = (-X 0 1) • P'.e + X 1 0 • P'.f := by
    rw [smul_neg, neg_smul]
  change Q ((X 0 0 • P.e + X 1 1 • P.f) + (X 0 1 • (-P'.e) + X 1 0 • P'.f)) = _
  rw [e1, QuadraticMap.map_add Q, Q_pair P, Q_pair P', polar_pairs h, Matrix.det_fin_two]
  ring

theorem polar_m2Emb_of_proj_zero {v : V} (hv : m2Proj P P' v = 0) (X : Matrix (Fin 2) (Fin 2) K) :
    polar Q v (m2Emb P P' X) = 0 := by
  have e00 := congrFun (congrFun hv 0) 0
  have e01 := congrFun (congrFun hv 0) 1
  have e10 := congrFun (congrFun hv 1) 0
  have e11 := congrFun (congrFun hv 1) 1
  simp [m2Proj] at e00 e01 e10 e11
  simp [m2Emb, QuadraticMap.polar_add_right, QuadraticMap.polar_smul_right,
    QuadraticMap.polar_neg_right, e00, e01, e10, e11]

@[expose] def m2Block (h : P.Orth P') : QBlock Q (Matrix (Fin 2) (Fin 2) K) where
  ι := m2Emb P P'
  m := m2Proj P P'
  qM := Matrix.det
  m_ι := m2Proj_emb h
  Q_add v y hv := by
    rw [QuadraticMap.map_add Q, Q_m2Emb h, polar_m2Emb_of_proj_zero hv]
    ring

theorem m2Proj_m2Emb_of_orth {R R' : HypPair Q} (h0 : P.Orth R) (h1 : P.Orth R') (h2 : P'.Orth R)
    (h3 : P'.Orth R') (X : Matrix (Fin 2) (Fin 2) K) : m2Proj R R' (m2Emb P P' X) = 0 := by
  have a1 : polar Q P.e R.e = 0 := h0.ee
  have a2 : polar Q P.e R.f = 0 := h0.ef
  have a3 : polar Q P.f R.e = 0 := h0.fe
  have a4 : polar Q P.f R.f = 0 := h0.ff
  have b1 : polar Q P.e R'.e = 0 := h1.ee
  have b2 : polar Q P.e R'.f = 0 := h1.ef
  have b3 : polar Q P.f R'.e = 0 := h1.fe
  have b4 : polar Q P.f R'.f = 0 := h1.ff
  have c1 : polar Q P'.e R.e = 0 := h2.ee
  have c2 : polar Q P'.e R.f = 0 := h2.ef
  have c3 : polar Q P'.f R.e = 0 := h2.fe
  have c4 : polar Q P'.f R.f = 0 := h2.ff
  have d1 : polar Q P'.e R'.e = 0 := h3.ee
  have d2 : polar Q P'.e R'.f = 0 := h3.ef
  have d3 : polar Q P'.f R'.e = 0 := h3.fe
  have d4 : polar Q P'.f R'.f = 0 := h3.ff
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [m2Proj, m2Emb, QuadraticMap.polar_add_left, QuadraticMap.polar_smul_left,
      QuadraticMap.polar_neg_left, a1, a2, a3, a4, b1, b2, b3, b4, c1, c2, c3, c4, d1, d2, d3, d4]

end M2

section Alg

variable {K : Type} [Field K]

@[expose] def cubeA : Matrix (Fin 2) (Fin 2) K := !![0, -1; 1, -1]

theorem cubeA_sq : (cubeA : Matrix (Fin 2) (Fin 2) K) * cubeA = !![-1, 1; -1, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [cubeA, Matrix.mul_apply, Fin.sum_univ_two]

theorem cubeA_cube : (cubeA : Matrix (Fin 2) (Fin 2) K) * cubeA * cubeA = 1 := by
  rw [cubeA_sq]
  ext i j; fin_cases i <;> fin_cases j <;> simp [cubeA, Matrix.mul_apply, Fin.sum_univ_two]

theorem det_cubeA : (cubeA : Matrix (Fin 2) (Fin 2) K).det = 1 := by
  simp [cubeA, Matrix.det_fin_two]

theorem cubeA_indep (a b : ℕ) (ha : a < 3) (hb : b < 3)
    (h : ∀ X : Matrix (Fin 2) (Fin 2) K, cubeA ^ a * (X * cubeA ^ b) = X) : a = 0 ∧ b = 0 := by
  have h1 := h 1
  have h2 := h !![1, 0; 0, 0]
  interval_cases a <;> interval_cases b <;> first | exact ⟨rfl, rfl⟩ | skip
  all_goals simp [pow_succ, cubeA] at h1 h2

@[expose] def leftA : Module.End K (Matrix (Fin 2) (Fin 2) K) := LinearMap.mulLeft K cubeA

@[expose] def rightA : Module.End K (Matrix (Fin 2) (Fin 2) K) := LinearMap.mulRight K cubeA

theorem leftA_apply (X : Matrix (Fin 2) (Fin 2) K) : leftA X = cubeA * X := rfl

theorem rightA_apply (X : Matrix (Fin 2) (Fin 2) K) : rightA X = X * cubeA := rfl

theorem leftA_pow_apply (a : ℕ) (X : Matrix (Fin 2) (Fin 2) K) :
    (leftA ^ a) X = cubeA ^ a * X := by
  rw [leftA, LinearMap.pow_mulLeft, LinearMap.mulLeft_apply]

theorem rightA_pow_apply (b : ℕ) (X : Matrix (Fin 2) (Fin 2) K) :
    (rightA ^ b) X = X * cubeA ^ b := by
  rw [rightA, LinearMap.pow_mulRight, LinearMap.mulRight_apply]

theorem leftA_cube : leftA ∘ₗ leftA ∘ₗ leftA = (LinearMap.id : Module.End K _) := by
  refine LinearMap.ext fun X => ?_
  simp only [LinearMap.comp_apply, leftA_apply, LinearMap.id_apply]
  rw [← mul_assoc, ← mul_assoc, cubeA_cube, one_mul]

theorem rightA_cube : rightA ∘ₗ rightA ∘ₗ rightA = (LinearMap.id : Module.End K _) := by
  refine LinearMap.ext fun X => ?_
  have h : (cubeA : Matrix (Fin 2) (Fin 2) K) * (cubeA * cubeA) = 1 := by
    rw [← mul_assoc]
    exact cubeA_cube
  simp only [LinearMap.comp_apply, rightA_apply, LinearMap.id_apply, mul_assoc, h, mul_one]

theorem leftA_rightA : leftA ∘ₗ rightA = rightA ∘ₗ (leftA : Module.End K _) := by
  refine LinearMap.ext fun X => ?_
  simp only [LinearMap.comp_apply, leftA_apply, rightA_apply, mul_assoc]

theorem det_leftA (X : Matrix (Fin 2) (Fin 2) K) : (leftA X).det = X.det := by
  rw [leftA_apply, Matrix.det_mul, det_cubeA, one_mul]

theorem det_rightA (X : Matrix (Fin 2) (Fin 2) K) : (rightA X).det = X.det := by
  rw [rightA_apply, Matrix.det_mul, det_cubeA, mul_one]

theorem leftA_rightA_indep (a b : ℕ) (ha : a < 3) (hb : b < 3)
    (h : (leftA : Module.End K _) ^ a * rightA ^ b = 1) : a = 0 ∧ b = 0 :=
  cubeA_indep a b ha hb fun X => by
    have := LinearMap.congr_fun h X
    simpa [Module.End.mul_apply, leftA_pow_apply, rightA_pow_apply] using this

theorem leftA_indep (c : ℕ) (hc : c < 3) (h : (leftA : Module.End K _) ^ c = 1) : c = 0 :=
  (cubeA_indep c 0 hc (by norm_num) fun X => by
    have := LinearMap.congr_fun h X
    simpa [leftA_pow_apply] using this).1

end Alg

section Rank3

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {P P' : HypPair Q} {M₂ : Type} [AddCommGroup M₂] [Module K M₂]

theorem not_rankLE2_of_m2Block (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ x ∈ U, Q x = 0) (h : P.Orth P')
    (B₂ : QBlock Q M₂) (h12 : ∀ y, m2Proj P P' (B₂.ι y) = 0)
    (h21 : ∀ X, B₂.m (m2Emb P P' X) = 0) (T : M₂ →ₗ[K] M₂) (hTq : ∀ y, B₂.qM (T y) = B₂.qM y)
    (hT3 : T ∘ₗ T ∘ₗ T = LinearMap.id) (hind2 : ∀ c : ℕ, c < 3 → T ^ c = 1 → c = 0) :
    ¬ RankLE2 3 (orthDerived Q) :=
  not_rankLE2_orthDerived_of_blocks hQ hT (m2Block h) B₂ h12 h21 leftA rightA T
    (fun X => det_leftA X) (fun X => det_rightA X) hTq leftA_cube rightA_cube hT3 leftA_rightA
    (fun a b ha hb hab => leftA_rightA_indep a b ha hb hab) hind2

end Rank3

section Plus

variable {n : ℕ} {K : Type} [Field K] [Finite K]

theorem not_rankLE2_orthDerived_plus (hn : 4 ≤ n) : ¬ RankLE2 3 (orthDerived (quadPlus n K)) := by
  obtain ⟨hnd, hT⟩ := regular_quadPlus (K := K) (n := n) (by omega)
  have p01 : (plusPair K (⟨0, by omega⟩ : Fin n)).Orth (plusPair K ⟨1, by omega⟩) :=
    plusPair_orth (by simp [Fin.ext_iff])
  have p23 : (plusPair K (⟨2, by omega⟩ : Fin n)).Orth (plusPair K ⟨3, by omega⟩) :=
    plusPair_orth (by simp [Fin.ext_iff])
  have p20 : (plusPair K (⟨2, by omega⟩ : Fin n)).Orth (plusPair K ⟨0, by omega⟩) :=
    plusPair_orth (by simp [Fin.ext_iff])
  have p21 : (plusPair K (⟨2, by omega⟩ : Fin n)).Orth (plusPair K ⟨1, by omega⟩) :=
    plusPair_orth (by simp [Fin.ext_iff])
  have p30 : (plusPair K (⟨3, by omega⟩ : Fin n)).Orth (plusPair K ⟨0, by omega⟩) :=
    plusPair_orth (by simp [Fin.ext_iff])
  have p31 : (plusPair K (⟨3, by omega⟩ : Fin n)).Orth (plusPair K ⟨1, by omega⟩) :=
    plusPair_orth (by simp [Fin.ext_iff])
  have p02 : (plusPair K (⟨0, by omega⟩ : Fin n)).Orth (plusPair K ⟨2, by omega⟩) :=
    plusPair_orth (by simp [Fin.ext_iff])
  have p03 : (plusPair K (⟨0, by omega⟩ : Fin n)).Orth (plusPair K ⟨3, by omega⟩) :=
    plusPair_orth (by simp [Fin.ext_iff])
  have p12 : (plusPair K (⟨1, by omega⟩ : Fin n)).Orth (plusPair K ⟨2, by omega⟩) :=
    plusPair_orth (by simp [Fin.ext_iff])
  have p13 : (plusPair K (⟨1, by omega⟩ : Fin n)).Orth (plusPair K ⟨3, by omega⟩) :=
    plusPair_orth (by simp [Fin.ext_iff])
  exact not_rankLE2_of_m2Block hnd hT p01 (m2Block p23)
    (fun y => m2Proj_m2Emb_of_orth p20 p21 p30 p31 y)
    (fun X => m2Proj_m2Emb_of_orth p02 p03 p12 p13 X) leftA (fun X => det_leftA X) leftA_cube
    (fun c hc h => leftA_indep c hc h)

end Plus

section Odd

variable {n : ℕ} {K : Type} [Field K] (j : Fin n)

@[expose] def oddEmb : (Fin 3 → K) →ₗ[K] (Fin n ⊕ Fin n ⊕ Unit → K) where
  toFun x := x 0 • Pi.single (Sum.inl j) 1 + x 1 • Pi.single (Sum.inr (Sum.inl j)) 1 +
    x 2 • Pi.single (Sum.inr (Sum.inr ())) 1
  map_add' x y := by simp only [Pi.add_apply, add_smul]; abel
  map_smul' c x := by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, smul_add, smul_smul]

@[expose] def oddProj : (Fin n ⊕ Fin n ⊕ Unit → K) →ₗ[K] (Fin 3 → K) where
  toFun v := ![v (Sum.inl j), v (Sum.inr (Sum.inl j)), v (Sum.inr (Sum.inr ()))]
  map_add' v w := by ext i; fin_cases i <;> simp
  map_smul' c v := by ext i; fin_cases i <;> simp

theorem oddProj_emb (x : Fin 3 → K) : oddProj j (oddEmb j x) = x := by
  ext i; fin_cases i <;> simp [oddProj, oddEmb]

theorem oddEmb_inl (y : Fin 3 → K) (i : Fin n) :
    oddEmb j y (Sum.inl i) = if i = j then y 0 else 0 := by
  by_cases h : i = j <;> simp [oddEmb, h]

theorem oddEmb_inr_inl (y : Fin 3 → K) (i : Fin n) :
    oddEmb j y (Sum.inr (Sum.inl i)) = if i = j then y 1 else 0 := by
  by_cases h : i = j <;> simp [oddEmb, h]

theorem oddEmb_z (y : Fin 3 → K) : oddEmb j y (Sum.inr (Sum.inr ())) = y 2 := by
  simp [oddEmb]

theorem Q_odd_add (v : Fin n ⊕ Fin n ⊕ Unit → K) (y : Fin 3 → K) (hv : oddProj j v = 0) :
    quadOdd n K (v + oddEmb j y) = quadOdd n K v + (y 0 * y 1 + y 2 ^ 2) := by
  have e0 := congrFun hv 0
  have e1 := congrFun hv 1
  have e2 := congrFun hv 2
  simp [oddProj] at e0 e1 e2
  rw [quadOdd_apply, quadOdd_apply]
  have hterm : ∀ i : Fin n,
      (v + oddEmb j y) (Sum.inl i) * (v + oddEmb j y) (Sum.inr (Sum.inl i)) =
        v (Sum.inl i) * v (Sum.inr (Sum.inl i)) + if i = j then y 0 * y 1 else 0 := by
    intro i
    by_cases hij : i = j
    · subst hij
      simp [oddEmb_inl, oddEmb_inr_inl, e0, e1]
    · simp [oddEmb_inl, oddEmb_inr_inl, hij]
  rw [Finset.sum_congr rfl fun i _ => hterm i]
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true, Pi.add_apply,
    oddEmb_z, e2, zero_add]
  ring

@[expose] def oddBlock : QBlock (quadOdd n K) (Fin 3 → K) where
  ι := oddEmb j
  m := oddProj j
  qM x := x 0 * x 1 + x 2 ^ 2
  m_ι := oddProj_emb j
  Q_add v y hv := Q_odd_add j v y hv

@[expose] def slT : (Fin 3 → K) →ₗ[K] (Fin 3 → K) where
  toFun x := ![-x 1, x 1 - x 0 - 2 * x 2, x 1 - x 2]
  map_add' x y := by ext i; fin_cases i <;> simp <;> ring
  map_smul' c x := by ext i; fin_cases i <;> simp <;> ring

theorem slT_isom (x : Fin 3 → K) : slT x 0 * slT x 1 + slT x 2 ^ 2 = x 0 * x 1 + x 2 ^ 2 := by
  simp [slT]
  ring

theorem slT_cube : slT ∘ₗ slT ∘ₗ slT = (LinearMap.id : Module.End K (Fin 3 → K)) := by
  refine LinearMap.ext fun x => funext fun i => ?_
  fin_cases i <;> simp [slT] <;> ring

theorem slT_indep (c : ℕ) (hc : c < 3) (h : (slT : Module.End K (Fin 3 → K)) ^ c = 1) : c = 0 := by
  have h1 := LinearMap.congr_fun h ![1, 0, 0]
  interval_cases c
  · rfl
  · simp [slT] at h1
  · simp [pow_succ, slT] at h1

end Odd

section OddRank

variable {n : ℕ} {K : Type} [Field K] [Finite K]

theorem not_rankLE2_orthDerived_odd (hn : 3 ≤ n) (h2 : (2 : K) ≠ 0) :
    ¬ RankLE2 3 (orthDerived (quadOdd n K)) := by
  obtain ⟨hnd, hT⟩ := regular_quadOdd h2 hn
  have p01 : (oddPair K (⟨0, by omega⟩ : Fin n)).Orth (oddPair K ⟨1, by omega⟩) :=
    oddPair_orth (by simp [Fin.ext_iff])
  refine not_rankLE2_of_m2Block hnd hT p01 (oddBlock (K := K) (⟨2, by omega⟩ : Fin n)) ?_ ?_ slT
    (fun y => slT_isom y) slT_cube (fun c hc h => slT_indep c hc h)
  · intro y
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [m2Proj, oddBlock, oddPair, polar_quadOdd_single_inl, polar_quadOdd_single_inr_inl,
        oddEmb_inl, oddEmb_inr_inl, Fin.ext_iff]
  · intro X
    ext a
    fin_cases a <;>
      simp [oddBlock, oddProj, m2Emb, oddPair, Fin.ext_iff]

end OddRank

section Minus

variable {n : ℕ} {K : Type} [Field K] (j : Fin (n - 1))

@[expose] def minusEmb : (Fin 4 → K) →ₗ[K] (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) where
  toFun x := x 0 • Pi.single (Sum.inl j) 1 + x 1 • Pi.single (Sum.inr (Sum.inl j)) 1 +
    x 2 • Pi.single (Sum.inr (Sum.inr 0)) 1 + x 3 • Pi.single (Sum.inr (Sum.inr 1)) 1
  map_add' x y := by simp only [Pi.add_apply, add_smul]; abel
  map_smul' c x := by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, smul_add, smul_smul]

@[expose] def minusProj : (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) →ₗ[K] (Fin 4 → K) where
  toFun v := ![v (Sum.inl j), v (Sum.inr (Sum.inl j)), v (Sum.inr (Sum.inr 0)),
    v (Sum.inr (Sum.inr 1))]
  map_add' v w := by ext i; fin_cases i <;> simp
  map_smul' c v := by ext i; fin_cases i <;> simp

theorem minusProj_emb (x : Fin 4 → K) : minusProj j (minusEmb j x) = x := by
  ext i; fin_cases i <;> simp [minusProj, minusEmb]

theorem minusEmb_inl (y : Fin 4 → K) (i : Fin (n - 1)) :
    minusEmb j y (Sum.inl i) = if i = j then y 0 else 0 := by
  by_cases h : i = j <;> simp [minusEmb, h]

theorem minusEmb_inr_inl (y : Fin 4 → K) (i : Fin (n - 1)) :
    minusEmb j y (Sum.inr (Sum.inl i)) = if i = j then y 1 else 0 := by
  by_cases h : i = j <;> simp [minusEmb, h]

theorem minusEmb_t0 (y : Fin 4 → K) : minusEmb j y (Sum.inr (Sum.inr 0)) = y 2 := by
  simp [minusEmb]

theorem minusEmb_t1 (y : Fin 4 → K) : minusEmb j y (Sum.inr (Sum.inr 1)) = y 3 := by
  simp [minusEmb]

theorem Q_minus_add (b c : K) (v : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) (y : Fin 4 → K)
    (hv : minusProj j v = 0) :
    quadMinus n K b c (v + minusEmb j y) = quadMinus n K b c v +
      (y 0 * y 1 + y 2 ^ 2 + b * y 2 * y 3 + c * y 3 ^ 2) := by
  have e0 := congrFun hv 0
  have e1 := congrFun hv 1
  have e2 := congrFun hv 2
  have e3 := congrFun hv 3
  simp [minusProj] at e0 e1 e2 e3
  rw [quadMinus_apply, quadMinus_apply]
  have hterm : ∀ i : Fin (n - 1),
      (v + minusEmb j y) (Sum.inl i) * (v + minusEmb j y) (Sum.inr (Sum.inl i)) =
        v (Sum.inl i) * v (Sum.inr (Sum.inl i)) + if i = j then y 0 * y 1 else 0 := by
    intro i
    by_cases hij : i = j
    · subst hij
      simp [minusEmb_inl, minusEmb_inr_inl, e0, e1]
    · simp [minusEmb_inl, minusEmb_inr_inl, hij]
  rw [Finset.sum_congr rfl fun i _ => hterm i]
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true, Pi.add_apply,
    minusEmb_t0, minusEmb_t1, e2, e3, zero_add]
  ring

@[expose] def minusBlock (b c : K) : QBlock (quadMinus n K b c) (Fin 4 → K) where
  ι := minusEmb j
  m := minusProj j
  qM x := x 0 * x 1 + x 2 ^ 2 + b * x 2 * x 3 + c * x 3 ^ 2
  m_ι := minusProj_emb j
  Q_add v y hv := Q_minus_add j b c v y hv

@[expose] def tailT (b : K) : (Fin 4 → K) →ₗ[K] (Fin 4 → K) where
  toFun x := ![-x 1, -x 0 + x 1 + 2 * x 2 + b * x 3, -x 1 - x 2 - b * x 3, x 3]
  map_add' x y := by ext i; fin_cases i <;> simp <;> ring
  map_smul' c x := by ext i; fin_cases i <;> simp <;> ring

theorem tailT_isom (b c : K) (x : Fin 4 → K) :
    tailT b x 0 * tailT b x 1 + tailT b x 2 ^ 2 + b * tailT b x 2 * tailT b x 3 +
      c * tailT b x 3 ^ 2 = x 0 * x 1 + x 2 ^ 2 + b * x 2 * x 3 + c * x 3 ^ 2 := by
  simp [tailT]
  ring

theorem tailT_cube (b : K) :
    tailT b ∘ₗ tailT b ∘ₗ tailT b = (LinearMap.id : Module.End K (Fin 4 → K)) := by
  refine LinearMap.ext fun x => funext fun i => ?_
  fin_cases i <;> simp [tailT] <;> ring

theorem tailT_indep (b : K) (m : ℕ) (hm : m < 3)
    (h : (tailT b : Module.End K (Fin 4 → K)) ^ m = 1) : m = 0 := by
  have h1 := LinearMap.congr_fun h ![1, 0, 0, 0]
  interval_cases m
  · rfl
  · simp [tailT] at h1
  · simp [pow_succ, tailT] at h1

end Minus

section MinusRank

variable {n : ℕ} {K : Type} [Field K] [Finite K] {b c : K}

theorem not_rankLE2_orthDerived_minus (hn : 4 ≤ n) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ¬ RankLE2 3 (orthDerived (quadMinus n K b c)) := by
  obtain ⟨hnd, hT⟩ := regular_quadMinus hn hirr
  have p01 : (minusPair K b c (⟨0, by omega⟩ : Fin (n - 1))).Orth
      (minusPair K b c ⟨1, by omega⟩) := minusPair_orth (by simp [Fin.ext_iff])
  refine not_rankLE2_of_m2Block hnd hT p01 (minusBlock (⟨2, by omega⟩ : Fin (n - 1)) b c) ?_ ?_
    (tailT b) (fun y => tailT_isom b c y) (tailT_cube b) (fun m hm h => tailT_indep b m hm h)
  · intro y
    ext a a'
    fin_cases a <;> fin_cases a' <;>
      simp [m2Proj, minusBlock, minusPair, polar_quadMinus_single_inl,
        polar_quadMinus_single_inr_inl, minusEmb_inl, minusEmb_inr_inl, Fin.ext_iff]
  · intro X
    ext a
    fin_cases a <;> simp [minusBlock, minusProj, m2Emb, minusPair, Fin.ext_iff]

end MinusRank

section Stated

variable {n : ℕ} {K : Type} [Field K] [Finite K]

theorem not_rankLE2_three_odd (hn : 3 ≤ n) (h2 : (2 : K) ≠ 0) :
    ¬ RankLE2 3 (StatedProj (StatedOmega (StatedQuadOdd n K))) := by
  obtain ⟨hnd, -⟩ := regular_quadOdd h2 hn
  exact not_rankLE2_statedProj (coe_quadOdd n K) (commutator_orthogonalGroup_quadOdd h2 hn) hnd
    Nat.prime_three (by norm_num) (not_rankLE2_orthDerived_odd hn h2)

theorem not_rankLE2_three_plus (hn : 4 ≤ n) :
    ¬ RankLE2 3 (StatedProj (StatedOmega (StatedQuadPlus n K))) := by
  have : Nonempty (Fin n ⊕ Fin n) := ⟨Sum.inl ⟨0, by omega⟩⟩
  obtain ⟨hnd, -⟩ := regular_quadPlus (K := K) (n := n) (by omega)
  exact not_rankLE2_statedProj (coe_quadPlus n K) (commutator_orthogonalGroup_quadPlus (by omega))
    hnd Nat.prime_three (by norm_num) (not_rankLE2_orthDerived_plus hn)

theorem not_rankLE2_three_minus {b c : K} (hn : 4 ≤ n) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ¬ RankLE2 3 (StatedProj (StatedOmega (StatedQuadMinus n K b c))) := by
  have : Nonempty (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) := ⟨Sum.inr (Sum.inr 0)⟩
  obtain ⟨hnd, -⟩ := regular_quadMinus hn hirr
  exact not_rankLE2_statedProj (coe_quadMinus n K b c)
    (commutator_orthogonalGroup_quadMinus hn hirr) hnd Nat.prime_three (by norm_num)
    (not_rankLE2_orthDerived_minus hn hirr)

end Stated

section Cat

theorem not_rankLE2_orthogonal_three :
    ∀ (d : TauCeti.ValidLieTypeIndex), IsOrthogonalIndex d.1 → ¬ RankLE2 3 (Cat d) := by
  rintro ⟨d, hv⟩ horth
  rcases horth with ⟨r, q, rfl, hr3, hq⟩ | ⟨r, q, rfl⟩ | ⟨r, q, rfl⟩
  ·
    let e := CFSG.RankThree.PartTwo.Census.Carrier.SpinB.typeBGroupEquivStatedProj_odd r q hv hq
      hr3
    have : Finite ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.B r q, hv⟩) :=
      CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
    have hcard : Nat.card ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.B r q, hv⟩) =
        q.p ^ q.exponent := by
      rw [card_fixedField_eq]
      simp [TauCeti.ValidLieTypeIndex.characteristic, TauCeti.ValidLieTypeIndex.fieldExponent]
    have h2 : (2 : ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.B r q, hv⟩)) ≠ 0 := by
      have hring := CFSG.ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq q.prime_p
        q.exponent_pos hcard
      have : CharP ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.B r q, hv⟩) q.p :=
        ringChar.of_eq hring
      intro h
      have : q.p ∣ 2 := (CharP.cast_eq_zero_iff
        ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.B r q, hv⟩) q.p 2).mp (by exact_mod_cast h)
      exact hq ((Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).mp this)
    exact fun h => not_rankLE2_three_odd hr3 h2 (RankLE2.of_mulEquiv e h)
  ·
    have hr4 : 4 ≤ r := ((TauCeti.LieTypeIndex.inStandardRange_iff _).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1)
    let e := CFSG.RankThree.PartTwo.Census.Carrier.SpinD.typeDGroupEquivStatedProj_of_valid r q hv
    have : Finite ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D r q, hv⟩) :=
      CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
    exact fun h => not_rankLE2_three_plus hr4 (RankLE2.of_mulEquiv e h)
  ·
    have hr4 : 4 ≤ r := ((TauCeti.LieTypeIndex.inStandardRange_iff _).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1)
    obtain ⟨b, c, hirr, ⟨e⟩⟩ :=
      CFSG.RankThree.PartTwo.Census.Carrier.SpinD.exists_typeTwistedDGroupEquivStatedProj_of_valid
        r q hv
    have : Finite ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.twistedD r q, hv⟩) :=
      CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
    exact fun h => not_rankLE2_three_minus hr4 hirr (RankLE2.of_mulEquiv e h)

end Cat

end CFSG.LieType.SeitzGeneration
