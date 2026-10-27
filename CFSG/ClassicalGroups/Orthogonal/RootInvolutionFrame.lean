module

public import CFSG.ClassicalGroups.Orthogonal.Eichler

public section

namespace CFSG.ClassicalGroups.Orthogonal

open QuadraticMap Matrix

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V} {n : ℕ}

@[expose] def rootFrameEmb (b : Fin n → V) : (Fin n → K) →ₗ[K] V where
  toFun x := ∑ i, x i • b i
  map_add' x y := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c x := by simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum,
    RingHom.id_apply]

theorem rootFrameEmb_apply (b : Fin n → V) (x : Fin n → K) :
    rootFrameEmb b x = ∑ i, x i • b i :=
  rfl

section CharTwo

variable [CharP K 2]

structure IsGramFrame (Q : QuadraticForm K V) (G₀ : Matrix (Fin n) (Fin n) (ZMod 2))
    (b : Fin n → V) : Prop where
  polar_eq : ∀ i j, polar Q (b i) (b j) = ZMod.castHom (dvd_refl 2) K (G₀ i j)

@[expose] def rootFrameProj (Q : QuadraticForm K V) (G₀ : Matrix (Fin n) (Fin n) (ZMod 2))
    (b : Fin n → V) : V →ₗ[K] (Fin n → K) where
  toFun v j := ∑ i, ZMod.castHom (dvd_refl 2) K (G₀ j i) * polar Q v (b i)
  map_add' v w := by
    funext j
    simp only [polar_add_left, mul_add, Finset.sum_add_distrib, Pi.add_apply]
  map_smul' c v := by
    funext j
    simp only [polar_smul_left, smul_eq_mul, Pi.smul_apply, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => mul_left_comm _ _ _

theorem rootFrameProj_apply (G₀ : Matrix (Fin n) (Fin n) (ZMod 2)) (b : Fin n → V) (v : V)
    (j : Fin n) :
    rootFrameProj Q G₀ b v j = ∑ i, ZMod.castHom (dvd_refl 2) K (G₀ j i) * polar Q v (b i) :=
  rfl

@[expose] def rootFrameEnd (Q : QuadraticForm K V) (G₀ : Matrix (Fin n) (Fin n) (ZMod 2))
    (b : Fin n → V) (A : Matrix (Fin n) (Fin n) K) : Module.End K V :=
  1 + rootFrameEmb b ∘ₗ (A - 1).mulVecLin ∘ₗ rootFrameProj Q G₀ b

theorem rootFrameEnd_apply (G₀ : Matrix (Fin n) (Fin n) (ZMod 2)) (b : Fin n → V)
    (A : Matrix (Fin n) (Fin n) K) (v : V) :
    rootFrameEnd Q G₀ b A v = v + rootFrameEmb b ((A - 1) *ᵥ rootFrameProj Q G₀ b v) :=
  rfl

variable {G₀ : Matrix (Fin n) (Fin n) (ZMod 2)} {b : Fin n → V}

theorem rootFrameProj_rootFrameEmb (hb : IsGramFrame Q G₀ b) (hG : G₀ᵀ = G₀)
    (hG2 : G₀ * G₀ = 1) (x : Fin n → K) : rootFrameProj Q G₀ b (rootFrameEmb b x) = x := by
  have hpol : ∀ i, polar Q (rootFrameEmb b x) (b i) =
      ∑ k, x k * ZMod.castHom (dvd_refl 2) K (G₀ k i) := by
    intro i
    rw [← QuadraticMap.polarBilin_apply_apply, rootFrameEmb_apply, map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, LinearMap.smul_apply, QuadraticMap.polarBilin_apply_apply, hb.polar_eq,
      smul_eq_mul]
  funext j
  rw [rootFrameProj_apply]
  simp only [hpol, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hδ : ∀ k, ∑ i, ZMod.castHom (dvd_refl 2) K (G₀ j i) *
      (x k * ZMod.castHom (dvd_refl 2) K (G₀ k i)) =
        x k * ZMod.castHom (dvd_refl 2) K ((1 : Matrix (Fin n) (Fin n) (ZMod 2)) j k) := by
    intro k
    rw [← hG2, Matrix.mul_apply, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hs : G₀ k i = G₀ i k := by rw [← Matrix.transpose_apply G₀ i k, hG]
    rw [hs, map_mul]
    ring
  simp only [hδ]
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hkj
    simp [Matrix.one_apply_ne hkj.symm]
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem rootFrameEnd_one : rootFrameEnd Q G₀ b 1 = 1 := by
  simp [rootFrameEnd]

theorem rootFrameEnd_mul (hb : IsGramFrame Q G₀ b) (hG : G₀ᵀ = G₀) (hG2 : G₀ * G₀ = 1)
    (A C : Matrix (Fin n) (Fin n) K) :
    rootFrameEnd Q G₀ b (A * C) = rootFrameEnd Q G₀ b A * rootFrameEnd Q G₀ b C := by
  refine LinearMap.ext fun v => ?_
  have hπ : rootFrameProj Q G₀ b (rootFrameEnd Q G₀ b C v) = C *ᵥ rootFrameProj Q G₀ b v := by
    rw [rootFrameEnd_apply, map_add, rootFrameProj_rootFrameEmb hb hG hG2]
    simp only [Matrix.sub_mulVec, Matrix.one_mulVec]
    abel
  change rootFrameEnd Q G₀ b (A * C) v = rootFrameEnd Q G₀ b A (rootFrameEnd Q G₀ b C v)
  rw [rootFrameEnd_apply G₀ b A (rootFrameEnd Q G₀ b C v), hπ, rootFrameEnd_apply G₀ b C v,
    rootFrameEnd_apply G₀ b (A * C) v, add_assoc, ← map_add]
  congr 2
  simp only [Matrix.sub_mulVec, Matrix.one_mulVec]
  rw [← Matrix.mulVec_mulVec]
  abel

theorem rootFrameEnd_injective (hb : IsGramFrame Q G₀ b) (hG : G₀ᵀ = G₀)
    (hG2 : G₀ * G₀ = 1) : Function.Injective (rootFrameEnd Q G₀ b) := by
  intro A C hAC
  have hemb : ∀ (M : Matrix (Fin n) (Fin n) K) (x : Fin n → K),
      rootFrameEnd Q G₀ b M (rootFrameEmb b x) = rootFrameEmb b (M *ᵥ x) := by
    intro M x
    rw [rootFrameEnd_apply, rootFrameProj_rootFrameEmb hb hG hG2, ← map_add]
    congr 1
    simp only [Matrix.sub_mulVec, Matrix.one_mulVec]
    abel
  have hι : Function.Injective (rootFrameEmb (K := K) b) :=
    Function.LeftInverse.injective (rootFrameProj_rootFrameEmb hb hG hG2)
  refine Matrix.ext_of_mulVec_single fun j => hι ?_
  rw [← hemb, ← hemb, hAC]

@[expose] def rootFrameEichMat (G₀ : Matrix (Fin n) (Fin n) (ZMod 2)) (u w : Fin n → ZMod 2)
    (c : ZMod 2) : Matrix (Fin n) (Fin n) (ZMod 2) :=
  1 + vecMulVec w (G₀ *ᵥ u) - vecMulVec u (G₀ *ᵥ w) - c • vecMulVec u (G₀ *ᵥ u)

private theorem dotProduct_rootFrameProj (hG : G₀ᵀ = G₀) (hG2 : G₀ * G₀ = 1)
    (z₀ : Fin n → ZMod 2) (v : V) :
    (fun i => ZMod.castHom (dvd_refl 2) K ((G₀ *ᵥ z₀) i)) ⬝ᵥ rootFrameProj Q G₀ b v =
      polar Q v (rootFrameEmb b (fun i => ZMod.castHom (dvd_refl 2) K (z₀ i))) := by
  have hGT : (G₀.map (ZMod.castHom (dvd_refl 2) K))ᵀ = G₀.map (ZMod.castHom (dvd_refl 2) K) := by
    rw [← Matrix.transpose_map, hG]
  have hG2' : G₀.map (ZMod.castHom (dvd_refl 2) K) * G₀.map (ZMod.castHom (dvd_refl 2) K) = 1 := by
    rw [← Matrix.map_mul, hG2, Matrix.map_one _ (map_zero _) (map_one _)]
  have h1 : (fun i => ZMod.castHom (dvd_refl 2) K ((G₀ *ᵥ z₀) i)) =
      G₀.map (ZMod.castHom (dvd_refl 2) K) *ᵥ fun i => ZMod.castHom (dvd_refl 2) K (z₀ i) :=
    funext fun i => RingHom.map_mulVec _ G₀ z₀ i
  have h2 : rootFrameProj Q G₀ b v =
      G₀.map (ZMod.castHom (dvd_refl 2) K) *ᵥ fun i => polar Q v (b i) := rfl
  rw [h1, h2, Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose, hGT, Matrix.vecMul_vecMul,
    hG2', Matrix.vecMul_one, rootFrameEmb_apply, ← QuadraticMap.polarBilin_apply_apply, map_sum]
  simp only [dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, QuadraticMap.polarBilin_apply_apply, smul_eq_mul]

private theorem map_vecMulVec_mulVec (p q : Fin n → ZMod 2) (x : Fin n → K) :
    (vecMulVec p q).map (ZMod.castHom (dvd_refl 2) K) *ᵥ x =
      ((fun j => ZMod.castHom (dvd_refl 2) K (q j)) ⬝ᵥ x) •
        fun i => ZMod.castHom (dvd_refl 2) K (p i) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, vecMulVec_apply, map_mul,
    Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

private theorem map_rootFrameEichMat_sub_one (u₀ w₀ : Fin n → ZMod 2) (c₀ : ZMod 2) :
    (rootFrameEichMat G₀ u₀ w₀ c₀).map (ZMod.castHom (dvd_refl 2) K) - 1 =
      (vecMulVec w₀ (G₀ *ᵥ u₀)).map (ZMod.castHom (dvd_refl 2) K) -
        (vecMulVec u₀ (G₀ *ᵥ w₀)).map (ZMod.castHom (dvd_refl 2) K) -
          ZMod.castHom (dvd_refl 2) K c₀ •
            (vecMulVec u₀ (G₀ *ᵥ u₀)).map (ZMod.castHom (dvd_refl 2) K) := by
  ext i j
  simp only [rootFrameEichMat, Matrix.sub_apply, Matrix.add_apply, Matrix.map_apply,
    Matrix.smul_apply, smul_eq_mul, map_add, map_sub, map_mul, Matrix.one_apply]
  split_ifs <;> simp only [map_one, map_zero] <;> ring

theorem eichler_rootFrameEmb_cast (hG : G₀ᵀ = G₀) (hG2 : G₀ * G₀ = 1)
    {u₀ w₀ : Fin n → ZMod 2} {c₀ : ZMod 2} {u w : V}
    (hu : rootFrameEmb b (fun i => ZMod.castHom (dvd_refl 2) K (u₀ i)) = u)
    (hw : rootFrameEmb b (fun i => ZMod.castHom (dvd_refl 2) K (w₀ i)) = w) (hQu : Q u = 0)
    (huw : polar Q u w = 0) (hQw : Q w = ZMod.castHom (dvd_refl 2) K c₀) :
    ((eichler Q u w : V ≃ₗ[K] V) : Module.End K V) =
      rootFrameEnd Q G₀ b ((rootFrameEichMat G₀ u₀ w₀ c₀).map (ZMod.castHom (dvd_refl 2) K)) := by
  refine LinearMap.ext fun v => ?_
  rw [LinearEquiv.coe_coe, eichler_apply hQu huw, rootFrameEnd_apply, map_rootFrameEichMat_sub_one,
    Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec, map_vecMulVec_mulVec,
    map_vecMulVec_mulVec, map_vecMulVec_mulVec, dotProduct_rootFrameProj hG hG2,
    dotProduct_rootFrameProj hG hG2, map_sub, map_sub, map_smul, map_smul, map_smul, map_smul, hu,
    hw, hQw]
  module

theorem polar_rootFrameEmb_cast (hb : IsGramFrame Q G₀ b) (x₀ y₀ : Fin n → ZMod 2) :
    polar Q (rootFrameEmb b (fun i => ZMod.castHom (dvd_refl 2) K (x₀ i)))
        (rootFrameEmb b (fun i => ZMod.castHom (dvd_refl 2) K (y₀ i))) =
      ZMod.castHom (dvd_refl 2) K (x₀ ⬝ᵥ (G₀ *ᵥ y₀)) := by
  rw [← QuadraticMap.polarBilin_apply_apply, rootFrameEmb_apply, rootFrameEmb_apply]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    QuadraticMap.polarBilin_apply_apply, hb.polar_eq, smul_eq_mul, dotProduct, Matrix.mulVec,
    map_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

@[expose] def rootFrameQ (G₀ : Matrix (Fin n) (Fin n) (ZMod 2)) (q₀ x₀ : Fin n → ZMod 2) :
    ZMod 2 :=
  ∑ i, x₀ i * q₀ i + ∑ i, ∑ j, if i < j then x₀ i * x₀ j * G₀ i j else 0

private theorem map_sum_smul_frame (hb : IsGramFrame Q G₀ b) (q₀ x₀ : Fin n → ZMod 2)
    (hq : ∀ i, x₀ i ≠ 0 → Q (b i) = ZMod.castHom (dvd_refl 2) K (q₀ i)) (s : Finset (Fin n)) :
    Q (∑ i ∈ s, ZMod.castHom (dvd_refl 2) K (x₀ i) • b i) =
      ZMod.castHom (dvd_refl 2) K (∑ i ∈ s, x₀ i * q₀ i +
        ∑ i ∈ s, ∑ j ∈ s, if i < j then x₀ i * x₀ j * G₀ i j else 0) := by
  induction s using Finset.induction_on_max with
  | empty => simp
  | insert a s ha ih =>
    have has : a ∉ s := fun h => lt_irrefl a (ha a h)
    have hQa : Q (ZMod.castHom (dvd_refl 2) K (x₀ a) • b a) =
        ZMod.castHom (dvd_refl 2) K (x₀ a * q₀ a) := by
      rw [QuadraticMap.map_smul]
      by_cases hx : x₀ a = 0
      · rw [hx]
        simp
      · have h1 : x₀ a = 1 := by
          revert hx
          generalize x₀ a = y
          revert y
          decide
        rw [hq a hx, h1]
        simp
    have hpol : polar Q (ZMod.castHom (dvd_refl 2) K (x₀ a) • b a)
        (∑ i ∈ s, ZMod.castHom (dvd_refl 2) K (x₀ i) • b i) =
          ZMod.castHom (dvd_refl 2) K (∑ i ∈ s, x₀ i * x₀ a * G₀ i a) := by
      rw [← QuadraticMap.polarBilin_apply_apply, map_sum, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [QuadraticMap.polarBilin_apply_apply, polar_comm, polar_smul_left, polar_smul_right,
        hb.polar_eq, smul_eq_mul, smul_eq_mul, map_mul, map_mul]
      ring
    have hds : (∑ i ∈ insert a s, ∑ j ∈ insert a s,
        if i < j then x₀ i * x₀ j * G₀ i j else 0) =
          ∑ i ∈ s, x₀ i * x₀ a * G₀ i a +
            ∑ i ∈ s, ∑ j ∈ s, if i < j then x₀ i * x₀ j * G₀ i j else 0 := by
      rw [Finset.sum_insert has, Finset.sum_insert has, if_neg (lt_irrefl a),
        Finset.sum_eq_zero fun j hj => if_neg (not_lt.mpr (ha j hj).le), zero_add, zero_add,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.sum_insert has, if_pos (ha i hi)]
    rw [Finset.sum_insert has, QuadraticMap.map_add Q, ih, hQa, hpol, hds, Finset.sum_insert has]
    simp only [map_add]
    ring

theorem map_rootFrameEmb_cast (hb : IsGramFrame Q G₀ b) (q₀ x₀ : Fin n → ZMod 2)
    (hq : ∀ i, x₀ i ≠ 0 → Q (b i) = ZMod.castHom (dvd_refl 2) K (q₀ i)) :
    Q (rootFrameEmb b (fun i => ZMod.castHom (dvd_refl 2) K (x₀ i))) =
      ZMod.castHom (dvd_refl 2) K (rootFrameQ G₀ q₀ x₀) := by
  rw [rootFrameEmb_apply, rootFrameQ]
  exact map_sum_smul_frame hb q₀ x₀ hq Finset.univ

@[expose] def rootPairFrame {k : ℕ} (x y : Fin k → V) : Fin (2 * k) → V := fun i =>
  if i.val % 2 = 0 then x ⟨i.val / 2, by omega⟩ else y ⟨i.val / 2, by omega⟩

@[expose] def rootPairGram (n : ℕ) : Matrix (Fin n) (Fin n) (ZMod 2) :=
  Matrix.of fun i j => if i.val / 2 = j.val / 2 ∧ i ≠ j then 1 else 0

omit [AddCommGroup V] in
private theorem rootPairFrame_cases {k : ℕ} (x y : Fin k → V) (i : Fin (2 * k)) :
    ∃ l : Fin k, (rootPairFrame x y i = x l ∧ i.val = 2 * l.val) ∨
      (rootPairFrame x y i = y l ∧ i.val = 2 * l.val + 1) := by
  refine ⟨⟨i.val / 2, by omega⟩, ?_⟩
  unfold rootPairFrame
  split_ifs with h
  · exact Or.inl ⟨rfl, show i.val = 2 * (i.val / 2) by omega⟩
  · exact Or.inr ⟨rfl, show i.val = 2 * (i.val / 2) + 1 by omega⟩

private theorem rootPairGram_apply {n : ℕ} (i j : Fin n) :
    rootPairGram n i j = if i.val / 2 = j.val / 2 ∧ i.val ≠ j.val then 1 else 0 := by
  simp only [rootPairGram, Matrix.of_apply, ne_eq, Fin.ext_iff]

theorem isGramFrame_rootPairFrame {k : ℕ} {x y : Fin k → V}
    (hxy : ∀ i, polar Q (x i) (y i) = 1)
    (horth : ∀ i j, i ≠ j → polar Q (x i) (x j) = 0 ∧ polar Q (x i) (y j) = 0 ∧
      polar Q (y i) (x j) = 0 ∧ polar Q (y i) (y j) = 0) :
    IsGramFrame Q (rootPairGram (2 * k)) (rootPairFrame x y) := by
  have hself : ∀ v : V, polar Q v v = 0 := fun v => by
    rw [polar_self_eq_two_mul, CharTwo.two_eq_zero, zero_mul]
  refine ⟨fun i j => ?_⟩
  rw [rootPairGram_apply]
  obtain ⟨l, ⟨hi, hil⟩ | ⟨hi, hil⟩⟩ := rootPairFrame_cases x y i <;>
    obtain ⟨l', ⟨hj, hjl⟩ | ⟨hj, hjl⟩⟩ := rootPairFrame_cases x y j <;>
    rw [hi, hj] <;>
    rcases eq_or_ne l l' with rfl | hll
  · rw [if_neg (by omega), map_zero, hself]
  · rw [if_neg (fun h => hll (Fin.ext (by omega))), map_zero, (horth l l' hll).1]
  · rw [if_pos (by omega), map_one, hxy]
  · rw [if_neg (fun h => hll (Fin.ext (by omega))), map_zero, (horth l l' hll).2.1]
  · rw [if_pos (by omega), map_one, polar_comm, hxy]
  · rw [if_neg (fun h => hll (Fin.ext (by omega))), map_zero, (horth l l' hll).2.2.1]
  · rw [if_neg (by omega), map_zero, hself]
  · rw [if_neg (fun h => hll (Fin.ext (by omega))), map_zero, (horth l l' hll).2.2.2]

end CharTwo

end CFSG.ClassicalGroups.Orthogonal
