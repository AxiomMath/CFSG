module

public import CFSG.ClassicalInvolution.Phan.PhanQ43Theta
public import CFSG.ClassicalInvolution.Phan.PhanP18Swap
public import CFSG.ClassicalInvolution.Phan.PhanQ2Act

public section

namespace CFSG.ClassicalInvolution.PhanQ

open QuadraticMap CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution.PhanP
  CFSG.ClassicalInvolution.PhanD4 CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.LieType.BorelTits CFSG.ClassicalGroups.Unitary CFSG.ClassicalInvolution.Phan

section Frames

variable {F K : Type} [Field F] [Field K] [Algebra F K] {ε : F} (D : KData F K ε)

theorem npair_orth_of_vecK (h2 : (2 : K) ≠ 0) (hε : ε ≠ 0) {z w : NPair ε}
    (hB : B8 (vecK D z) (vecK D w) = 0) (hH : her D (vecK D z) (vecK D w) = 0) :
    B8 z.x w.x = 0 ∧ B8 z.x w.y = 0 ∧ B8 z.y w.x = 0 ∧ B8 z.y w.y = 0 := by
  have h2F := two_ne_zero_of_algebra (F := F) h2
  rw [B8_vecK] at hB
  rw [her_vecK] at hH
  obtain ⟨h1, h3⟩ := theta_indep D h2 hε (α := B8 z.x w.x + -(1 / ε) * B8 z.y w.y)
    (β := B8 z.x w.y + B8 z.y w.x) hB
  obtain ⟨h4, h5⟩ := theta_indep D h2 hε (α := B8 z.x w.x + 1 / ε * B8 z.y w.y)
    (β := B8 z.y w.x - B8 z.x w.y) hH
  have hxx : B8 z.x w.x = 0 := by
    have : 2 * B8 z.x w.x = 0 := by linear_combination h1 + h4
    exact (mul_eq_zero.1 this).resolve_left h2F
  have hyy : B8 z.y w.y = 0 := by
    have h6 : 2 * ((1 / ε) * B8 z.y w.y) = 0 := by linear_combination h4 - h1
    have h7 := (mul_eq_zero.1 h6).resolve_left h2F
    exact (mul_eq_zero.1 h7).resolve_left (one_div_ne_zero hε)
  have hxy : B8 z.x w.y = 0 := by
    have : 2 * B8 z.x w.y = 0 := by linear_combination h3 - h5
    exact (mul_eq_zero.1 this).resolve_left h2F
  have hyx : B8 z.y w.x = 0 := by linear_combination h3 - hxy
  exact ⟨hxx, hxy, hyx, hyy⟩

theorem PhanSolid.exists_orthoframe [Finite K] [Finite F] {W : Submodule K (V8 K)}
    (hW : PhanSolid D W) (hodd : Odd (Nat.card F)) (h2 : (2 : K) ≠ 0) (hε : ε ≠ 0)
    {σ : K ≃+* K} (hσ : ∀ x, σ x = D.τ x) :
    ∃ z : Fin 4 → NPair ε, LinearIndependent K (fun i => vecK D (z i)) ∧
      (∀ i, vecK D (z i) ∈ W) ∧
      ∀ i j, i ≠ j → B8 (z i).x (z j).x = 0 ∧ B8 (z i).x (z j).y = 0 ∧
        B8 (z i).y (z j).x = 0 ∧ B8 (z i).y (z j).y = 0 := by
  obtain ⟨Θ, hΘ⟩ := PhanSolid.exists_isometry D hW h2 hε hσ
  let u : Fin 4 → V8 K := fun i => (Θ (Pi.single i 1) : V8 K)
  have hu_mem : ∀ i, u i ∈ W := fun i => (Θ (Pi.single i 1)).2
  have hu_her : ∀ i j, her D (u i) (u j) = if i = j then 1 else 0 := by
    intro i j
    have := hΘ (Pi.single j 1) (Pi.single i 1)
    rw [← this]
    simp [herm_def, Pi.single_apply, eq_comm]
  have hu_ff : ∀ i, ffK D (u i) := by
    intro i
    refine ⟨?_, by rw [hu_her]; simp⟩
    have h1 := hW.ts _ (hu_mem i) _ (hu_mem i)
    rw [B8_self] at h1
    exact (mul_eq_zero.1 h1).resolve_left h2
  choose κ hκ z hz using fun i => exists_npair_of_ffK D hodd h2 hε (hu_ff i)
  have hindep : LinearIndependent K u := by
    have := (Pi.basisFun K (Fin 4)).linearIndependent.map' (W.subtype ∘ₗ Θ.toLinearMap)
      (by
        rw [LinearMap.ker_eq_bot]
        exact fun a b h => Θ.injective (Subtype.ext h))
    simpa [u, Function.comp_def] using this
  refine ⟨z, ?_, ?_, ?_⟩
  · have := hindep.units_smul (fun i => (Units.mk0 (κ i) (hκ i))⁻¹)
    convert this using 1
    ext i : 1
    simp [hz i, smul_smul, Units.smul_def, inv_mul_cancel₀ (hκ i)]
  · intro i
    have : vecK D (z i) = (κ i)⁻¹ • u i := by
      rw [hz i, smul_smul, inv_mul_cancel₀ (hκ i), one_smul]
    rw [this]
    exact W.smul_mem _ (hu_mem i)
  · intro i j hij
    refine npair_orth_of_vecK D h2 hε ?_ ?_
    · have e1 : vecK D (z i) = (κ i)⁻¹ • u i := by
        rw [hz i, smul_smul, inv_mul_cancel₀ (hκ i), one_smul]
      have e2 : vecK D (z j) = (κ j)⁻¹ • u j := by
        rw [hz j, smul_smul, inv_mul_cancel₀ (hκ j), one_smul]
      rw [e1, e2, B8_smul_left, B8_smul_right, hW.ts _ (hu_mem i) _ (hu_mem j), mul_zero,
        mul_zero]
    · have e1 : vecK D (z i) = (κ i)⁻¹ • u i := by
        rw [hz i, smul_smul, inv_mul_cancel₀ (hκ i), one_smul]
      have e2 : vecK D (z j) = (κ j)⁻¹ • u j := by
        rw [hz j, smul_smul, inv_mul_cancel₀ (hκ j), one_smul]
      rw [e1, e2, her_smul_left, her_smul_right, hu_her]
      simp [hij]

end Frames

section WittFrames

variable {F : Type} [Field F] {ε : F}

theorem Q8_add_B8 (x y : V8 F) : Q8 (x + y) = Q8 x + Q8 y + B8 x y := by
  simpa using Q8_lin (1 : F) 1 x y

theorem B8_sum_right {ι : Type} (s : Finset ι) (x : V8 F) (f : ι → V8 F) :
    B8 x (∑ k ∈ s, f k) = ∑ k ∈ s, B8 x (f k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [B8_eq_sum]
  | insert k s hk ih => rw [Finset.sum_insert hk, Finset.sum_insert hk, B8_add_right, ih]

theorem Q_sum_orth {ι : Type} [DecidableEq ι] (s : Finset ι) (v : ι → V8 F) (w : ι → F)
    (hQ : ∀ k, Q8 (v k) = w k) (hB : ∀ j k, j ≠ k → B8 (v j) (v k) = 0) (c : ι → F) :
    Q8 (∑ k ∈ s, c k • v k) = ∑ k ∈ s, w k * c k ^ 2 := by
  induction s using Finset.induction_on with
  | empty => simp [Q8_eq_sum]
  | insert k s hk ih =>
    rw [Finset.sum_insert hk, Finset.sum_insert hk, Q8_add_B8, ih]
    have h1 : B8 (c k • v k) (∑ j ∈ s, c j • v j) = 0 := by
      rw [B8_smul_left, B8_sum_right]
      have : ∀ j ∈ s, B8 (v k) (c j • v j) = 0 := by
        intro j hj
        rw [B8_smul_right, hB k j (fun h => hk (h ▸ hj)), mul_zero]
      rw [Finset.sum_eq_zero this, mul_zero]
    have h2 : Q8 (c k • v k) = w k * c k ^ 2 := by
      have := Q8_lin (c k) 0 (v k) 0
      rw [zero_smul, add_zero] at this
      rw [this, hQ]
      ring
    rw [h1, h2, add_zero]

@[expose] def combLin {ι : Type} [Fintype ι] (v : ι → V8 F) : (ι → F) →ₗ[F] V8 F where
  toFun c := ∑ k, c k • v k
  map_add' c d := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a c := by simp [Finset.smul_sum, smul_smul]

@[expose] noncomputable def combIsometry {ι : Type} [Fintype ι] [DecidableEq ι] (v : ι → V8 F)
    (w : ι → F) (hQ : ∀ k, Q8 (v k) = w k) (hB : ∀ j k, j ≠ k → B8 (v j) (v k) = 0) :
    (QuadraticMap.weightedSumSquares F w) →qᵢ quadPlus 4 F where
  toLinearMap := combLin v
  map_app' c := by
    rw [QuadraticMap.weightedSumSquares_apply]
    show Q8 (∑ k, c k • v k) = _
    rw [Q_sum_orth Finset.univ v w hQ hB c]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [smul_eq_mul]
    ring

@[expose] def frameVecs {n : ℕ} (z : Fin n → NPair ε) : Fin n × Fin 2 → V8 F :=
  fun p => if p.2 = 0 then (z p.1).x else (z p.1).y

@[expose] def frameW (ε : F) {n : ℕ} : Fin n × Fin 2 → F := fun p => if p.2 = 0 then 1 else ε

theorem frameVecs_Q {n : ℕ} (z : Fin n → NPair ε) (p : Fin n × Fin 2) :
    Q8 (frameVecs z p) = frameW ε p := by
  obtain ⟨i, j⟩ := p
  fin_cases j
  · simp [frameVecs, frameW, (z i).hx]
  · simp [frameVecs, frameW, (z i).hy]

theorem frameVecs_B {n : ℕ} (z : Fin n → NPair ε)
    (horth : ∀ i j, i ≠ j → B8 (z i).x (z j).x = 0 ∧ B8 (z i).x (z j).y = 0 ∧
      B8 (z i).y (z j).x = 0 ∧ B8 (z i).y (z j).y = 0) (p q : Fin n × Fin 2) (hpq : p ≠ q) :
    B8 (frameVecs z p) (frameVecs z q) = 0 := by
  obtain ⟨i, j⟩ := p
  obtain ⟨i', j'⟩ := q
  by_cases hi : i = i'
  · subst hi
    have hj : j ≠ j' := fun h => hpq (by rw [h])
    fin_cases j <;> fin_cases j' <;> simp_all [frameVecs, B8_comm (z i).y (z i).x, (z i).hxy]
  · obtain ⟨h1, h2, h3, h4⟩ := horth i i' hi
    fin_cases j <;> fin_cases j' <;> simp [frameVecs, h1, h2, h3, h4]

theorem combLin_single {ι : Type} [Fintype ι] [DecidableEq ι] (v : ι → V8 F) (p : ι) :
    combLin v (Pi.single p 1) = v p := by
  show ∑ k, (Pi.single p (1 : F) : ι → F) k • v k = v p
  rw [Finset.sum_eq_single p]
  · simp
  · intro k _ hk
    simp [hk]
  · simp

theorem exists_spin_frames [Finite F] {n : ℕ} (hn : n ≤ 3) (hodd : Odd (Nat.card F))
    (h2 : (2 : F) ≠ 0) (hε : ε ≠ 0) (z z0 : Fin n → NPair ε)
    (horth : ∀ i j, i ≠ j → B8 (z i).x (z j).x = 0 ∧ B8 (z i).x (z j).y = 0 ∧
      B8 (z i).y (z j).x = 0 ∧ B8 (z i).y (z j).y = 0)
    (horth0 : ∀ i j, i ≠ j → B8 (z0 i).x (z0 j).x = 0 ∧ B8 (z0 i).x (z0 j).y = 0 ∧
      B8 (z0 i).y (z0 j).x = 0 ∧ B8 (z0 i).y (z0 j).y = 0) :
    ∃ g : spinGroup (quadPlus 4 F), ∀ i, g • z0 i = z i := by
  have : Invertible (2 : F) := invertibleOfNonzero h2
  have hw : ∀ p : Fin n × Fin 2, IsRegular (frameW ε p) := by
    intro p
    refine IsUnit.isRegular (isUnit_iff_ne_zero.2 ?_)
    obtain ⟨i, j⟩ := p
    fin_cases j <;> simp [frameW, hε]
  have hQE := QuadraticMap.nondegenerate_weightedSumSquares hw
  let α := combIsometry (frameVecs z0) (frameW ε (n := n)) (frameVecs_Q z0) (frameVecs_B z0 horth0)
  let β := combIsometry (frameVecs z) (frameW ε (n := n)) (frameVecs_Q z) (frameVecs_B z horth)
  have hα : Function.Injective α := isometry_injective_of_nondegenerate hQE α
  have hβ : Function.Injective β := isometry_injective_of_nondegenerate hQE β
  have hreg := nondegenerate_range α hα hQE
  have hdim : 2 ≤ Module.finrank F (LinearMap.BilinForm.orthogonal (quadPlus 4 F).polarBilin
      (LinearMap.range α.toLinearMap)) := by
    have h1 := Submodule.finrank_add_eq_of_isCompl hreg.isCompl_orthogonal
    have h6 : Module.finrank F (LinearMap.range α.toLinearMap) = 2 * n := by
      rw [LinearMap.finrank_range_of_inj hα]
      simp [Module.finrank_fintype_fun_eq_card, mul_comm]
    have h8 : Module.finrank F (Fin 4 ⊕ Fin 4 → F) = 8 := by
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    rw [h6] at h1
    omega
  obtain ⟨y, hy⟩ := exists_spin_extend hodd (nondegenerate_polarBilin_quadPlus 4 F) α β hα hβ
    hreg hdim
  refine ⟨y, fun i => ?_⟩
  have e0 := hy (Pi.single (i, 0) 1)
  have e1 := hy (Pi.single (i, 1) 1)
  ext1
  · show spinAction (quadPlus 4 F) y (z0 i).x = (z i).x
    have a0 : (z0 i).x = α (Pi.single (i, 0) 1) := by
      show (z0 i).x = combLin (frameVecs z0) (Pi.single (i, 0) 1)
      rw [combLin_single]
      simp [frameVecs]
    have b0 : (z i).x = β (Pi.single (i, 0) 1) := by
      show (z i).x = combLin (frameVecs z) (Pi.single (i, 0) 1)
      rw [combLin_single]
      simp [frameVecs]
    rw [a0, b0]
    exact e0
  · show spinAction (quadPlus 4 F) y (z0 i).y = (z i).y
    have a1 : (z0 i).y = α (Pi.single (i, 1) 1) := by
      show (z0 i).y = combLin (frameVecs z0) (Pi.single (i, 1) 1)
      rw [combLin_single]
      simp [frameVecs]
    have b1 : (z i).y = β (Pi.single (i, 1) 1) := by
      show (z i).y = combLin (frameVecs z) (Pi.single (i, 1) 1)
      rw [combLin_single]
      simp [frameVecs]
    rw [a1, b1]
    exact e1

end WittFrames

end CFSG.ClassicalInvolution.PhanQ
