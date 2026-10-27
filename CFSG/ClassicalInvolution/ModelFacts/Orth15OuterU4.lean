module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15OuterU4Mat
public import CFSG.ClassicalInvolution.ModelFacts.Orth15ChainU
public import CFSG.ClassicalInvolution.ModelFacts.UnitaryAutBlocks
public import CFSG.ClassicalInvolution.Models.UnitaryFrames.Frame
public import CFSG.ClassicalInvolution.Phan.Center

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterU4

open Matrix CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.ModelFacts.UnitaryAut CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.ClassicalInvolution.ModelFacts.Orth15.ChainU
  CFSG.ClassicalGroups.Unitary

section Elements

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

omit [Finite K] [Fact p.Prime] [CharP K p] in
theorem aMat_conjTr (σ : K ≃+* K) (hσσ : ∀ c, σ (σ c) = c) {a b : K}
    (hab : σ a * a + σ b * b = 1) :
    conjTr σ !![a, b; -σ b, σ a] * !![a, b; -σ b, σ a] = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [conjTr, Matrix.mul_apply, Fin.sum_univ_two, hσσ] <;>
    first | ring1 | linear_combination hab

variable (K p f) in
@[expose] noncomputable def aSU {a b : K}
    (hab : unitaryInvolution K p f a * a + unitaryInvolution K p f b * b = 1)
    (hσσ : ∀ c, unitaryInvolution K p f (unitaryInvolution K p f c) = c) : Su K p f 2 :=
  mkSU K p f !![a, b; -unitaryInvolution K p f b, unitaryInvolution K p f a]
    (by rw [Matrix.det_fin_two_of]; linear_combination hab) (aMat_conjTr _ hσσ hab)

theorem suMat_aSU {a b : K}
    (hab : unitaryInvolution K p f a * a + unitaryInvolution K p f b * b = 1)
    (hσσ : ∀ c, unitaryInvolution K p f (unitaryInvolution K p f c) = c) :
    suMat (aSU K p f hab hσσ) =
      !![a, b; -unitaryInvolution K p f b, unitaryInvolution K p f a] := rfl

variable (K p f) in
@[expose] noncomputable def mixSU : Su K p f 4 :=
  mkSU K p f !![0, 0, 1, 0; 0, 1, 0, 0; -1, 0, 0, 0; 0, 0, 0, 1]
    (by simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove])
    (by
      ext a b
      fin_cases a <;> fin_cases b <;> simp [conjTr, Matrix.mul_apply, Fin.sum_univ_four])

theorem suMat_mixSU :
    suMat (mixSU K p f) = !![0, 0, 1, 0; 0, 1, 0, 0; -1, 0, 0, 0; 0, 0, 0, 1] := rfl

omit [Finite K] [Fact p.Prime] [CharP K p] in
theorem blockMat_four_zero (A : Matrix (Fin 2) (Fin 2) K) :
    blockMat 4 0 A = !![A 0 0, A 0 1, 0, 0; A 1 0, A 1 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] := by
  ext a b
  rw [blockMat_apply]
  fin_cases a <;> fin_cases b <;> simp

omit [Finite K] [Fact p.Prime] [CharP K p] in
theorem blockMat_four_two (A : Matrix (Fin 2) (Fin 2) K) :
    blockMat 4 2 A = !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, A 0 0, A 0 1; 0, 0, A 1 0, A 1 1] := by
  ext a b
  rw [blockMat_apply]
  fin_cases a <;> fin_cases b <;> simp

theorem suMat_blockEmb_zero (A : Su K p f 2) :
    suMat (blockEmb K p f 4 2 0 (by norm_num) A) =
      !![suMat A 0 0, suMat A 0 1, 0, 0; suMat A 1 0, suMat A 1 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] :=
  by rw [suMat_blockEmb, blockMat_four_zero]

theorem suMat_blockEmb_two (A : Su K p f 2) :
    suMat (blockEmb K p f 4 2 2 (by norm_num) A) =
      !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, suMat A 0 0, suMat A 0 1; 0, 0, suMat A 1 0, suMat A 1 1] :=
  by rw [suMat_blockEmb, blockMat_four_two]

end Elements

section Square

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem suMat_rootInvSU_four :
    suMat (rootInvSU K p f (show 2 ≤ 4 by norm_num)) =
      !![-1, 0, 0, 0; 0, -1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] := by
  rw [rootInvSU, suMat_blockEmb, suMat_negOneSU, blockMat_four_zero]
  ext a b
  fin_cases a <;> fin_cases b <;> simp

theorem rootInvSU_mul_self_four :
    rootInvSU K p f (show 2 ≤ 4 by norm_num) * rootInvSU K p f (show 2 ≤ 4 by norm_num) = 1 := by
  rw [rootInvSU, ← map_mul, negOneSU_mul_self, map_one]

theorem suMat_rootInvSU_inv_four :
    suMat (rootInvSU K p f (show 2 ≤ 4 by norm_num))⁻¹ =
      !![-1, 0, 0, 0; 0, -1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] := by
  rw [inv_eq_of_mul_eq_one_right rootInvSU_mul_self_four, suMat_rootInvSU_four]

theorem sq_of_diag4 (hK : Nat.card K = (p ^ f) ^ 2) (β : Su K p f 4 →* Su K p f 4) {s w : K}
    (hs : s ≠ 0) (hw : w ≠ 0)
    (hβ : ∀ x, suMat (β x) =
      !![s, 0, 0, 0; 0, s, 0, 0; 0, 0, w, 0; 0, 0, 0, w] * suMat x *
        !![s⁻¹, 0, 0, 0; 0, s⁻¹, 0, 0; 0, 0, w⁻¹, 0; 0, 0, 0, w⁻¹])
    (hβ2 : ∀ x, β (β x) * x⁻¹ ∈ Subgroup.center (Su K p f 4)) :
    (∀ x, β x = x) ∨ (∀ x, β x = rootInvSU K p f (show 2 ≤ 4 by norm_num) * x *
      (rootInvSU K p f (show 2 ≤ 4 by norm_num))⁻¹) := by
  have hσ : IsUnitaryInvolution (unitaryInvolution K p f) :=
    isUnitaryInvolution_unitaryInvolution hK
  obtain ⟨c, hc⟩ := exists_scalar_of_mem_center hσ (by norm_num : 3 ≤ 4) (hβ2 (mixSU K p f))
  have e : suMat (β (β (mixSU K p f)) * (mixSU K p f)⁻¹) = Matrix.scalar (Fin 4) (c : K) := hc
  have e2 : suMat (β (β (mixSU K p f))) =
      Matrix.scalar (Fin 4) (c : K) * suMat (mixSU K p f) := by
    calc suMat (β (β (mixSU K p f))) = suMat (β (β (mixSU K p f)) * (mixSU K p f)⁻¹) *
          suMat (mixSU K p f) := by
          rw [suMat_mul, Matrix.mul_assoc, suMat_inv_mul_suMat, Matrix.mul_one]
      _ = _ := by rw [e]
  have h1 : suMat (β (β (mixSU K p f))) = (c : K) • suMat (mixSU K p f) := by
    rw [e2, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul, Matrix.one_mul]
  rw [hβ (β (mixSU K p f)), hβ (mixSU K p f), suMat_mixSU] at h1
  have hss : s * s = w * w := sq_eq_of_scalar hs hw (c : K) h1
  rcases mul_self_eq_mul_self_iff.mp hss with h | h
  · left
    subst h
    intro x
    apply suMat_injective
    rw [hβ x]
    exact conj_scalar4 hs (suMat x)
  · right
    have hw' : w = -s := by linear_combination h
    subst hw'
    intro x
    apply suMat_injective
    rw [hβ x, suMat_mul, suMat_mul, suMat_rootInvSU_inv_four, suMat_rootInvSU_four, inv_neg]
    exact conj_neg4 hs (suMat x)

end Square

section Fixing

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

omit [Finite K] [Fact p.Prime] [CharP K p] in
theorem mapMatrix_refl_four (X : Matrix (Fin 4) (Fin 4) K) :
    (RingEquiv.refl K).mapMatrix X = X := by
  ext i j
  simp

theorem sq_of_lift (hK : Nat.card K = (p ^ f) ^ 2) (α : Su K p f 4 →* Su K p f 4)
    (G Gi : Matrix (Fin 4) (Fin 4) K) (φ : K ≃+* K) (hφφ : ∀ c, φ (φ c) = c)
    (hGiG : Gi * G = 1) (hα : ∀ x, suMat (α x) = G * φ.mapMatrix (suMat x) * Gi) {s w : K}
    (hs : s ≠ 0) (hw : w ≠ 0)
    (hD : G * φ.mapMatrix G = !![s, 0, 0, 0; 0, s, 0, 0; 0, 0, w, 0; 0, 0, 0, w])
    (hα4 : ∀ x, α (α (α (α x))) * x⁻¹ ∈ Subgroup.center (Su K p f 4)) :
    (∀ x, α (α x) = x) ∨ (∀ x, α (α x) = rootInvSU K p f (show 2 ≤ 4 by norm_num) * x *
      (rootInvSU K p f (show 2 ≤ 4 by norm_num))⁻¹) := by
  have hDi : φ.mapMatrix Gi * Gi = !![s⁻¹, 0, 0, 0; 0, s⁻¹, 0, 0; 0, 0, w⁻¹, 0; 0, 0, 0, w⁻¹] := by
    apply inv_of_diag4 hs hw
    rw [← hD]
    exact inv_sq_matrix φ G Gi hGiG
  have hβ : ∀ x, suMat ((α.comp α) x) =
      !![s, 0, 0, 0; 0, s, 0, 0; 0, 0, w, 0; 0, 0, 0, w] * suMat x *
        !![s⁻¹, 0, 0, 0; 0, s⁻¹, 0, 0; 0, 0, w⁻¹, 0; 0, 0, 0, w⁻¹] := by
    intro x
    show suMat (α (α x)) = _
    rw [hα (α x), hα x, alpha_sq_matrix φ hφφ, hD, hDi]
  exact sq_of_diag4 hK (α.comp α) hs hw hβ hα4

theorem su4_fixing (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) (α : Su K p f 4 →* Su K p f 4)
    (g : GL (Fin 4) K) (φ : K ≃+* K)
    (hα : ∀ x : Su K p f 4, suMat (α x) =
      (g : Matrix (Fin 4) (Fin 4) K) * φ.mapMatrix (suMat x) *
        ((g⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K))
    (hfix0 : ∀ A : Su K p f 2, α (blockEmb K p f 4 2 0 (by norm_num) A) =
      blockEmb K p f 4 2 0 (by norm_num) A)
    (hfix2 : ∀ A : Su K p f 2, α (blockEmb K p f 4 2 2 (by norm_num) A) =
      blockEmb K p f 4 2 2 (by norm_num) A)
    (hα4 : ∀ x, α (α (α (α x))) * x⁻¹ ∈ Subgroup.center (Su K p f 4)) :
    (∀ x, α (α x) = x) ∨ (∀ x, α (α x) = rootInvSU K p f (show 2 ≤ 4 by norm_num) * x *
      (rootInvSU K p f (show 2 ≤ 4 by norm_num))⁻¹) := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_charP_ne_two (K := K) hp
  have hσ : IsUnitaryInvolution (unitaryInvolution K p f) :=
    isUnitaryInvolution_unitaryInvolution hK
  have hσσ : ∀ c, unitaryInvolution K p f (unitaryInvolution K p f c) = c :=
    unitaryInvolution_involutive hK
  obtain ⟨t, ht, hts⟩ : ∃ t : K, unitaryInvolution K p f t * t = 1 ∧
      unitaryInvolution K p f t ≠ t := by
    obtain ⟨ζ, hζ0, hζ⟩ := exists_unitaryInvolution_eq_neg hK
    exact exists_norm_one_ne_aux _ h2 hζ0 hζ
  have ht' := hσσ t
  set G : Matrix (Fin 4) (Fin 4) K := (g : Matrix (Fin 4) (Fin 4) K) with hG
  set Gi : Matrix (Fin 4) (Fin 4) K := ((g⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)
    with hGi
  have hGiG : Gi * G = 1 := by rw [hG, hGi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hdet : G.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).mp g.isUnit).ne_zero
  have key : ∀ (r : Su K p f 4) (R R' : Matrix (Fin 4) (Fin 4) K), α r = r → suMat r = R →
      φ.mapMatrix R = R' → G * R' = R * G := by
    intro r R R' hr hR hR'
    have h := hα r
    rw [hr, hR, hR'] at h
    have hGGi : G * Gi = 1 := by rw [hG, hGi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    calc G * R' = G * R' * (Gi * G) := by rw [hGiG, Matrix.mul_one]
      _ = (G * R' * Gi) * G := by simp only [Matrix.mul_assoc]
      _ = R * G := by rw [← h]
  have hd1 : G * !![φ t, 0, 0, 0; 0, φ (unitaryInvolution K p f t), 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] =
      !![t, 0, 0, 0; 0, unitaryInvolution K p f t, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] * G := by
    refine key _ _ _ (hfix0 (dSU K p f ht ht')) ?_ ?_
    · rw [suMat_blockEmb_zero, suMat_dSU]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    · ext i j
      fin_cases i <;> fin_cases j <;> simp
  have hd2 : G * !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, φ t, 0; 0, 0, 0, φ (unitaryInvolution K p f t)] =
      !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, t, 0; 0, 0, 0, unitaryInvolution K p f t] * G := by
    refine key _ _ _ (hfix2 (dSU K p f ht ht')) ?_ ?_
    · rw [suMat_blockEmb_two, suMat_dSU]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    · ext i j
      fin_cases i <;> fin_cases j <;> simp
  have hj1 : G * !![0, 1, 0, 0; -1, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] =
      !![0, 1, 0, 0; -1, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] * G := by
    refine key _ _ _ (hfix0 (jSU K p f)) ?_ ?_
    · rw [suMat_blockEmb_zero, suMat_jSU]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    · ext i j
      fin_cases i <;> fin_cases j <;> simp
  have hj2 : G * !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 1; 0, 0, -1, 0] =
      !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 1; 0, 0, -1, 0] * G := by
    refine key _ _ _ (hfix2 (jSU K p f)) ?_ ?_
    · rw [suMat_blockEmb_two, suMat_jSU]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    · ext i j
      fin_cases i <;> fin_cases j <;> simp
  have hA : ∀ a : K, ∃ b : K,
      G * !![φ a, φ b, 0, 0; -φ (unitaryInvolution K p f b), φ (unitaryInvolution K p f a), 0, 0;
          0, 0, 1, 0; 0, 0, 0, 1] =
        !![a, b, 0, 0; -unitaryInvolution K p f b, unitaryInvolution K p f a, 0, 0;
          0, 0, 1, 0; 0, 0, 0, 1] * G := by
    intro a
    have hfixd : unitaryInvolution K p f (1 - unitaryInvolution K p f a * a) =
        1 - unitaryInvolution K p f a * a := by
      rw [map_sub, map_one, map_mul, hσσ]
      ring
    obtain ⟨b, hb⟩ := hσ.exists_norm hfixd
    have hab : unitaryInvolution K p f a * a + unitaryInvolution K p f b * b = 1 := by
      rw [hb]
      ring
    refine ⟨b, key _ _ _ (hfix0 (aSU K p f hab hσσ)) ?_ ?_⟩
    · rw [suMat_blockEmb_zero, suMat_aSU]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    · ext i j
      fin_cases i <;> fin_cases j <;> simp
  rcases core4 (unitaryInvolution K p f) φ hσσ (u := t) (v := unitaryInvolution K p f t)
      (by rw [mul_comm]; exact ht) hts G hdet hd1 hd2 hj1 hj2 hA with
    ⟨hφ, a, b, ha, hb, hGab⟩ | ⟨hφ, m, n, hm, hn, hGmn⟩
  · subst hφ
    refine sq_of_lift hK α G Gi (RingEquiv.refl K) (fun c => rfl) hGiG hα (mul_ne_zero ha ha)
      (mul_ne_zero hb hb) ?_ hα4
    rw [mapMatrix_refl_four, hGab]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]
  · subst hφ
    have hσm : unitaryInvolution K p f m ≠ 0 := (map_ne_zero _).mpr hm
    have hσn : unitaryInvolution K p f n ≠ 0 := (map_ne_zero _).mpr hn
    refine sq_of_lift hK α G Gi (unitaryInvolution K p f) hσσ hGiG hα
      (neg_ne_zero.mpr (mul_ne_zero hσm hm)) (neg_ne_zero.mpr (mul_ne_zero hσn hn)) ?_ hα4
    rw [hGmn]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_four, RingEquiv.mapMatrix_apply] <;> ring

end Fixing

section Blocks

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem su4_aut_blocks (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) (hq : 5 ≤ p ^ f) {X : Type}
    [Group X] (θ : Su K p f 4 →* X) (hθ : Function.Surjective θ)
    (hker : θ.ker ≤ Subgroup.center (Su K p f 4)) (σ : MulAut X) (hσ4 : σ * σ * (σ * σ) = 1)
    (hfix0 : ∀ A : Su K p f 2, σ (θ (blockEmb K p f 4 2 0 (by norm_num) A)) =
      θ (blockEmb K p f 4 2 0 (by norm_num) A))
    (hfix2 : ∀ A : Su K p f 2, σ (θ (blockEmb K p f 4 2 2 (by norm_num) A)) =
      θ (blockEmb K p f 4 2 2 (by norm_num) A)) :
    σ * σ = 1 ∨ σ * σ = MulAut.conj (θ (rootInvSU K p f (show 2 ≤ 4 by norm_num))) := by
  obtain ⟨α, g, φ, hlift, hmat, -, -⟩ :=
    unitaryAutClassification_isometry_of_card hK hp hq (d := 4) (by norm_num) X θ hθ hker σ
  have : Group.IsPerfect (Su K p f 2) := isPerfect_suTwo_of_card hK hq
  have hαfix0 : ∀ A : Su K p f 2, α (blockEmb K p f 4 2 0 (by norm_num) A) =
      blockEmb K p f 4 2 0 (by norm_num) A := fun A =>
    DFunLike.congr_fun (lift_comp_eq_of_fixed hker hlift (blockEmb K p f 4 2 0 (by norm_num))
      hfix0) A
  have hαfix2 : ∀ A : Su K p f 2, α (blockEmb K p f 4 2 2 (by norm_num) A) =
      blockEmb K p f 4 2 2 (by norm_num) A := fun A =>
    DFunLike.congr_fun (lift_comp_eq_of_fixed hker hlift (blockEmb K p f 4 2 2 (by norm_num))
      hfix2) A
  have h4 : ∀ y, σ (σ (σ (σ y))) = y := fun y => by
    have := congrArg (fun τ : MulAut X => τ y) hσ4
    simpa using this
  have hα4 : ∀ x, α (α (α (α x))) * x⁻¹ ∈ Subgroup.center (Su K p f 4) := by
    intro x
    apply hker
    rw [MonoidHom.mem_ker, map_mul, map_inv, hlift, hlift, hlift, hlift, h4, mul_inv_cancel]
  rcases su4_fixing hK hp α g φ (fun x => hmat x) hαfix0 hαfix2 hα4 with h | h
  · left
    ext y
    obtain ⟨x, rfl⟩ := hθ y
    show σ (σ (θ x)) = θ x
    rw [← hlift x, ← hlift (α x), h x]
  · right
    ext y
    obtain ⟨x, rfl⟩ := hθ y
    show σ (σ (θ x)) = _
    rw [← hlift x, ← hlift (α x), h x]
    simp [map_mul, map_inv]

omit [Finite K] [Fact p.Prime] [CharP K p] in
theorem negBlock_four_two :
    negBlock K 4 2 = !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, -1, 0; 0, 0, 0, -1] := by
  rw [negBlock_eq_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem twin_std_u (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) {R R' : Subgroup (Su K p f 4)}
    (hR : R ∈ longRootSetU (K := K) (p := p) (f := f) (show 2 ≤ 4 by norm_num))
    (hR' : R' ∈ longRootSetU (K := K) (p := p) (f := f) (show 2 ≤ 4 by norm_num))
    (hne : R ≠ R') {x x' : Su K p f 4} (hxR : x ∈ R) (hx2 : x * x = 1) (hx1 : x ≠ 1)
    (hx'R' : x' ∈ R') (hx'2 : x' * x' = 1) (hx'1 : x' ≠ 1)
    (hc : x' * x⁻¹ ∈ Subgroup.center (Su K p f 4)) :
    ∃ g : Su K p f 4,
      R = (blockEmb K p f 4 2 0 (by norm_num)).range.map (MulAut.conj g).toMonoidHom ∧
      R' = (blockEmb K p f 4 2 2 (by norm_num)).range.map (MulAut.conj g).toMonoidHom ∧
      x = g * rootInvSU K p f (show 2 ≤ 4 by norm_num) * g⁻¹ := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_charP_ne_two (K := K) hp
  have hσ : IsUnitaryInvolution (unitaryInvolution K p f) :=
    isUnitaryInvolution_unitaryInvolution hK
  obtain ⟨i, hi⟩ := hR
  obtain ⟨i', hi'⟩ := hR'
  have hxi : x = i := hi.eq_of_orderOf_eq_two hK hp hxR (orderOf_eq_prime (by rwa [pow_two]) hx1)
  have hxi' : x' = i' :=
    hi'.eq_of_orderOf_eq_two hK hp hx'R' (orderOf_eq_prime (by rwa [pow_two]) hx'1)
  have hRlr := hi.eq_longRootGroupSU h2
  have hR'lr := hi'.eq_longRootGroupSU h2
  obtain ⟨g, hRg, hig⟩ := hi
  obtain ⟨r, hr⟩ := exists_scalar_of_mem_center hσ (by norm_num : 3 ≤ 4) hc
  have hr' : suMat (x' * x⁻¹) = Matrix.scalar (Fin 4) (r : K) := hr
  have hxx : suMat x * suMat x = 1 := by rw [← suMat_mul, hx2, suMat_one]
  have hxx' : suMat x' * suMat x' = 1 := by rw [← suMat_mul, hx'2, suMat_one]
  have hx'x : suMat x' = (r : K) • suMat x := by
    calc suMat x' = suMat (x' * x⁻¹) * suMat x := by
          rw [suMat_mul, Matrix.mul_assoc, suMat_inv_mul_suMat, Matrix.mul_one]
      _ = (r : K) • suMat x := by
          rw [hr', Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul,
            Matrix.one_mul]
  have hr2 : (r : K) * r = 1 := by
    have h1 : suMat x' * suMat x' = ((r : K) * r) • (1 : Matrix (Fin 4) (Fin 4) K) := by
      rw [hx'x, Matrix.smul_mul, Matrix.mul_smul, hxx, smul_smul]
    rw [hxx'] at h1
    have := congrFun (congrFun h1 0) 0
    simpa using this.symm
  rcases mul_self_eq_one_iff.mp hr2 with hr1 | hr1
  · exfalso
    apply hne
    have hxx'' : x' = x := by
      apply suMat_injective
      rw [hx'x, hr1, one_smul]
    rw [hRlr, hR'lr, ← hxi, ← hxi', hxx'']
  · refine ⟨g, hRg, ?_, hxi.trans hig⟩
    have hneg : -(!![-1, 0, 0, 0; 0, -1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] :
        Matrix (Fin 4) (Fin 4) K) = !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, -1, 0; 0, 0, 0, -1] := by
      ext a b
      fin_cases a <;> fin_cases b <;> simp
    have hX' : suMat x' = suMat g * negBlock K 4 2 * suMat g⁻¹ := by
      rw [hx'x, hr1, neg_one_smul, hxi, hig, suMat_mul, suMat_mul, suMat_rootInvSU_four,
        negBlock_four_two, ← hneg, Matrix.mul_neg, Matrix.neg_mul]
    rw [hR'lr, ← hxi', hX', longRootGroupSU_conj, range_blockEmb_eq_longRootGroupSU h2]

theorem psu4_autVac (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    {R R' : Subgroup (Su K p f 4)}
    (hR : R ∈ longRootSetU (K := K) (p := p) (f := f) (show 2 ≤ 4 by norm_num))
    (hR' : R' ∈ longRootSetU (K := K) (p := p) (f := f) (show 2 ≤ 4 by norm_num))
    (hne : R ≠ R') {x x' : Su K p f 4} (hxR : x ∈ R) (hx2 : x * x = 1) (hx1 : x ≠ 1)
    (hx'R' : x' ∈ R') (hx'2 : x' * x' = 1) (hx'1 : x' ≠ 1)
    (hc : x' * x⁻¹ ∈ Subgroup.center (Su K p f 4))
    (σ : MulAut (Su K p f 4 ⧸ Subgroup.center (Su K p f 4)))
    (hσ : ∀ r ∈ R, σ (QuotientGroup.mk r) = QuotientGroup.mk r)
    (hσ' : ∀ r ∈ R', σ (QuotientGroup.mk r) = QuotientGroup.mk r)
    (hσ4 : σ * σ * (σ * σ) = 1) :
    σ * σ = 1 ∨ σ * σ = MulAut.conj (QuotientGroup.mk x) := by
  obtain ⟨g, hRg, hR'g, hxg⟩ := twin_std_u hK hp hR hR' hne hxR hx2 hx1 hx'R' hx'2 hx'1 hc
  set θ : Su K p f 4 →* Su K p f 4 ⧸ Subgroup.center (Su K p f 4) := QuotientGroup.mk' _
    with hθ
  set c : MulAut (Su K p f 4 ⧸ Subgroup.center (Su K p f 4)) := MulAut.conj (θ g) with hcdef
  have hcp : ∀ s, c (θ s) = θ (g * s * g⁻¹) := fun s => by
    rw [hcdef, MulAut.conj_apply, map_mul, map_mul, map_inv]
  set σ' : MulAut (Su K p f 4 ⧸ Subgroup.center (Su K p f 4)) := c⁻¹ * σ * c with hσ'def
  have hσ'p : ∀ s, σ' (θ s) = (c⁻¹) (σ (c (θ s))) := fun s => rfl
  have hfixσ' : ∀ (S : Subgroup (Su K p f 4)),
      (∀ r ∈ S.map (MulAut.conj g).toMonoidHom, σ (θ r) = θ r) → ∀ r ∈ S, σ' (θ r) = θ r := by
    intro S hS r hr
    have hmem : g * r * g⁻¹ ∈ S.map (MulAut.conj g).toMonoidHom := ⟨r, hr, rfl⟩
    rw [hσ'p, hcp, hS _ hmem, ← hcp]
    simp
  have hσ4' : σ' * σ' * (σ' * σ') = 1 := by
    calc σ' * σ' * (σ' * σ') = c⁻¹ * (σ * σ * (σ * σ)) * c := by rw [hσ'def]; group
      _ = 1 := by rw [hσ4]; group
  have hfix0 := hfixσ' ((blockEmb K p f 4 2 0 (by norm_num)).range) (hRg ▸ hσ)
  have hfix2 := hfixσ' ((blockEmb K p f 4 2 2 (by norm_num)).range) (hR'g ▸ hσ')
  have hsq : σ * σ = c * (σ' * σ') * c⁻¹ := by rw [hσ'def]; group
  rcases su4_aut_blocks hK hp hq θ (QuotientGroup.mk'_surjective _)
      (by rw [hθ, QuotientGroup.ker_mk']) σ' hσ4' (fun A => hfix0 _ ⟨A, rfl⟩)
      (fun A => hfix2 _ ⟨A, rfl⟩) with h | h
  · left
    rw [hsq, h]
    group
  · right
    rw [hsq, h, hxg]
    have : MulAut.conj (θ (g * rootInvSU K p f (show 2 ≤ 4 by norm_num) * g⁻¹)) =
        c * MulAut.conj (θ (rootInvSU K p f (show 2 ≤ 4 by norm_num))) * c⁻¹ := by
      rw [hcdef]
      simp only [map_mul, map_inv]
    exact this.symm

end Blocks

end CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterU4
