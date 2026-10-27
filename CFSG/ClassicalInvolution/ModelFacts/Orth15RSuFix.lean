module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15RSuMix
public import CFSG.ClassicalInvolution.ModelFacts.Orth15OuterU4

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Orth15.InnerSu

open Matrix CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.ModelFacts.UnitaryAut CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.ClassicalInvolution.ModelFacts.Orth15.ChainU
  CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterU4
  CFSG.ClassicalGroups.Unitary

section Fixing

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem sq_lift_matrix (α : Su K p f 4 →* Su K p f 4) (G Gi : Matrix (Fin 4) (Fin 4) K)
    (φ : K ≃+* K) (hφφ : ∀ c, φ (φ c) = c) (hGiG : Gi * G = 1)
    (hα : ∀ x, suMat (α x) = G * φ.mapMatrix (suMat x) * Gi) {s w : K} (hs : s ≠ 0)
    (hw : w ≠ 0) (hD : G * φ.mapMatrix G = diag4 s w) :
    ∀ x, suMat (α (α x)) = diag4 s w * suMat x * diag4 s⁻¹ w⁻¹ := by
  have hDi : φ.mapMatrix Gi * Gi = diag4 s⁻¹ w⁻¹ := by
    apply inv_of_diag4 hs hw
    rw [← show G * φ.mapMatrix G = !![s, 0, 0, 0; 0, s, 0, 0; 0, 0, w, 0; 0, 0, 0, w] from hD]
    exact inv_sq_matrix φ G Gi hGiG
  intro x
  rw [hα (α x), hα x, alpha_sq_matrix φ hφφ, hD, hDi]

theorem su4_fixing_sq (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) (α : Su K p f 4 →* Su K p f 4)
    (g : GL (Fin 4) K) (φ : K ≃+* K)
    (hα : ∀ x : Su K p f 4, suMat (α x) =
      (g : Matrix (Fin 4) (Fin 4) K) * φ.mapMatrix (suMat x) *
        ((g⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K))
    (hfix0 : ∀ A : Su K p f 2, α (blockEmb K p f 4 2 0 (by norm_num) A) =
      blockEmb K p f 4 2 0 (by norm_num) A)
    (hfix2 : ∀ A : Su K p f 2, α (blockEmb K p f 4 2 2 (by norm_num) A) =
      blockEmb K p f 4 2 2 (by norm_num) A) :
    ∃ s w : K, s ≠ 0 ∧ w ≠ 0 ∧
      ∀ x, suMat (α (α x)) = diag4 s w * suMat x * diag4 s⁻¹ w⁻¹ := by
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
    refine ⟨a * a, b * b, mul_ne_zero ha ha, mul_ne_zero hb hb, ?_⟩
    refine sq_lift_matrix α G Gi (RingEquiv.refl K) (fun c => rfl) hGiG hα (mul_ne_zero ha ha)
      (mul_ne_zero hb hb) ?_
    rw [mapMatrix_refl_four, hGab, diag4]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]
  · subst hφ
    have hσm : unitaryInvolution K p f m ≠ 0 := (map_ne_zero _).mpr hm
    have hσn : unitaryInvolution K p f n ≠ 0 := (map_ne_zero _).mpr hn
    refine ⟨-(unitaryInvolution K p f m * m), -(unitaryInvolution K p f n * n),
      neg_ne_zero.mpr (mul_ne_zero hσm hm), neg_ne_zero.mpr (mul_ne_zero hσn hn), ?_⟩
    refine sq_lift_matrix α G Gi (unitaryInvolution K p f) hσσ hGiG hα
      (neg_ne_zero.mpr (mul_ne_zero hσm hm)) (neg_ne_zero.mpr (mul_ne_zero hσn hn)) ?_
    rw [hGmn, diag4]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_four, RingEquiv.mapMatrix_apply] <;> ring

theorem aut_sq_eq_one (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) (hq : 5 ≤ p ^ f) {X : Type}
    [Group X] (θ : Su K p f 4 →* X) (hθ : Function.Surjective θ)
    (hker : θ.ker ≤ Subgroup.center (Su K p f 4)) (σ : MulAut X)
    (hfix0 : ∀ A : Su K p f 2, σ (θ (blockEmb K p f 4 2 0 (by norm_num) A)) =
      θ (blockEmb K p f 4 2 0 (by norm_num) A))
    (hfix2 : ∀ A : Su K p f 2, σ (θ (blockEmb K p f 4 2 2 (by norm_num) A)) =
      θ (blockEmb K p f 4 2 2 (by norm_num) A))
    {m : Su K p f 4} (hmix : MixProp (suMat m)) (hm : σ (θ m) = θ m) : σ * σ = 1 := by
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
  have hα2 : ∀ x : Su K p f 4, suMat (α x) =
      (g : Matrix (Fin 4) (Fin 4) K) * φ.mapMatrix (suMat x) *
        ((g⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := fun x => hmat x
  obtain ⟨s, w, hs, hw, hsq⟩ := su4_fixing_sq hK hp α g φ hα2 hαfix0 hαfix2
  have hσ' : IsUnitaryInvolution (unitaryInvolution K p f) :=
    isUnitaryInvolution_unitaryInvolution hK
  have hcen : α m * m⁻¹ ∈ Subgroup.center (Su K p f 4) := by
    apply hker
    rw [MonoidHom.mem_ker, map_mul, map_inv, hlift, hm, mul_inv_cancel]
  obtain ⟨c, hc⟩ := exists_scalar_of_mem_center hσ' (by norm_num : 3 ≤ 4) hcen
  have hc' : suMat (α m * m⁻¹) = Matrix.scalar (Fin 4) (c : K) := hc
  have hαm : suMat (α m) = (c : K) • suMat m := by
    have h1 : α m = (α m * m⁻¹) * m := by group
    rw [h1, suMat_mul, hc', Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul,
      Matrix.one_mul]
  have hD : suMat (α (α m)) = (φ (c : K) * c) • suMat m := by
    have e : φ.mapMatrix ((c : K) • suMat m) = φ (c : K) • φ.mapMatrix (suMat m) := by
      ext i j
      simp [RingEquiv.mapMatrix_apply]
    rw [hα2 (α m), hαm, e, Matrix.mul_smul, Matrix.smul_mul, ← hα2 m, hαm, smul_smul]
  have hDD : diag4 s⁻¹ w⁻¹ * diag4 s w = 1 := by
    rw [diag4, diag4]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four] <;> field_simp
  have hcomm : diag4 s w * suMat m = (φ (c : K) * c) • (suMat m * diag4 s w) := by
    calc diag4 s w * suMat m = diag4 s w * suMat m * (diag4 s⁻¹ w⁻¹ * diag4 s w) := by
          rw [hDD, Matrix.mul_one]
      _ = (diag4 s w * suMat m * diag4 s⁻¹ w⁻¹) * diag4 s w := by simp only [Matrix.mul_assoc]
      _ = ((φ (c : K) * c) • suMat m) * diag4 s w := by rw [← hsq m, hD]
      _ = (φ (c : K) * c) • (suMat m * diag4 s w) := by rw [Matrix.smul_mul]
  have hsw : s = w := hmix s w hs hw _ hcomm
  subst hsw
  have hid : ∀ x, α (α x) = x := fun x =>
    suMat_injective (by rw [hsq x]; exact conj_scalar4 hs (suMat x))
  ext y
  obtain ⟨x, rfl⟩ := hθ y
  show σ (σ (θ x)) = θ x
  rw [← hlift x, ← hlift (α x), hid x]

end Fixing

end CFSG.ClassicalInvolution.ModelFacts.Orth15.InnerSu
