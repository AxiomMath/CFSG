module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15OuterU4

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Model1520U

open Matrix CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.ModelFacts.UnitaryAut CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.ClassicalInvolution.ModelFacts.Orth15.ChainU
  CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterU4 CFSG.ClassicalGroups.Unitary

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem iter_mix (β : Su K p f 4 →* Su K p f 4) {s w : K} (hs : s ≠ 0) (hw : w ≠ 0)
    (hβ : ∀ x, suMat (β x) =
      !![s, 0, 0, 0; 0, s, 0, 0; 0, 0, w, 0; 0, 0, 0, w] * suMat x *
        !![s⁻¹, 0, 0, 0; 0, s⁻¹, 0, 0; 0, 0, w⁻¹, 0; 0, 0, 0, w⁻¹]) (n : ℕ) :
    suMat ((⇑β)^[n] (mixSU K p f)) =
      !![0, 0, (s * w⁻¹) ^ n, 0; 0, 1, 0, 0; -((s * w⁻¹) ^ n)⁻¹, 0, 0, 0; 0, 0, 0, 1] := by
  induction n with
  | zero =>
    rw [Function.iterate_zero_apply, suMat_mixSU]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', hβ, ih]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_four, pow_succ, mul_comm, mul_assoc] <;> field_simp

theorem sq_of_diag4_odd (hK : Nat.card K = (p ^ f) ^ 2) (h3 : p ^ f = 3) (β : Su K p f 4 →* Su K p f 4) {s w : K}
    (hs : s ≠ 0) (hw : w ≠ 0)
    (hβ : ∀ x, suMat (β x) =
      !![s, 0, 0, 0; 0, s, 0, 0; 0, 0, w, 0; 0, 0, 0, w] * suMat x *
        !![s⁻¹, 0, 0, 0; 0, s⁻¹, 0, 0; 0, 0, w⁻¹, 0; 0, 0, 0, w⁻¹]) {m : ℕ} (hm : Odd m)
    (hβm : ∀ x, (⇑β)^[m] x * x⁻¹ ∈ Subgroup.center (Su K p f 4)) : ∀ x, β x = x := by
  have hσ : IsUnitaryInvolution (unitaryInvolution K p f) :=
    isUnitaryInvolution_unitaryInvolution hK
  obtain ⟨c, hc⟩ := exists_scalar_of_mem_center hσ (by norm_num : 3 ≤ 4) (hβm (mixSU K p f))
  have e : suMat ((⇑β)^[m] (mixSU K p f) * (mixSU K p f)⁻¹) = Matrix.scalar (Fin 4) (c : K) := hc
  have e2 : suMat ((⇑β)^[m] (mixSU K p f)) =
      Matrix.scalar (Fin 4) (c : K) * suMat (mixSU K p f) := by
    calc suMat ((⇑β)^[m] (mixSU K p f)) =
        suMat ((⇑β)^[m] (mixSU K p f) * (mixSU K p f)⁻¹) * suMat (mixSU K p f) := by
          rw [suMat_mul, Matrix.mul_assoc, suMat_inv_mul_suMat, Matrix.mul_one]
      _ = _ := by rw [e]
  have h1 : suMat ((⇑β)^[m] (mixSU K p f)) = (c : K) • suMat (mixSU K p f) := by
    rw [e2, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul, Matrix.one_mul]
  rw [iter_mix β hs hw hβ m, suMat_mixSU] at h1
  have e11 := congrFun (congrFun h1 1) 1
  have e02 := congrFun (congrFun h1 0) 2
  simp at e11 e02
  have hc1 : (c : K) = 1 := by simpa using e11.symm
  have hu : (s * w⁻¹) ^ m = 1 := by rw [e02, hc1]
  have hu0 : s * w⁻¹ ≠ 0 := mul_ne_zero hs (inv_ne_zero hw)
  have hu8 : (s * w⁻¹) ^ 8 = 1 := by
    have := Fintype.ofFinite K
    have hcard : Fintype.card K = 9 := by rw [← Nat.card_eq_fintype_card, hK, h3]; norm_num
    have h := FiniteField.pow_card_sub_one_eq_one (s * w⁻¹) hu0
    rwa [hcard] at h
  have hg : (s * w⁻¹) ^ Nat.gcd m 8 = 1 := pow_gcd_eq_one.mpr ⟨hu, hu8⟩
  have hcop : Nat.gcd m 8 = 1 := Nat.Coprime.pow_right 3 (Odd.coprime_two_right hm)
  rw [hcop, pow_one] at hg
  have hsw : s = w := by
    have : s = s * w⁻¹ * w := by field_simp
    rw [this, hg, one_mul]
  subst hsw
  intro x
  apply suMat_injective
  rw [hβ x]
  exact conj_scalar4 hs (suMat x)


theorem sq_of_lift_odd (hK : Nat.card K = (p ^ f) ^ 2) (h3 : p ^ f = 3) (α : Su K p f 4 →* Su K p f 4)
    (G Gi : Matrix (Fin 4) (Fin 4) K) (φ : K ≃+* K) (hφφ : ∀ c, φ (φ c) = c)
    (hGiG : Gi * G = 1) (hα : ∀ x, suMat (α x) = G * φ.mapMatrix (suMat x) * Gi) {s w : K}
    (hs : s ≠ 0) (hw : w ≠ 0)
    (hD : G * φ.mapMatrix G = !![s, 0, 0, 0; 0, s, 0, 0; 0, 0, w, 0; 0, 0, 0, w])
    {m : ℕ} (hm : Odd m)
    (hαm : ∀ x, (⇑(α.comp α))^[m] x * x⁻¹ ∈ Subgroup.center (Su K p f 4)) :
    ∀ x, α (α x) = x := by
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
  exact sq_of_diag4_odd hK h3 (α.comp α) hs hw hβ hm hαm


theorem su4_fixing_odd (hK : Nat.card K = (p ^ f) ^ 2) (h3 : p ^ f = 3) (hp : p ≠ 2) (α : Su K p f 4 →* Su K p f 4)
    (g : GL (Fin 4) K) (φ : K ≃+* K)
    (hα : ∀ x : Su K p f 4, suMat (α x) =
      (g : Matrix (Fin 4) (Fin 4) K) * φ.mapMatrix (suMat x) *
        ((g⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K))
    (hfix0 : ∀ A : Su K p f 2, α (blockEmb K p f 4 2 0 (by norm_num) A) =
      blockEmb K p f 4 2 0 (by norm_num) A)
    (hfix2 : ∀ A : Su K p f 2, α (blockEmb K p f 4 2 2 (by norm_num) A) =
      blockEmb K p f 4 2 2 (by norm_num) A)
    {m : ℕ} (hm : Odd m)
    (hαm : ∀ x, (⇑(α.comp α))^[m] x * x⁻¹ ∈ Subgroup.center (Su K p f 4)) :
    ∀ x, α (α x) = x := by
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
    ⟨hφ, a, b, ha, hb, hGab⟩ | ⟨hφ, m', n', hm', hn', hGmn⟩
  · subst hφ
    refine sq_of_lift_odd hK h3 α G Gi (RingEquiv.refl K) (fun c => rfl) hGiG hα (mul_ne_zero ha ha)
      (mul_ne_zero hb hb) ?_ hm hαm
    rw [mapMatrix_refl_four, hGab]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]
  · subst hφ
    have hσm : unitaryInvolution K p f m' ≠ 0 := (map_ne_zero _).mpr hm'
    have hσn : unitaryInvolution K p f n' ≠ 0 := (map_ne_zero _).mpr hn'
    refine sq_of_lift_odd hK h3 α G Gi (unitaryInvolution K p f) hσσ hGiG hα
      (neg_ne_zero.mpr (mul_ne_zero hσm hm')) (neg_ne_zero.mpr (mul_ne_zero hσn hn')) ?_ hm hαm
    rw [hGmn]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_four, RingEquiv.mapMatrix_apply] <;> ring


end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Model1520U
