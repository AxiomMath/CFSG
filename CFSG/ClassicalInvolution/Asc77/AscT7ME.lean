module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15OuterU4

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterU4

open Matrix CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.ModelFacts.UnitaryAut CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.ClassicalInvolution.ModelFacts.Orth15.ChainU
  CFSG.ClassicalGroups.Unitary

section Fixing

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

omit [Finite K] [Fact p.Prime] [CharP K p] in
theorem antidiag_mul_map (σ : K ≃+* K) (m n : K) :
    (!![0, m, 0, 0; -m, 0, 0, 0; 0, 0, 0, n; 0, 0, -n, 0] : Matrix (Fin 4) (Fin 4) K) *
      σ.mapMatrix (!![0, m, 0, 0; -m, 0, 0, 0; 0, 0, 0, n; 0, 0, -n, 0] :
        Matrix (Fin 4) (Fin 4) K) =
      !![-(σ m * m), 0, 0, 0; 0, -(σ m * m), 0, 0; 0, 0, -(σ n * n), 0; 0, 0, 0, -(σ n * n)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, RingEquiv.mapMatrix_apply] <;> ring

theorem su4_fixing_sq (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) (α : Su K p f 4 →* Su K p f 4)
    (g : GL (Fin 4) K) (φ : K ≃+* K)
    (hα : ∀ x : Su K p f 4, suMat (α x) =
      (g : Matrix (Fin 4) (Fin 4) K) * φ.mapMatrix (suMat x) *
        ((g⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K))
    (hiso : ((g : Matrix (Fin 4) (Fin 4) K).map (unitaryInvolution K p f))ᵀ *
      (g : Matrix (Fin 4) (Fin 4) K) = 1)
    (hfix0 : ∀ A : Su K p f 2, α (blockEmb K p f 4 2 0 (by norm_num) A) =
      blockEmb K p f 4 2 0 (by norm_num) A)
    (hfix2 : ∀ A : Su K p f 2, α (blockEmb K p f 4 2 2 (by norm_num) A) =
      blockEmb K p f 4 2 2 (by norm_num) A)
    (hsq : ∀ x, α (α x) * (rootInvSU K p f (show 2 ≤ 4 by norm_num) * x *
      (rootInvSU K p f (show 2 ≤ 4 by norm_num))⁻¹)⁻¹ ∈ Subgroup.center (Su K p f 4)) :
    ∃ ι : K, ι * ι = -1 ∧ unitaryInvolution K p f ι * ι = 1 := by
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
  obtain ⟨c, hc⟩ := exists_scalar_of_mem_center hσ (by norm_num : 3 ≤ 4)
    (hsq (mixSU K p f))
  have e0 : suMat (α (α (mixSU K p f)) * (rootInvSU K p f (show 2 ≤ 4 by norm_num) *
      mixSU K p f * (rootInvSU K p f (show 2 ≤ 4 by norm_num))⁻¹)⁻¹) =
        Matrix.scalar (Fin 4) (c : K) := hc
  have h2' : suMat (α (α (mixSU K p f))) = (c : K) •
      (!![0, 0, -1, 0; 0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1] : Matrix (Fin 4) (Fin 4) K) := by
    have hx : suMat (rootInvSU K p f (show 2 ≤ 4 by norm_num) * mixSU K p f *
        (rootInvSU K p f (show 2 ≤ 4 by norm_num))⁻¹) =
        !![0, 0, -1, 0; 0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1] := by
      rw [suMat_mul, suMat_mul, suMat_rootInvSU_inv_four, suMat_rootInvSU_four, suMat_mixSU]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]
    calc suMat (α (α (mixSU K p f))) = suMat (α (α (mixSU K p f)) *
          (rootInvSU K p f (show 2 ≤ 4 by norm_num) * mixSU K p f *
            (rootInvSU K p f (show 2 ≤ 4 by norm_num))⁻¹)⁻¹) *
          suMat (rootInvSU K p f (show 2 ≤ 4 by norm_num) * mixSU K p f *
            (rootInvSU K p f (show 2 ≤ 4 by norm_num))⁻¹) := by
          rw [suMat_mul, Matrix.mul_assoc, suMat_inv_mul_suMat, Matrix.mul_one]
      _ = _ := by
          rw [e0, hx, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul,
            Matrix.one_mul]
  rcases core4 (unitaryInvolution K p f) φ hσσ (u := t) (v := unitaryInvolution K p f t)
      (by rw [mul_comm]; exact ht) hts G hdet hd1 hd2 hj1 hj2 hA with
    ⟨hφ, a, b, ha, hb, hGab⟩ | ⟨hφ, m, n, hm, hn, hGmn⟩
  · subst hφ
    have hGi : Gi = !![a⁻¹, 0, 0, 0; 0, a⁻¹, 0, 0; 0, 0, b⁻¹, 0; 0, 0, 0, b⁻¹] :=
      inv_of_diag4 ha hb Gi (by rw [← hGab]; exact hGiG)
    have h1 : suMat (α (α (mixSU K p f))) = G * (G * suMat (mixSU K p f) * Gi) * Gi := by
      rw [hα (α _), hα _, mapMatrix_refl_four, mapMatrix_refl_four]
    rw [h1, hGab, hGi, suMat_mixSU] at h2'
    have e := congrFun (congrFun h2' 0) 2
    have e' := congrFun (congrFun h2' 1) 1
    simp [Matrix.mul_apply, Fin.sum_univ_four] at e e'
    have hc1 : (c : K) = 1 := by
      field_simp at e'
      linear_combination -e'
    have n0 : unitaryInvolution K p f a * a = 1 := by
      have := congrFun (congrFun hiso 0) 0
      rw [hGab] at this
      simpa [Matrix.mul_apply, Fin.sum_univ_four] using this
    have n2 : unitaryInvolution K p f b * b = 1 := by
      have := congrFun (congrFun hiso 2) 2
      rw [hGab] at this
      simpa [Matrix.mul_apply, Fin.sum_univ_four] using this
    refine ⟨a * b⁻¹, ?_, ?_⟩
    · rw [hc1] at e
      linear_combination e
    · rw [map_mul, map_inv₀]
      calc unitaryInvolution K p f a * (unitaryInvolution K p f b)⁻¹ * (a * b⁻¹)
          = (unitaryInvolution K p f a * a) * ((unitaryInvolution K p f b * b)⁻¹) := by
            field_simp
        _ = 1 := by rw [n0, n2]; simp
  · exfalso
    subst hφ
    have h1 : suMat (α (α (mixSU K p f))) = (G * (unitaryInvolution K p f).mapMatrix G) *
        suMat (mixSU K p f) * ((unitaryInvolution K p f).mapMatrix Gi * Gi) := by
      rw [hα (α _), hα _, alpha_sq_matrix _ hσσ]
    have hGsq : G * (unitaryInvolution K p f).mapMatrix G = -1 := by
      have hn0 : unitaryInvolution K p f m * m = 1 := by
        have := congrFun (congrFun hiso 0) 0
        rw [hGmn] at this
        simpa [Matrix.mul_apply, Fin.sum_univ_four] using this
      have hn2 : unitaryInvolution K p f n * n = 1 := by
        have := congrFun (congrFun hiso 2) 2
        rw [hGmn] at this
        simpa [Matrix.mul_apply, Fin.sum_univ_four] using this
      rw [hGmn, antidiag_mul_map _ m n, hn0, hn2]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    have hGisq : (unitaryInvolution K p f).mapMatrix Gi * Gi = -1 := by
      have h3 := inv_sq_matrix (unitaryInvolution K p f) G Gi hGiG
      rw [hGsq] at h3
      calc (unitaryInvolution K p f).mapMatrix Gi * Gi
          = ((unitaryInvolution K p f).mapMatrix Gi * Gi) * (-1) * (-1) := by simp
        _ = 1 * (-1) := by rw [h3]
        _ = -1 := by simp
    rw [h1, hGsq, hGisq, suMat_mixSU] at h2'
    have e := congrFun (congrFun h2' 0) 2
    have e' := congrFun (congrFun h2' 1) 1
    simp [Matrix.mul_apply, Fin.sum_univ_four] at e e'
    apply h2
    linear_combination e + e'

end Fixing

section Blocks

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem su4_aut_blocks_sq (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) (hq : 5 ≤ p ^ f) {X : Type}
    [Group X] (θ : Su K p f 4 →* X) (hθ : Function.Surjective θ)
    (hker : θ.ker ≤ Subgroup.center (Su K p f 4)) (σ : MulAut X)
    (hfix0 : ∀ A : Su K p f 2, σ (θ (blockEmb K p f 4 2 0 (by norm_num) A)) =
      θ (blockEmb K p f 4 2 0 (by norm_num) A))
    (hfix2 : ∀ A : Su K p f 2, σ (θ (blockEmb K p f 4 2 2 (by norm_num) A)) =
      θ (blockEmb K p f 4 2 2 (by norm_num) A))
    (hσ2 : σ * σ = MulAut.conj (θ (rootInvSU K p f (show 2 ≤ 4 by norm_num)))) :
    ∃ ι : K, ι * ι = -1 ∧ unitaryInvolution K p f ι * ι = 1 := by
  obtain ⟨α, g, φ, hlift, hmat, hiso, -⟩ :=
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
  have hsq : ∀ x, α (α x) * (rootInvSU K p f (show 2 ≤ 4 by norm_num) * x *
      (rootInvSU K p f (show 2 ≤ 4 by norm_num))⁻¹)⁻¹ ∈ Subgroup.center (Su K p f 4) := by
    intro x
    apply hker
    rw [MonoidHom.mem_ker, map_mul, map_inv, hlift, hlift]
    have h1 := DFunLike.congr_fun hσ2 (θ x)
    rw [MulAut.mul_apply, MulAut.conj_apply] at h1
    rw [show σ (σ (θ x)) = _ from h1]
    simp [map_mul, map_inv]
  exact su4_fixing_sq hK hp α g φ (fun x => hmat x) hiso hαfix0 hαfix2 hsq

theorem psu4_autSq (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    {R R' : Subgroup (Su K p f 4)}
    (hR : R ∈ longRootSetU (K := K) (p := p) (f := f) (show 2 ≤ 4 by norm_num))
    (hR' : R' ∈ longRootSetU (K := K) (p := p) (f := f) (show 2 ≤ 4 by norm_num))
    (hne : R ≠ R') {x x' : Su K p f 4} (hxR : x ∈ R) (hx2 : x * x = 1) (hx1 : x ≠ 1)
    (hx'R' : x' ∈ R') (hx'2 : x' * x' = 1) (hx'1 : x' ≠ 1)
    (hc : x' * x⁻¹ ∈ Subgroup.center (Su K p f 4))
    (σ : MulAut (Su K p f 4 ⧸ Subgroup.center (Su K p f 4)))
    (hσ : ∀ r ∈ R, σ (QuotientGroup.mk r) = QuotientGroup.mk r)
    (hσ' : ∀ r ∈ R', σ (QuotientGroup.mk r) = QuotientGroup.mk r)
    (hσ2 : σ * σ = MulAut.conj (QuotientGroup.mk x)) :
    ∃ ι : K, ι * ι = -1 ∧ unitaryInvolution K p f ι * ι = 1 := by
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
  have hfix0 := hfixσ' ((blockEmb K p f 4 2 0 (by norm_num)).range) (hRg ▸ hσ)
  have hfix2 := hfixσ' ((blockEmb K p f 4 2 2 (by norm_num)).range) (hR'g ▸ hσ')
  have hconj : MulAut.conj (θ (g * rootInvSU K p f (show 2 ≤ 4 by norm_num) * g⁻¹)) =
      c * MulAut.conj (θ (rootInvSU K p f (show 2 ≤ 4 by norm_num))) * c⁻¹ := by
    rw [hcdef]
    simp only [map_mul, map_inv]
  have hσ'2 : σ' * σ' = MulAut.conj (θ (rootInvSU K p f (show 2 ≤ 4 by norm_num))) := by
    have h1 : σ' * σ' = c⁻¹ * (σ * σ) * c := by rw [hσ'def]; group
    rw [h1, hσ2]
    have h2 : MulAut.conj (QuotientGroup.mk x :
        Su K p f 4 ⧸ Subgroup.center (Su K p f 4)) = MulAut.conj (θ x) := rfl
    rw [h2, hxg, hconj]
    group
  exact su4_aut_blocks_sq hK hp hq θ (QuotientGroup.mk'_surjective _)
    (by rw [hθ, QuotientGroup.ker_mk']) σ' (fun A => hfix0 _ ⟨A, rfl⟩)
    (fun A => hfix2 _ ⟨A, rfl⟩) hσ'2

end Blocks

end CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterU4
