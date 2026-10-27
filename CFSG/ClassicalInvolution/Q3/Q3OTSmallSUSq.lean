module

public import CFSG.ClassicalInvolution.Asc77.AscT7MX
public import CFSG.ClassicalInvolution.Q3.Q3URPat
public import CFSG.ClassicalInvolution.Asc77.AscT7MS

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3OT

open Matrix CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.ModelFacts.UnitaryAut CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.ClassicalInvolution.ModelFacts.Orth15.ChainU
  CFSG.ClassicalGroups.Unitary CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterU4
  CFSG.ClassicalInvolution.ModelFacts.Orth15.SqU4 CFSG.ClassicalInvolution.ModelFacts.Orth15

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem su4_sq_blocks3 (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) (hf : 1 ≤ f)
    (hcop : ∀ z ∈ Subgroup.center (Su K p f 4), ¬ 3 ∣ orderOf z)
    (hL : ∀ l : Su K p f 2, l ^ 3 ∈ ⁅(⊤ : Subgroup (Su K p f 2)), (⊤ : Subgroup (Su K p f 2))⁆)
    (φ : MulAut (PU K p f))
    (hfix0 : ∀ A : Su K p f 2, φ (QuotientGroup.mk (blockEmb K p f 4 2 0 (by norm_num) A)) =
      QuotientGroup.mk (blockEmb K p f 4 2 0 (by norm_num) A))
    (hfix2 : ∀ A : Su K p f 2, φ (QuotientGroup.mk (blockEmb K p f 4 2 2 (by norm_num) A)) =
      QuotientGroup.mk (blockEmb K p f 4 2 2 (by norm_num) A))
    (hφ2 : φ * φ =
      MulAut.conj (QuotientGroup.mk (rootInvSU K p f (show 2 ≤ 4 by norm_num)) : PU K p f)) :
    ∃ a b : K, a ≠ 0 ∧ b ≠ 0 ∧ unitaryInvolution K p f a * a = 1 ∧
      unitaryInvolution K p f b * b = 1 ∧ a * a = -(b * b) ∧
      ActsAsM φ (!![a, 0, 0, 0; 0, a, 0, 0; 0, 0, b, 0; 0, 0, 0, b] : Matrix (Fin 4) (Fin 4) K)
        !![a⁻¹, 0, 0, 0; 0, a⁻¹, 0, 0; 0, 0, b⁻¹, 0; 0, 0, 0, b⁻¹] := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_charP_ne_two (K := K) hp
  have hσ : IsUnitaryInvolution (unitaryInvolution K p f) :=
    isUnitaryInvolution_unitaryInvolution hK
  have hσσ : ∀ c, unitaryInvolution K p f (unitaryInvolution K p f c) = c :=
    unitaryInvolution_involutive hK
  set θ : Su K p f 4 →* Su K p f 4 ⧸ Subgroup.center (Su K p f 4) := QuotientGroup.mk' _
    with hθ
  have hker : θ.ker ≤ Subgroup.center (Su K p f 4) := by rw [hθ, QuotientGroup.ker_mk']
  obtain ⟨α, g, ψ, hlift, hmat, hiso, -⟩ :=
    Q3NT.unitaryAutClassification_isometry_of_odd hK hp hf (d := 4) (by norm_num) _ θ
      (QuotientGroup.mk'_surjective _) hker φ
  have hcop' : ∀ x ∈ θ.ker, ¬ 3 ∣ orderOf x := fun x hx => hcop x (hker hx)
  have hfixα : ∀ (i : ℕ) (hi : i + 2 ≤ 4),
      (∀ A : Su K p f 2, φ (θ (blockEmb K p f 4 2 i hi A)) = θ (blockEmb K p f 4 2 i hi A)) →
      ∀ A : Su K p f 2, α (blockEmb K p f 4 2 i hi A) = blockEmb K p f 4 2 i hi A := by
    intro i hi hfix A
    have := Q3.Q3W.hom_eq_of_central_ker3_gen θ hker hcop' hL
      (α.comp (blockEmb K p f 4 2 i hi)) (blockEmb K p f 4 2 i hi) (fun l => by
        rw [MonoidHom.comp_apply, hlift, hfix l])
    exact DFunLike.congr_fun this A
  have hαfix0 : ∀ A : Su K p f 2, α (blockEmb K p f 4 2 0 (by norm_num) A) =
      blockEmb K p f 4 2 0 (by norm_num) A := hfixα 0 (by norm_num) hfix0
  have hαfix2 : ∀ A : Su K p f 2, α (blockEmb K p f 4 2 2 (by norm_num) A) =
      blockEmb K p f 4 2 2 (by norm_num) A := hfixα 2 (by norm_num) hfix2
  have hsq : ∀ x, α (α x) * (rootInvSU K p f (show 2 ≤ 4 by norm_num) * x *
      (rootInvSU K p f (show 2 ≤ 4 by norm_num))⁻¹)⁻¹ ∈ Subgroup.center (Su K p f 4) := by
    intro x
    apply hker
    rw [MonoidHom.mem_ker, map_mul, map_inv, hlift, hlift]
    have h1 := DFunLike.congr_fun hφ2 (θ x)
    rw [MulAut.mul_apply, MulAut.conj_apply] at h1
    rw [show φ (φ (θ x)) = _ from h1]
    simp [hθ, map_mul, map_inv]
  set G : Matrix (Fin 4) (Fin 4) K := (g : Matrix (Fin 4) (Fin 4) K) with hG
  set Gi : Matrix (Fin 4) (Fin 4) K := ((g⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)
    with hGi
  have hGiG : Gi * G = 1 := by rw [hG, hGi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hα' : ∀ x : Su K p f 4, suMat (α x) = G * ψ.mapMatrix (suMat x) * Gi := fun x => hmat x
  obtain ⟨c, hc⟩ := exists_scalar_of_mem_center hσ (by norm_num : 3 ≤ 4) (hsq (mixSU K p f))
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
  rcases su4_core_cases hK hp α g ψ (fun x => hmat x) hαfix0 hαfix2 with
    ⟨hψ, a, b, ha, hb, hGab⟩ | ⟨hψ, m, n, hm, hn, hGmn⟩
  · subst hψ
    rw [← hG] at hGab
    have hGi' : Gi = !![a⁻¹, 0, 0, 0; 0, a⁻¹, 0, 0; 0, 0, b⁻¹, 0; 0, 0, 0, b⁻¹] :=
      inv_of_diag4 ha hb Gi (by rw [← hGab]; exact hGiG)
    have n0 : unitaryInvolution K p f a * a = 1 := by
      have := congrFun (congrFun hiso 0) 0
      rw [hGab] at this
      simpa [Matrix.mul_apply, Fin.sum_univ_four] using this
    have n2 : unitaryInvolution K p f b * b = 1 := by
      have := congrFun (congrFun hiso 2) 2
      rw [hGab] at this
      simpa [Matrix.mul_apply, Fin.sum_univ_four] using this
    have h1 : suMat (α (α (mixSU K p f))) = G * (G * suMat (mixSU K p f) * Gi) * Gi := by
      rw [hα' (α _), hα' _, mapMatrix_refl_four, mapMatrix_refl_four]
    rw [h1, hGab, hGi', suMat_mixSU] at h2'
    have e := congrFun (congrFun h2' 0) 2
    have e' := congrFun (congrFun h2' 1) 1
    simp [Matrix.mul_apply, Fin.sum_univ_four] at e e'
    have hc1 : (c : K) = 1 := by
      rw [← e']
      field_simp
    rw [hc1] at e
    have hab : a * a = -(b * b) := by
      field_simp at e
      linear_combination e
    refine ⟨a, b, ha, hb, n0, n2, hab, ?_, ?_, fun h => ⟨α h, (hlift h).symm, ?_⟩⟩
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four, ha, hb]
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four, ha, hb]
    · rw [hα' h, mapMatrix_refl_four, hGab, hGi']
  · exfalso
    subst hψ
    rw [← hG] at hGmn
    have hn0 : unitaryInvolution K p f m * m = 1 := by
      have := congrFun (congrFun hiso 0) 0
      rw [hGmn] at this
      simpa [Matrix.mul_apply, Fin.sum_univ_four] using this
    have hn2 : unitaryInvolution K p f n * n = 1 := by
      have := congrFun (congrFun hiso 2) 2
      rw [hGmn] at this
      simpa [Matrix.mul_apply, Fin.sum_univ_four] using this
    have h1 : suMat (α (α (mixSU K p f))) = (G * (unitaryInvolution K p f).mapMatrix G) *
        suMat (mixSU K p f) * ((unitaryInvolution K p f).mapMatrix Gi * Gi) := by
      rw [hα' (α _), hα' _, alpha_sq_matrix _ hσσ]
    have hGsq : G * (unitaryInvolution K p f).mapMatrix G = -1 := by
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


theorem twin_std_ku3 (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2)
    {R R' : Subgroup (Su K p f 4)}
    (hR : R ∈ longRootSetU (K := K) (p := p) (f := f) (show 2 ≤ 4 by norm_num))
    (hR' : R' ∈ longRootSetU (K := K) (p := p) (f := f) (show 2 ≤ 4 by norm_num))
    (hne : R ≠ R') {x x' : Su K p f 4} (hxR : x ∈ R) (hx2 : x * x = 1) (hx1 : x ≠ 1)
    (hx'R' : x' ∈ R') (hx'2 : x' * x' = 1) (hx'1 : x' ≠ 1)
    (hc : x' * x⁻¹ ∈ Subgroup.center (Su K p f 4)) {k : Su K p f 4} (hkR : k ∈ R)
    (hkk : (QuotientGroup.mk k : PU K p f) * QuotientGroup.mk k = QuotientGroup.mk x) :
    ∃ g : Su K p f 4,
      R = (blockEmb K p f 4 2 0 (by norm_num)).range.map (MulAut.conj g).toMonoidHom ∧
      R' = (blockEmb K p f 4 2 2 (by norm_num)).range.map (MulAut.conj g).toMonoidHom ∧
      x = g * rootInvSU K p f (show 2 ≤ 4 by norm_num) * g⁻¹ ∧
      k = g * blockEmb K p f 4 2 0 (by norm_num) (jSU K p f) * g⁻¹ := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_charP_ne_two (K := K) hp
  obtain ⟨g, hRg, hR'g, hxg⟩ := twin_std_u hK hp hR hR' hne hxR hx2 hx1 hx'R' hx'2 hx'1 hc
  have hkR' := hkR
  rw [hRg] at hkR'
  obtain ⟨k₀, hk₀, hkeq⟩ := hkR'
  obtain ⟨k₂, rfl⟩ := hk₀
  have hk : k = g * blockEmb K p f 4 2 0 (by norm_num) k₂ * g⁻¹ := by
    rw [← hkeq]
    rfl
  have hk0sq : (QuotientGroup.mk (blockEmb K p f 4 2 0 (by norm_num) k₂ *
      blockEmb K p f 4 2 0 (by norm_num) k₂) : PU K p f) =
      QuotientGroup.mk (rootInvSU K p f (show 2 ≤ 4 by norm_num)) := by
    rw [hk, hxg] at hkk
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] at hkk ⊢
    have h3 : (QuotientGroup.mk g : PU K p f) * (QuotientGroup.mk
        (blockEmb K p f 4 2 0 (by norm_num) k₂) * QuotientGroup.mk
        (blockEmb K p f 4 2 0 (by norm_num) k₂)) * (QuotientGroup.mk g)⁻¹ =
        QuotientGroup.mk g * QuotientGroup.mk (rootInvSU K p f (show 2 ≤ 4 by norm_num)) *
          (QuotientGroup.mk g)⁻¹ := by
      rw [← hkk]
      group
    exact mul_left_cancel (mul_right_cancel h3)
  have hz := QuotientGroup.eq.mp hk0sq
  obtain ⟨c, hc'⟩ := exists_scalar_of_mem_center
    (isUnitaryInvolution_unitaryInvolution hK) (by norm_num : 3 ≤ 4) hz
  set k0 : Su K p f 4 := blockEmb K p f 4 2 0 (by norm_num) k₂ with hk0
  have hx0M : suMat (rootInvSU K p f (show 2 ≤ 4 by norm_num)) = (c : K) • suMat (k0 * k0) := by
    have hc'' : suMat ((k0 * k0)⁻¹ * rootInvSU K p f (show 2 ≤ 4 by norm_num)) =
        Matrix.scalar (Fin 4) (c : K) := hc'
    calc suMat (rootInvSU K p f (show 2 ≤ 4 by norm_num)) =
        suMat (k0 * k0) * suMat ((k0 * k0)⁻¹ * rootInvSU K p f (show 2 ≤ 4 by norm_num)) := by
          rw [suMat_mul (k0 * k0)⁻¹, ← Matrix.mul_assoc, suMat_mul_suMat_inv, Matrix.one_mul]
      _ = (c : K) • suMat (k0 * k0) := by
          rw [hc'', Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul,
            Matrix.mul_one]
  have hc1 : (c : K) = 1 := by
    have e := congrFun (congrFun hx0M 2) 2
    rw [suMat_rootInvSU_four, suMat_mul, hk0, suMat_blockEmb_zero] at e
    simp at e
    exact e.symm
  have hkk0 : k0 * k0 = rootInvSU K p f (show 2 ≤ 4 by norm_num) := by
    apply suMat_injective
    rw [hx0M, hc1, one_smul]
  have hk2 : k₂ * k₂ = negOneSU K p f := by
    apply blockEmb_injective (K := K) (p := p) (f := f) (m := 4) (k := 2) (i := 0) (by norm_num)
    rw [map_mul]
    exact hkk0
  obtain ⟨u, hu⟩ := InnerSu.exists_conj_jSU hK h2 hk2
  set b : Su K p f 4 := blockEmb K p f 4 2 0 (by norm_num) u with hb
  have hbR0 : b ∈ InnerSu.R0 K p f := ⟨u, rfl⟩
  have hbx : b * InnerSu.x0 K p f = InnerSu.x0 K p f * b := blockEmb_zero_comm_x0 u
  have hbR0' : ∀ n ∈ InnerSu.R0' K p f, b * n = n * b := fun n hn =>
    InnerSu.R0_comm_R0' hbR0 hn
  refine ⟨g * b, ?_, ?_, ?_, ?_⟩
  · exact hRg.trans (map_conj_mul_eq' (N := InnerSu.R0 K p f) (g := g)
      (fun n hn => (InnerSu.R0 K p f).mul_mem ((InnerSu.R0 K p f).mul_mem hbR0 hn)
        ((InnerSu.R0 K p f).inv_mem hbR0))
      (fun n hn => (InnerSu.R0 K p f).mul_mem ((InnerSu.R0 K p f).mul_mem
        ((InnerSu.R0 K p f).inv_mem hbR0) hn) hbR0)).symm
  · have h1 : ∀ n ∈ InnerSu.R0' K p f, b * n * b⁻¹ ∈ InnerSu.R0' K p f := fun n hn => by
      have : b * n * b⁻¹ = n := by rw [hbR0' n hn]; group
      rw [this]
      exact hn
    have h2' : ∀ n ∈ InnerSu.R0' K p f, b⁻¹ * n * b ∈ InnerSu.R0' K p f := fun n hn => by
      have : b⁻¹ * n * b = n := by
        rw [mul_assoc, ← hbR0' n hn, ← mul_assoc, inv_mul_cancel, one_mul]
      rw [this]
      exact hn
    exact hR'g.trans (map_conj_mul_eq' (N := InnerSu.R0' K p f) (g := g) h1 h2').symm
  · rw [hxg]
    have hx0 : InnerSu.x0 K p f = rootInvSU K p f (show 2 ≤ 4 by norm_num) := rfl
    rw [← hx0]
    calc g * InnerSu.x0 K p f * g⁻¹ = g * (InnerSu.x0 K p f * b * b⁻¹) * g⁻¹ := by group
      _ = g * (b * InnerSu.x0 K p f * b⁻¹) * g⁻¹ := by rw [← hbx]
      _ = g * b * InnerSu.x0 K p f * (g * b)⁻¹ := by group
  · rw [hk]
    have hk2' : k0 = b * blockEmb K p f 4 2 0 (by norm_num) (jSU K p f) * b⁻¹ := by
      rw [hk0, hb, ← hu]
      simp only [map_mul, map_inv]
    rw [hk2']
    group


end CFSG.ClassicalInvolution.Q3.Q3OT
