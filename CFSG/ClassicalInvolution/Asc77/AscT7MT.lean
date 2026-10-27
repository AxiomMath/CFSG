module

public import CFSG.ClassicalInvolution.Asc77.AscT7ME
import CFSG.ClassicalInvolution.Asc77.AscSu4ShapeEng
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Orth15.SqU4

set_option linter.unusedSectionVars false

open Matrix CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.ModelFacts.UnitaryAut CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.ClassicalInvolution.ModelFacts.Orth15.ChainU
  CFSG.ClassicalGroups.Unitary CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterU4

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem su4_core_cases (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) (α : Su K p f 4 →* Su K p f 4)
    (g : GL (Fin 4) K) (φ : K ≃+* K)
    (hα : ∀ x : Su K p f 4, suMat (α x) =
      (g : Matrix (Fin 4) (Fin 4) K) * φ.mapMatrix (suMat x) *
        ((g⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K))
    (hfix0 : ∀ A : Su K p f 2, α (blockEmb K p f 4 2 0 (by norm_num) A) =
      blockEmb K p f 4 2 0 (by norm_num) A)
    (hfix2 : ∀ A : Su K p f 2, α (blockEmb K p f 4 2 2 (by norm_num) A) =
      blockEmb K p f 4 2 2 (by norm_num) A) :
    (φ = RingEquiv.refl K ∧ ∃ a b : K, a ≠ 0 ∧ b ≠ 0 ∧
      (g : Matrix (Fin 4) (Fin 4) K) =
        !![a, 0, 0, 0; 0, a, 0, 0; 0, 0, b, 0; 0, 0, 0, b]) ∨
    (φ = unitaryInvolution K p f ∧ ∃ m n : K, m ≠ 0 ∧ n ≠ 0 ∧
      (g : Matrix (Fin 4) (Fin 4) K) =
        !![0, m, 0, 0; -m, 0, 0, 0; 0, 0, 0, n; 0, 0, -n, 0]) :=
  CFSG.ClassicalInvolution.Asc77.CX.CX4.U4.shape_gen hK hp α g φ hα hfix0 hfix2

theorem su4_odd_blocks (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (φ : MulAut (Su K p f 4 ⧸ Subgroup.center (Su K p f 4)))
    (hfix0 : ∀ A : Su K p f 2, φ (QuotientGroup.mk (blockEmb K p f 4 2 0 (by norm_num) A)) =
      QuotientGroup.mk (blockEmb K p f 4 2 0 (by norm_num) A))
    (hfix2 : ∀ A : Su K p f 2, φ (QuotientGroup.mk (blockEmb K p f 4 2 2 (by norm_num) A)) =
      QuotientGroup.mk (blockEmb K p f 4 2 2 (by norm_num) A))
    (hodd : Odd (orderOf φ)) :
    ∃ a b : K, a ≠ 0 ∧ b ≠ 0 ∧ unitaryInvolution K p f a * a = 1 ∧
      unitaryInvolution K p f b * b = 1 ∧
      ∀ h : Su K p f 4, ∃ h' : Su K p f 4, φ (QuotientGroup.mk h) = QuotientGroup.mk h' ∧
        suMat h' = !![a, 0, 0, 0; 0, a, 0, 0; 0, 0, b, 0; 0, 0, 0, b] * suMat h *
          !![a⁻¹, 0, 0, 0; 0, a⁻¹, 0, 0; 0, 0, b⁻¹, 0; 0, 0, 0, b⁻¹] := by
  have hσσ : ∀ c, unitaryInvolution K p f (unitaryInvolution K p f c) = c :=
    unitaryInvolution_involutive hK
  set θ : Su K p f 4 →* Su K p f 4 ⧸ Subgroup.center (Su K p f 4) := QuotientGroup.mk' _
    with hθ
  have hker : θ.ker ≤ Subgroup.center (Su K p f 4) := by rw [hθ, QuotientGroup.ker_mk']
  obtain ⟨α, g, ψ, hlift, hmat, hiso, -⟩ :=
    unitaryAutClassification_isometry_of_card hK hp hq (d := 4) (by norm_num) _ θ
      (QuotientGroup.mk'_surjective _) hker φ
  have : Group.IsPerfect (Su K p f 2) := isPerfect_suTwo_of_card hK hq
  have hαfix0 : ∀ A : Su K p f 2, α (blockEmb K p f 4 2 0 (by norm_num) A) =
      blockEmb K p f 4 2 0 (by norm_num) A := fun A =>
    DFunLike.congr_fun (lift_comp_eq_of_fixed hker hlift (blockEmb K p f 4 2 0 (by norm_num))
      hfix0) A
  have hαfix2 : ∀ A : Su K p f 2, α (blockEmb K p f 4 2 2 (by norm_num) A) =
      blockEmb K p f 4 2 2 (by norm_num) A := fun A =>
    DFunLike.congr_fun (lift_comp_eq_of_fixed hker hlift (blockEmb K p f 4 2 2 (by norm_num))
      hfix2) A
  set G : Matrix (Fin 4) (Fin 4) K := (g : Matrix (Fin 4) (Fin 4) K) with hG
  set Gi : Matrix (Fin 4) (Fin 4) K := ((g⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)
    with hGi
  have hGiG : Gi * G = 1 := by rw [hG, hGi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hα' : ∀ x : Su K p f 4, suMat (α x) = G * ψ.mapMatrix (suMat x) * Gi := fun x => hmat x
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
    refine ⟨a, b, ha, hb, n0, n2, fun h => ⟨α h, (hlift h).symm, ?_⟩⟩
    rw [hα' h, mapMatrix_refl_four, hGab, hGi']
  ·
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
    have hαα : ∀ x, α (α x) = x := by
      intro x
      apply suMat_injective
      rw [hα' (α x), hα' x, alpha_sq_matrix _ hσσ, hGsq, hGisq]
      simp
    have hφ2 : φ * φ = 1 := by
      ext y
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
      show φ (φ (QuotientGroup.mk x)) = QuotientGroup.mk x
      have h1 : φ (QuotientGroup.mk x) = θ (α x) := (hlift x).symm
      have h2 : φ (θ (α x)) = θ (α (α x)) := (hlift (α x)).symm
      rw [h1, h2, hαα]
      rfl
    have hord : orderOf φ ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hφ2)
    have hle := Nat.le_of_dvd (by norm_num) hord
    have h1' : orderOf φ = 1 := by
      obtain ⟨t, ht⟩ := hodd
      omega
    have hφ1 : φ = 1 := orderOf_eq_one_iff.mp h1'
    refine ⟨1, 1, one_ne_zero, one_ne_zero, by simp, by simp, fun h => ⟨h, ?_, ?_⟩⟩
    · rw [hφ1]
      rfl
    · have e1 : (!![(1 : K), 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] :
          Matrix (Fin 4) (Fin 4) K) = 1 := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp
      rw [inv_one, e1, Matrix.one_mul, Matrix.mul_one]

end CFSG.ClassicalInvolution.ModelFacts.Orth15.SqU4
