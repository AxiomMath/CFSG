module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15OuterU4
public import CFSG.ClassicalInvolution.Asc77.AscCX4L1
import CFSG.ClassicalInvolution.Asc77.AscSu4ShapeEng

public section

namespace CFSG.ClassicalInvolution.Asc77.CX.CX4.U4

open Matrix CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.ModelFacts.UnitaryAut CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.ClassicalInvolution.ModelFacts.Orth15.ChainU
  CFSG.ClassicalGroups.Unitary CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterU4

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem shape (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) (α : Su K p f 4 →* Su K p f 4)
    (g : GL (Fin 4) K) (φ : K ≃+* K)
    (hα : ∀ x : Su K p f 4, suMat (α x) =
      (g : Matrix (Fin 4) (Fin 4) K) * φ.mapMatrix (suMat x) *
        ((g⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K))
    (hfix0 : ∀ A : Su K p f 2, α (blockEmb K p f 4 2 0 (by norm_num) A) =
      blockEmb K p f 4 2 0 (by norm_num) A)
    (hfix2 : ∀ A : Su K p f 2, α (blockEmb K p f 4 2 2 (by norm_num) A) =
      blockEmb K p f 4 2 2 (by norm_num) A) :
    (φ = RingEquiv.refl K ∧ ∃ a b : K, a ≠ 0 ∧ b ≠ 0 ∧
      (g : Matrix (Fin 4) (Fin 4) K) = !![a, 0, 0, 0; 0, a, 0, 0; 0, 0, b, 0; 0, 0, 0, b]) ∨
    (φ = unitaryInvolution K p f ∧ ∃ m n : K, m ≠ 0 ∧ n ≠ 0 ∧
      (g : Matrix (Fin 4) (Fin 4) K) = !![0, m, 0, 0; -m, 0, 0, 0; 0, 0, 0, n; 0, 0, -n, 0]) :=
  CFSG.ClassicalInvolution.Asc77.CX.CX4.U4.shape_gen hK hp α g φ hα hfix0 hfix2

theorem fix_cases (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) (hq : 5 ≤ p ^ f) {X : Type}
    [Group X] (θ : Su K p f 4 →* X) (hθ : Function.Surjective θ)
    (hker : θ.ker ≤ Subgroup.center (Su K p f 4)) (s : MulAut X)
    (hfix0 : ∀ A : Su K p f 2, s (θ (blockEmb K p f 4 2 0 (by norm_num) A)) =
      θ (blockEmb K p f 4 2 0 (by norm_num) A))
    (hfix2 : ∀ A : Su K p f 2, s (θ (blockEmb K p f 4 2 2 (by norm_num) A)) =
      θ (blockEmb K p f 4 2 2 (by norm_num) A)) :
    ∃ α : Su K p f 4 →* Su K p f 4, (∀ x, θ (α x) = s (θ x)) ∧
      ((∃ a b : K, a ≠ 0 ∧ b ≠ 0 ∧ unitaryInvolution K p f a * a = 1 ∧
        unitaryInvolution K p f b * b = 1 ∧ ∀ x, suMat (α x) =
          !![a, 0, 0, 0; 0, a, 0, 0; 0, 0, b, 0; 0, 0, 0, b] * suMat x *
            !![a⁻¹, 0, 0, 0; 0, a⁻¹, 0, 0; 0, 0, b⁻¹, 0; 0, 0, 0, b⁻¹]) ∨
       (∃ m n : K, m ≠ 0 ∧ n ≠ 0 ∧ unitaryInvolution K p f m * m = 1 ∧
        unitaryInvolution K p f n * n = 1 ∧ ∀ x, suMat (α x) =
          !![0, m, 0, 0; -m, 0, 0, 0; 0, 0, 0, n; 0, 0, -n, 0] *
            (unitaryInvolution K p f).mapMatrix (suMat x) *
              !![0, -m⁻¹, 0, 0; m⁻¹, 0, 0, 0; 0, 0, 0, -n⁻¹; 0, 0, n⁻¹, 0])) := by
  obtain ⟨α, g, φ, hlift, hmat, hunit, -⟩ :=
    unitaryAutClassification_isometry_of_card hK hp hq (d := 4) (by norm_num) X θ hθ hker s
  have : Group.IsPerfect (Su K p f 2) := isPerfect_suTwo_of_card hK hq
  have hαfix0 : ∀ A : Su K p f 2, α (blockEmb K p f 4 2 0 (by norm_num) A) =
      blockEmb K p f 4 2 0 (by norm_num) A := fun A =>
    DFunLike.congr_fun (lift_comp_eq_of_fixed hker hlift (blockEmb K p f 4 2 0 (by norm_num))
      hfix0) A
  have hαfix2 : ∀ A : Su K p f 2, α (blockEmb K p f 4 2 2 (by norm_num) A) =
      blockEmb K p f 4 2 2 (by norm_num) A := fun A =>
    DFunLike.congr_fun (lift_comp_eq_of_fixed hker hlift (blockEmb K p f 4 2 2 (by norm_num))
      hfix2) A
  have hGiG : ((g⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
      (g : Matrix (Fin 4) (Fin 4) K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  refine ⟨α, hlift, ?_⟩
  rcases shape hK hp α g φ (fun x => hmat x) hαfix0 hαfix2 with
    ⟨hφ, a, b, ha, hb, hGab⟩ | ⟨hφ, m, n, hm, hn, hGmn⟩
  · left
    subst hφ
    have hGi := inv_of_diag4 ha hb _ (by rw [← hGab]; exact hGiG)
    have e00 := congrFun (congrFun hunit 0) 0
    have e22 := congrFun (congrFun hunit 2) 2
    rw [hGab] at e00 e22
    simp [Matrix.mul_apply, Fin.sum_univ_four] at e00 e22
    refine ⟨a, b, ha, hb, e00, e22, fun x => ?_⟩
    show ((α x : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = _
    rw [hmat x, mapMatrix_refl_four, hGab, hGi]
    rfl
  · right
    subst hφ
    have hGi := L4.inv_antidiag g hm hn hGmn
    have e00 := congrFun (congrFun hunit 0) 0
    have e22 := congrFun (congrFun hunit 2) 2
    rw [hGmn] at e00 e22
    simp [Matrix.mul_apply, Fin.sum_univ_four] at e00 e22
    refine ⟨m, n, hm, hn, e00, e22, fun x => ?_⟩
    show ((α x : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = _
    rw [hmat x, hGmn, hGi]
    rfl

end CFSG.ClassicalInvolution.Asc77.CX.CX4.U4
