module

public import CFSG.CGT.Stroth77.AlperinBridge

public section

namespace CFSG.CGT.Stroth77

open CFSG.OddStandard.ONan76

variable {G : Type} [Group G] {D : Subgroup G} {uv t u : G}

theorem exists_alperinFrame_of_type310 (e : Additive D ≃+ Torus (Type310.k 2))
    (ht : t ∈ Subgroup.normalizer (D : Set G)) (hu : u ∈ Subgroup.normalizer (D : Set G))
    (ht_conj : ∀ x : D,
      e (Additive.ofMul (conjBy ht x)) = (Type310.action 2 le_rfl).φt (e (Additive.ofMul x)))
    (hu_conj : ∀ x : D,
      e (Additive.ofMul (conjBy hu x)) = (Type310.action 2 le_rfl).φu (e (Additive.ofMul x)))
    (ht2 : t * t = 1) (hu2 : u * u = 1) (huv2 : uv * uv = 1) (htu : t * u = u * uv * t) :
    ∃ v₁ v₂ v₃ s r : G, AlperinFrame 2 v₁ v₂ v₃ s r ∧ s ^ 4 = 1 ∧
      Subgroup.closure ({v₁, v₂, v₃, s, r} : Set G) = D ⊔ Subgroup.closure {uv, t, u} := by
  have hk : ∀ i, Type310.k 2 i = 2 := fun i => by fin_cases i <;> rfl
  refine exists_alperinFrame_of_matEq hk e (Mt := Type310.tM 2) (Mu := Type310.uM 2) ht hu
    ht_conj hu_conj ht2 hu2 huv2 htu (P := ofCols ![1, 0, 1] ![3, 1, 3] ![1, 3, 0]) ?_ ?_ ?_
  · refine MatEq.of_witness (W := !![-3, -7, 1; 0, 0, 0; -1, -1, 0]) ?_
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [Type310.tM, Type310.uM, Type310.ρM, Type310.uvA, Type310.k, uMat, ofCols_apply, alpS,
        Matrix.mul_apply, Fin.sum_univ_three, Matrix.mulVec, dotProduct]
  · refine MatEq.of_witness (W := !![1, 3, 1; 1, 1, 0; 0, 1, 1]) ?_
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [Type310.uM, Type310.k, uMat, ofCols_apply, alpT, Matrix.mul_apply, Fin.sum_univ_three]
  · rw [Matrix.det_fin_three]
    simp [ofCols_apply]

theorem exists_alperinFrame_of_type321 (e : Additive D ≃+ Torus Type321.k)
    (ht : t ∈ Subgroup.normalizer (D : Set G)) (hu : u ∈ Subgroup.normalizer (D : Set G))
    (ht_conj : ∀ x : D,
      e (Additive.ofMul (conjBy ht x)) = Type321.action.φt (e (Additive.ofMul x)))
    (hu_conj : ∀ x : D,
      e (Additive.ofMul (conjBy hu x)) = Type321.action.φu (e (Additive.ofMul x)))
    (ht2 : t * t = 1) (hu2 : u * u = 1) (huv2 : uv * uv = 1) (htu : t * u = u * uv * t) :
    ∃ v₁ v₂ v₃ s r : G, AlperinFrame 3 v₁ v₂ v₃ s r ∧ s ^ 4 = 1 ∧
      Subgroup.closure ({v₁, v₂, v₃, s, r} : Set G) = D ⊔ Subgroup.closure {uv, t, u} := by
  have hk : ∀ i, Type321.k i = 3 := fun i => by fin_cases i <;> rfl
  refine exists_alperinFrame_of_matEq hk e (Mt := Type321.tM) (Mu := Type321.uM) ht hu
    ht_conj hu_conj ht2 hu2 huv2 htu (P := ofCols ![1, 0, 1] ![3, 5, 3] ![1, 7, 0]) ?_ ?_ ?_
  · refine MatEq.of_witness (W := !![-4, -11, 0; -1, -2, 0; -1, 0, 3]) ?_
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [Type321.tM, Type321.uM, Type321.ρM, Type321.uvA, Type321.k, uMat, ofCols_apply,
        alpS, Matrix.mul_apply, Fin.sum_univ_three, Matrix.mulVec, dotProduct]
  · refine MatEq.of_witness (W := !![0, 0, 0; 1, 1, 0; 0, 1, 1]) ?_
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [Type321.uM, Type321.k, uMat, ofCols_apply, alpT, Matrix.mul_apply, Fin.sum_univ_three]
  · rw [Matrix.det_fin_three]
    simp [ofCols_apply]
    decide

end CFSG.CGT.Stroth77
