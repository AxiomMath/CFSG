module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD309LieMon

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD309L

open Equiv Subgroup

abbrev V3 : Type := Fin 3 → ZMod 5

@[expose] def ext5 (v : V3) : Fin 5 → ZMod 5 := ![v 0, v 1, v 2, -(v 0 + v 1 + v 2), 0]

@[expose] def ch5 (y : Fin 5 → ZMod 5) : V3 := ![y 0 - y 4, y 1 - y 4, y 2 - y 4]

@[expose] def act (τ : Perm (Fin 5)) (v : V3) : V3 := ch5 (fun i => ext5 v (τ.symm i))

theorem ch5_ext5 (v : V3) : ch5 (ext5 v) = v := by
  funext i
  fin_cases i <;> simp [ch5, ext5]

theorem sum_ext5 (v : V3) : ∑ i, ext5 v i = 0 := by
  simp [Fin.sum_univ_five, ext5]

theorem ext5_ch5 {y : Fin 5 → ZMod 5} (h : ∑ i, y i = 0) :
    ext5 (ch5 y) = fun i => y i - y 4 := by
  have h5 : (5 : ZMod 5) = 0 := by decide
  have hs : y 0 + y 1 + y 2 + y 3 + y 4 = 0 := by simpa [Fin.sum_univ_five] using h
  funext i
  fin_cases i <;> simp [ext5, ch5]
  linear_combination (-1 : ZMod 5) * hs + (y 4) * h5

theorem ch5_sub_const (y : Fin 5 → ZMod 5) (c : ZMod 5) : ch5 (fun i => y i - c) = ch5 y := by
  funext i
  fin_cases i <;> simp [ch5]

theorem ch5_add (y y' : Fin 5 → ZMod 5) : ch5 (y + y') = ch5 y + ch5 y' := by
  funext i
  fin_cases i <;> simp [ch5] <;> ring

theorem ch5_smul (c : ZMod 5) (y : Fin 5 → ZMod 5) : ch5 (c • y) = c • ch5 y := by
  funext i
  fin_cases i <;> simp [ch5] <;> ring

theorem ext5_add (v w : V3) (j : Fin 5) : ext5 (v + w) j = ext5 v j + ext5 w j := by
  fin_cases j <;> simp [ext5] <;> ring

theorem ext5_smul (c : ZMod 5) (v : V3) (j : Fin 5) : ext5 (c • v) j = c * ext5 v j := by
  fin_cases j <;> simp [ext5] <;> ring

@[expose] def actL (τ : Perm (Fin 5)) : V3 →ₗ[ZMod 5] V3 where
  toFun := act τ
  map_add' v w := by
    simp only [act]
    rw [← ch5_add]
    congr 1
    funext i
    simp [ext5_add]
  map_smul' c v := by
    simp only [act, RingHom.id_apply]
    rw [← ch5_smul]
    congr 1
    funext i
    simp [ext5_smul]

theorem act_act (σ τ : Perm (Fin 5)) (v : V3) : act σ (act τ v) = act (σ * τ) v := by
  unfold act
  have hs : ∑ i, ext5 v (τ.symm i) = 0 := by
    rw [Equiv.sum_comp τ.symm (ext5 v)]
    exact sum_ext5 v
  rw [ext5_ch5 hs, ← ch5_sub_const (fun i => ext5 v ((σ * τ).symm i)) (ext5 v (τ.symm 4))]
  rfl

theorem act_one (v : V3) : act 1 v = v := ch5_ext5 v

theorem act_inv_act (τ : Perm (Fin 5)) (v : V3) : act τ⁻¹ (act τ v) = v := by
  rw [act_act, inv_mul_cancel, act_one]

theorem act_act_inv (τ : Perm (Fin 5)) (v : V3) : act τ (act τ⁻¹ v) = v := by
  rw [act_act, mul_inv_cancel, act_one]

@[expose] def canon (v : V3) : V3 :=
  if v 0 ≠ 0 then (v 0)⁻¹ • v else if v 1 ≠ 0 then (v 1)⁻¹ • v else (v 2)⁻¹ • v

theorem canon_smul : ∀ c : ZMod 5, c ≠ 0 → ∀ v : V3, canon (c • v) = canon v := by
  decide +kernel

@[expose] def sg : Perm (Fin 5) := sig5

@[expose] def sg' : Perm (Fin 5) := swap 0 1 * sig5 * swap 0 1

@[expose] def words : Finset (Perm (Fin 5)) :=
  (Finset.univ : Finset (Fin 5 × Fin 5 × Fin 5)).image
    (fun p => sg ^ (p.1 : ℕ) * sg' ^ (p.2.1 : ℕ) * sg ^ (p.2.2 : ℕ))

@[expose] def actD (τ : Perm (Fin 5)) (u : V3) : V3 := fun k => u ⬝ᵥ (act τ⁻¹ (Pi.single k 1))

theorem lines_ge_six : ∀ v : V3, v ≠ 0 → 6 ≤ (words.image (fun w => canon (act w v))).card := by
  decide +kernel

theorem planes_ge_six : ∀ u : V3, u ≠ 0 →
    6 ≤ (words.image (fun w => canon (actD w u))).card := by
  decide +kernel

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD309L
