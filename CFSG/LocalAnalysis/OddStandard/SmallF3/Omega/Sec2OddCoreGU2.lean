module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2OddCoreBasic
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2OddCoreTransport
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma41aU3

public section

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.GH74.GLS.IVK.Proofs2 CFSG.LocalAnalysis.ComponentInitial
  CFSG.ComponentClassification.UnbalancedCatalog.EvenCatalog
open scoped Matrix

section Algebra

variable {F : Type} [Field F]

theorem pow_four_fin_two (x y z w : F) :
    (!![x, y; z, w] : Matrix (Fin 2) (Fin 2) F) ^ 4 =
      !![(x * x + y * z) * (x * x + y * z) + (x * y + y * w) * (z * x + w * z),
         (x * x + y * z) * (x * y + y * w) + (x * y + y * w) * (z * y + w * w);
         (z * x + w * z) * (x * x + y * z) + (z * y + w * w) * (z * x + w * z),
         (z * x + w * z) * (x * y + y * w) + (z * y + w * w) * (z * y + w * w)] := by
  simp only [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq, Matrix.mul_fin_two]

theorem fin_two_eq_iff {a b c d a' b' c' d' : F} :
    (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) F) = !![a', b'; c', d'] ↔
      a = a' ∧ b = b' ∧ c = c' ∧ d = d' := by
  constructor
  · intro h
    exact ⟨congrFun (congrFun h 0) 0, congrFun (congrFun h 0) 1, congrFun (congrFun h 1) 0,
      congrFun (congrFun h 1) 1⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    rfl

theorem unitary_entries (h : UnitaryFieldData 3 1 F) {M : Matrix (Fin 2) (Fin 2) F}
    (hu : (M.map h.bar)ᵀ * M = 1) :
    M 0 0 ^ 3 * M 0 0 + M 1 0 ^ 3 * M 1 0 = 1 ∧ M 0 0 ^ 3 * M 0 1 + M 1 0 ^ 3 * M 1 1 = 0 ∧
      M 0 1 ^ 3 * M 0 0 + M 1 1 ^ 3 * M 1 0 = 0 ∧ M 0 1 ^ 3 * M 0 1 + M 1 1 ^ 3 * M 1 1 = 1 := by
  have hb : ∀ t : F, h.bar t = t ^ 3 := fun t => by
    rw [UnitaryFieldData.bar_apply]
    norm_num
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply, hb] using
      congrFun (congrFun hu 0) 0
  · simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply, hb] using
      congrFun (congrFun hu 0) 1
  · simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply, hb] using
      congrFun (congrFun hu 1) 0
  · simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply, hb] using
      congrFun (congrFun hu 1) 1

theorem three_eq_zero_of_unitaryFieldData (h : UnitaryFieldData 3 1 F) : (3 : F) = 0 := by
  haveI := h.charP
  exact_mod_cast CharP.cast_eq_zero F 3

theorem two_ne_zero_of_unitaryFieldData (h : UnitaryFieldData 3 1 F) : (2 : F) ≠ 0 := by
  intro h2
  have h3 := three_eq_zero_of_unitaryFieldData h
  exact one_ne_zero (show (1 : F) = 0 by linear_combination h3 - h2)

theorem pow_four_eq_one_of_commute_diag (h : UnitaryFieldData 3 1 F) {M : Matrix (Fin 2) (Fin 2) F}
    (hu : (M.map h.bar)ᵀ * M = 1) (hc : M * !![1, 0; 0, -1] = !![1, 0; 0, -1] * M) :
    M ^ 4 = 1 := by
  obtain ⟨hU1, -, -, hU4⟩ := unitary_entries h hu
  have h2 := two_ne_zero_of_unitaryFieldData h
  rw [Matrix.eta_fin_two M, Matrix.mul_fin_two, Matrix.mul_fin_two, fin_two_eq_iff] at hc
  obtain ⟨-, hc01, hc10, -⟩ := hc
  have hy : M 0 1 = 0 := by
    have : (2 : F) * M 0 1 = 0 := by linear_combination (-1 : F) * hc01
    exact (mul_eq_zero.mp this).resolve_left h2
  have hz : M 1 0 = 0 := by
    have : (2 : F) * M 1 0 = 0 := by linear_combination hc10
    exact (mul_eq_zero.mp this).resolve_left h2
  rw [Matrix.eta_fin_two M, hy, hz, pow_four_fin_two, Matrix.one_fin_two, fin_two_eq_iff]
  rw [hz] at hU1
  rw [hy] at hU4
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination hU1
  · ring
  · ring
  · linear_combination hU4

theorem pow_four_eq_one_of_commute_swap (h : UnitaryFieldData 3 1 F) {M : Matrix (Fin 2) (Fin 2) F}
    (hu : (M.map h.bar)ᵀ * M = 1) (hc : M * !![0, 1; 1, 0] = !![0, 1; 1, 0] * M) :
    M ^ 4 = 1 := by
  obtain ⟨hU1, hU2, -, -⟩ := unitary_entries h hu
  have h3 := three_eq_zero_of_unitaryFieldData h
  rw [Matrix.eta_fin_two M, Matrix.mul_fin_two, Matrix.mul_fin_two, fin_two_eq_iff] at hc
  obtain ⟨hc00, hc01, -, -⟩ := hc
  have hz : M 1 0 = M 0 1 := by linear_combination -hc00
  have hw : M 1 1 = M 0 0 := by linear_combination -hc01
  rw [hz] at hU1 hU2
  rw [hw] at hU2
  rw [Matrix.eta_fin_two M, hz, hw, pow_four_fin_two, Matrix.one_fin_two, fin_two_eq_iff]
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination hU1 + (2 * M 0 0 ^ 2 * M 0 1 ^ 2) * h3
  · linear_combination 4 * hU2
  · linear_combination 4 * hU2
  · linear_combination hU1 + (2 * M 0 0 ^ 2 * M 0 1 ^ 2) * h3

theorem pow_four_eq_one_of_commute_rot (h : UnitaryFieldData 3 1 F) {M : Matrix (Fin 2) (Fin 2) F}
    (hu : (M.map h.bar)ᵀ * M = 1) (hc : M * !![0, 1; -1, 0] = !![0, 1; -1, 0] * M) :
    M ^ 4 = 1 := by
  obtain ⟨hU1, hU2, -, -⟩ := unitary_entries h hu
  have h3 := three_eq_zero_of_unitaryFieldData h
  rw [Matrix.eta_fin_two M, Matrix.mul_fin_two, Matrix.mul_fin_two, fin_two_eq_iff] at hc
  obtain ⟨hc00, hc01, -, -⟩ := hc
  have hz : M 1 0 = -M 0 1 := by linear_combination -hc00
  have hw : M 1 1 = M 0 0 := by linear_combination -hc01
  rw [hz] at hU1 hU2
  rw [hw] at hU2
  rw [Matrix.eta_fin_two M, hz, hw, pow_four_fin_two, Matrix.one_fin_two, fin_two_eq_iff]
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination hU1 + (-2 * M 0 0 ^ 2 * M 0 1 ^ 2) * h3
  · linear_combination 4 * hU2
  · linear_combination (-4) * hU2
  · linear_combination hU1 + (-2 * M 0 0 ^ 2 * M 0 1 ^ 2) * h3

end Algebra

section Assembly

variable {F : Type} [Field F]

theorem diag_mul_self :
    (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) F) * !![1, 0; 0, -1] = 1 := by
  rw [Matrix.mul_fin_two, Matrix.one_fin_two, fin_two_eq_iff]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ring

theorem swap_mul_self :
    (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) F) * !![0, 1; 1, 0] = 1 := by
  rw [Matrix.mul_fin_two, Matrix.one_fin_two, fin_two_eq_iff]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ring

theorem unitary_diag (h : UnitaryFieldData 3 1 F) :
    ((!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) F).map h.bar)ᵀ * !![1, 0; 0, -1] = 1 := by
  have e : ((!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) F).map h.bar)ᵀ = !![1, 0; 0, -1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [e]
  exact diag_mul_self

theorem unitary_swap (h : UnitaryFieldData 3 1 F) :
    ((!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) F).map h.bar)ᵀ * !![0, 1; 1, 0] = 1 := by
  have e : ((!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) F).map h.bar)ᵀ = !![0, 1; 1, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [e]
  exact swap_mul_self

@[expose] def gl2OfSq (M : Matrix (Fin 2) (Fin 2) F) (h : M * M = 1) :
    Matrix.GeneralLinearGroup (Fin 2) F :=
  ⟨M, M, h, h⟩

theorem matrix_commute {G' : Subgroup (Matrix.GeneralLinearGroup (Fin 2) F)} {g c : G'}
    (hg : g * c = c * g) :
    ((g : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
        ((c : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      ((c : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
        ((g : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
  have := congrArg (fun u : G' => ((u : Matrix.GeneralLinearGroup (Fin 2) F) :
    Matrix (Fin 2) (Fin 2) F)) hg
  simpa using this

theorem pow_eq_one_of_matrix {G' : Subgroup (Matrix.GeneralLinearGroup (Fin 2) F)} (g : G')
    (hM : ((g : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) ^ 4 = 1) :
    g ^ (2 ^ 2) = 1 :=
  Subtype.ext (Units.ext (by simpa [Units.val_pow_eq_pow_val] using hM))

theorem oddCore_gu2_eq_bot [Finite F] (hF : Nat.card F = 9) :
    oddCore ↥(GU2Stated (3 ^ 1) F) = ⊥ := by
  have h : UnitaryFieldData 3 1 F := ⟨Nat.prime_three, le_rfl, by rw [hF]; norm_num⟩
  let a : ↥(GU2Stated (3 ^ 1) F) := ⟨gl2OfSq !![1, 0; 0, -1] diag_mul_self,
    (Lemma41aU3.mem_GU2Stated_iff h).mpr (unitary_diag h)⟩
  let b : ↥(GU2Stated (3 ^ 1) F) := ⟨gl2OfSq !![0, 1; 1, 0] swap_mul_self,
    (Lemma41aU3.mem_GU2Stated_iff h).mpr (unitary_swap h)⟩
  have hab : ((a * b : ↥(GU2Stated (3 ^ 1) F)) : Matrix.GeneralLinearGroup (Fin 2) F).val =
      !![0, 1; -1, 0] := by
    change (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) F) * !![0, 1; 1, 0] = _
    rw [Matrix.mul_fin_two, fin_two_eq_iff]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> ring
  refine oddCore_eq_bot_of_three_involutions (a := a) (b := b)
    (Subtype.ext (Units.ext diag_mul_self)) (Subtype.ext (Units.ext swap_mul_self)) ?_ ?_ ?_
  · refine oddCore_eq_bot_of_isPGroup_two (isPGroup_two_centralizer_of_pow_eq_one 2 fun g hg => ?_)
    exact pow_eq_one_of_matrix g (pow_four_eq_one_of_commute_diag h
      ((Lemma41aU3.mem_GU2Stated_iff h).mp g.2) (matrix_commute hg))
  · refine oddCore_eq_bot_of_isPGroup_two (isPGroup_two_centralizer_of_pow_eq_one 2 fun g hg => ?_)
    exact pow_eq_one_of_matrix g (pow_four_eq_one_of_commute_swap h
      ((Lemma41aU3.mem_GU2Stated_iff h).mp g.2) (matrix_commute hg))
  · refine oddCore_eq_bot_of_isPGroup_two (isPGroup_two_centralizer_of_pow_eq_one 2 fun g hg => ?_)
    refine pow_eq_one_of_matrix g (pow_four_eq_one_of_commute_rot h
      ((Lemma41aU3.mem_GU2Stated_iff h).mp g.2) ?_)
    have := matrix_commute hg
    rwa [show ((a * b : ↥(GU2Stated (3 ^ 1) F)) : Matrix.GeneralLinearGroup (Fin 2) F).val =
      !![0, 1; -1, 0] from hab] at this

end Assembly

end CFSG.OddStandard.SmallF3.Omega
