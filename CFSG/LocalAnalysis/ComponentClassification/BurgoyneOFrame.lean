module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOEigen

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.O

open Matrix CFSG
open CFSG.ComponentClassification.Burgoyne.PSL (OrthNF exists_frame exists_orth_normal_form)

variable {K : Type} [Field K] {d : ℕ}

theorem famOf_props {R : Matrix (Fin d) (Fin d) K} {W : Submodule K (Fin d → K)} {m : ℕ}
    (u : Module.Basis (Fin m) K W) {P : Matrix (Fin m) (Fin m) K} {w : Fin m → K}
    (hP : Pᵀ * gramMat R u * P = diagonal w) :
    (∀ j k, j ≠ k → famOf u P j ⬝ᵥ R *ᵥ famOf u P k = 0) ∧
      ∀ j, famOf u P j ⬝ᵥ R *ᵥ famOf u P j = w j := by
  constructor
  · intro j k hjk
    rw [famOf_gram, hP, diagonal_apply_ne _ hjk]
  · intro j
    rw [famOf_gram, hP, diagonal_apply_eq]

variable [Finite K]

theorem exists_frame_of_basis (hK : ringChar K ≠ 2) {R : Matrix (Fin d) (Fin d) K}
    (hR : Rᵀ = R) {W : Submodule K (Fin d → K)}
    (hW : ∀ v ∈ W, (∀ u ∈ W, v ⬝ᵥ R *ᵥ u = 0) → v = 0) {m : ℕ}
    (u : Module.Basis (Fin m) K W) (hm : 2 ≤ m) {a : K} (ha : a ≠ 0) :
    ∃ c : Fin m → Fin d → K, (∀ j, c j ∈ W) ∧ (∀ j k, j ≠ k → c j ⬝ᵥ R *ᵥ c k = 0) ∧
      (∀ j : Fin m, (j : ℕ) + 1 < m → c j ⬝ᵥ R *ᵥ c j = a) ∧
      c ⟨m - 1, by omega⟩ ⬝ᵥ R *ᵥ c ⟨m - 1, by omega⟩ ≠ 0 ∧
      ∃ s : K, s ≠ 0 ∧ a ^ (m - 1) * (c ⟨m - 1, by omega⟩ ⬝ᵥ R *ᵥ c ⟨m - 1, by omega⟩) =
        s ^ 2 * (gramMat R u).det := by
  obtain ⟨P, w, hw, hwa, hP⟩ := exists_frame hK hm (gramGL hR hW u)
    (by rw [coe_gramGL]; exact gramMat_transpose hR u) ha
  rw [coe_gramGL] at hP
  obtain ⟨horth, hnorm⟩ := famOf_props u hP
  refine ⟨famOf u P, famOf_mem u P, horth, fun j hj => by rw [hnorm, hwa j hj],
    by rw [hnorm]; exact hw _, (P : Matrix (Fin m) (Fin m) K).det,
    (Matrix.isUnits_det_units P).ne_zero, ?_⟩
  rw [hnorm]
  have e := congrArg Matrix.det hP
  rw [det_mul, det_mul, det_transpose, det_diagonal] at e
  have hprod : ∏ j, w j = a ^ (m - 1) * w ⟨m - 1, by omega⟩ := by
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ ⟨m - 1, by omega⟩)]
    congr 1
    rw [Finset.prod_congr rfl (fun j hj => hwa j (by
        have hj' := Finset.ne_of_mem_erase hj
        have : (j : ℕ) ≠ m - 1 := fun h => hj' (Fin.ext h)
        omega)), Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, Fintype.card_fin]
  rw [← hprod, ← e]
  ring

theorem exists_family_of_basis (hK : ringChar K ≠ 2) {R : Matrix (Fin d) (Fin d) K}
    (hR : Rᵀ = R) {W : Submodule K (Fin d → K)}
    (hW : ∀ v ∈ W, (∀ u ∈ W, v ⬝ᵥ R *ᵥ u = 0) → v = 0) {m : ℕ}
    (u : Module.Basis (Fin m) K W) :
    ∃ c : Fin m → Fin d → K, (∀ j, c j ∈ W) ∧ (∀ j k, j ≠ k → c j ⬝ᵥ R *ᵥ c k = 0) ∧
      (∀ j, c j ⬝ᵥ R *ᵥ c j ≠ 0) ∧ (3 ≤ m → OrthNF fun j => c j ⬝ᵥ R *ᵥ c j) := by
  have hG : ((gramGL hR hW u : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)ᵀ = gramGL hR hW u := by
    rw [coe_gramGL]
    exact gramMat_transpose hR u
  rcases Nat.lt_or_ge m 3 with hm | hm
  · rcases Nat.lt_or_ge m 2 with hm2 | hm2
    ·
      refine ⟨fun j => (u j : Fin d → K), fun j => (u j).2, fun j k hjk => ?_, fun j => ?_,
        fun h => absurd h (by omega)⟩
      · exact absurd (Fin.ext (by omega)) hjk
      · have hdet := gramMat_det_ne_zero hR hW u
        obtain rfl : m = 1 := by
          have := j.2
          omega
        rw [Matrix.det_unique] at hdet
        have hj : j = default := Subsingleton.elim _ _
        rw [hj]
        exact hdet
    · obtain ⟨c, hc, horth, hval, hlast, -⟩ := exists_frame_of_basis hK hR hW u hm2 one_ne_zero
      refine ⟨c, hc, horth, fun j => ?_, fun h => absurd h (by omega)⟩
      by_cases hj : (j : ℕ) + 1 < m
      · rw [hval j hj]
        exact one_ne_zero
      · have hj2 := j.2
        have : j = ⟨m - 1, by omega⟩ := Fin.ext (by simp only; omega)
        rw [this]
        exact hlast
  · obtain ⟨P, w, hNF, hP⟩ := exists_orth_normal_form hK hm (gramGL hR hW u) hG
    rw [coe_gramGL] at hP
    obtain ⟨horth, hnorm⟩ := famOf_props u hP
    have hfun : (fun j => famOf u P j ⬝ᵥ R *ᵥ famOf u P j) = w := funext hnorm
    refine ⟨famOf u P, famOf_mem u P, horth, fun j => by rw [hnorm]; exact hNF.1 j,
      fun _ => by rw [hfun]; exact hNF⟩

end CFSG.ComponentClassification.Burgoyne.O
