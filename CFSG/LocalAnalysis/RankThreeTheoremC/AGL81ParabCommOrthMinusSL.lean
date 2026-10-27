module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.OrthMinus

open Matrix

variable {K : Type} [Field K]

theorem transvection_mulVec {k : ℕ} {i j : Fin k} (hij : i ≠ j) (t : K) (v : Fin k → K) :
    ((SpecialLinearGroup.transvection hij t : SpecialLinearGroup (Fin k) K) :
      Matrix (Fin k) (Fin k) K) *ᵥ v = v + Pi.single i (t * v j) := by
  rw [SpecialLinearGroup.transvection_coe, Matrix.add_mulVec, Matrix.one_mulVec,
    Matrix.single_mulVec_eq]
  congr 1
  ext l
  by_cases h : l = i
  · subst h
    simp
  · simp [Pi.single_apply, h]

theorem sl_schur {k : ℕ} (hk : 2 ≤ k) (σ : K ≃+* K) (φ : (Fin k → K) → (Fin k → K))
    (hadd : ∀ u v, φ (u + v) = φ u + φ v)
    (hsm : ∀ (a : K) (u : Fin k → K), φ (a • u) = σ a • φ u) (hinj : Function.Injective φ)
    (hcomm : ∀ (B : SpecialLinearGroup (Fin k) K) (u : Fin k → K),
      φ ((B : Matrix (Fin k) (Fin k) K) *ᵥ u) = (B : Matrix (Fin k) (Fin k) K) *ᵥ φ u) :
    (∀ a : K, σ a = a) ∧ ∃ a : K, a ≠ 0 ∧ ∀ u, φ u = a • u := by
  have h0 : φ 0 = 0 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact left_eq_add.1 this
  have hsingle : ∀ (i : Fin k) (x : K), (Pi.single i x : Fin k → K) = x • Pi.single i 1 := by
    intro i x
    ext l
    by_cases h : l = i
    · subst h
      simp
    · simp [Pi.single_apply, h]
  have key : ∀ i j : Fin k, i ≠ j → ∀ (t : K) (u : Fin k → K),
      σ (t * u j) • φ (Pi.single i 1) = Pi.single i (t * φ u j) := by
    intro i j hij t u
    have h1 := hcomm (SpecialLinearGroup.transvection hij t) u
    rw [transvection_mulVec, transvection_mulVec, hadd, hsingle i (t * u j), hsm] at h1
    exact add_left_cancel h1
  let o : Fin k := ⟨0, by omega⟩
  let o' : Fin k := ⟨1, by omega⟩
  have hoo' : o ≠ o' := fun e => by simpa [o, o'] using congrArg Fin.val e
  have hex : ∀ i : Fin k, ∃ j : Fin k, i ≠ j := fun i => by
    by_cases hi : i = o
    · exact ⟨o', fun e => hoo' (hi ▸ e)⟩
    · exact ⟨o, hi⟩
  have hphi : ∀ i j : Fin k, i ≠ j → φ (Pi.single i 1) = φ (Pi.single j 1) j • Pi.single i 1 := by
    intro i j hij
    have h1 := key i j hij 1 (Pi.single j 1)
    rw [one_mul, one_mul, Pi.single_eq_same, map_one, one_smul] at h1
    rw [h1, hsingle i]
  have hdiag : ∀ i j : Fin k, φ (Pi.single i 1) i = φ (Pi.single j 1) j := by
    intro i j
    by_cases hij : i = j
    · rw [hij]
    · have h1 := congrFun (hphi i j hij) i
      have h2 := congrFun (hphi j i (Ne.symm hij)) j
      simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one] at h1 h2
      rw [h1, h2]
  set a₀ := φ (Pi.single o 1) o with ha₀
  have hphi' : ∀ i : Fin k, φ (Pi.single i 1) = a₀ • Pi.single i 1 := by
    intro i
    obtain ⟨j, hj⟩ := hex i
    rw [hphi i j hj, hdiag j o]
  have ha₀ne : a₀ ≠ 0 := by
    intro h
    have h1 := hphi' o
    rw [h, zero_smul] at h1
    have h2 := hinj (h1.trans h0.symm)
    have := congrFun h2 o
    simp at this
  have hσ : ∀ t : K, σ t = t := by
    intro t
    obtain ⟨j, hj⟩ := hex o
    have h2 := congrFun (key o j hj t (Pi.single j 1)) o
    simp only [hphi' o, hphi' j, mul_one, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul] at h2
    exact mul_right_cancel₀ ha₀ne h2
  refine ⟨hσ, a₀, ha₀ne, fun u => ?_⟩
  have hu : u = ∑ i, u i • (Pi.single i 1 : Fin k → K) := by
    conv_lhs => rw [← Finset.univ_sum_single u]
    exact Finset.sum_congr rfl fun i _ => hsingle i (u i)
  have hsum := map_sum (AddMonoidHom.mk' φ hadd) (fun i => u i • (Pi.single i 1 : Fin k → K))
    Finset.univ
  simp only [AddMonoidHom.mk'_apply] at hsum
  rw [← hu] at hsum
  rw [hsum]
  calc ∑ x, φ (u x • (Pi.single x 1 : Fin k → K))
      = ∑ x, a₀ • (u x • (Pi.single x 1 : Fin k → K)) :=
        Finset.sum_congr rfl fun i _ => by
          rw [hsm, hσ, hphi' i, smul_smul, smul_smul, mul_comm]
    _ = a₀ • ∑ x, u x • (Pi.single x 1 : Fin k → K) := (Finset.smul_sum ..).symm
    _ = a₀ • u := by rw [← hu]

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.OrthMinus
