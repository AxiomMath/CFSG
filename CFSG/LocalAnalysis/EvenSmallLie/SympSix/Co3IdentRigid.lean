
module

public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Co3IdentRigidBase

public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Co3IdentRigidCheck

public section

namespace CFSG.EvenSmallLie.SympSix.Co3Ident

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.Co3
  CFSG.Sporadic.Schreier.Co3.Native Subgroup

theorem e3_spec :
    (∀ k < classData.1.size, classData.1[k]! < 4608) ∧
    (∀ j < 4608, testsOK #[hList[j]!] wsE1 = true →
      classData.2.1[j]! < classData.1.size ∧ classData.2.2[j]! < 4608 ∧
      eqA 276 (compA 276 hList[classData.2.2[j]!]! hList[j]!)
        (compA 276 hList[classData.1[classData.2.1[j]!]!]! hList[classData.2.2[j]!]!) = true) ∧
    (∀ k < classData.1.size, ∀ j₂ < 4608,
      testsOK #[hList[classData.1[k]!]!, hList[j₂]!] wsE2 = true → ∀ j₃ < 4608,
      testsOK #[hList[classData.1[k]!]!, hList[j₂]!, hList[j₃]!] wsE3 = true →
      leafOK #[hList[classData.1[k]!]!, hList[j₂]!, hList[j₃]!] = true) := by
  have h := e3_check
  unfold e3Check at h
  simp only [Bool.and_eq_true, allLt_iff, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨h1, fun j hj ht => ?_, fun k hk j₂ hj₂ ht₂ j₃ hj₃ ht₃ => ?_⟩
  · rcases h2 j hj with h | h
    · rw [ht] at h; exact absurd h (by decide)
    · exact ⟨h.1.1, h.1.2, h.2⟩
  · rcases h3 k hk j₂ hj₂ with h | h
    · rw [ht₂] at h; exact absurd h (by decide)
    · rcases h j₃ hj₃ with h' | h'
      · rw [ht₃] at h'; exact absurd h' (by decide)
      · exact h'

theorem edgeRigidity :
    EdgeRigidity := by
  intro σ he ha hp
  obtain ⟨hreps, hlev1, hlev23⟩ := e3_spec
  obtain ⟨j₁, hj₁, hσ₁⟩ := exists_eltH (σ (gH 0))
  have ht₁ : testsOK #[hList[j₁]!] wsE1 = true := by
    refine testsOK_of σ he ha (rep_arr1 (f := fun m => perm (σ (gH m))) ?_) fun w hw i hi => ?_
    · show Rep 276 hList[j₁]! (perm (σ (gH 0)))
      rw [← hσ₁]
      exact rep_eltH hj₁
    · have := mem_testWords hw i hi
      simp; omega
  obtain ⟨hk, hi, heq⟩ := hlev1 j₁ hj₁ ht₁
  set k := classData.2.1[j₁]!
  set i₁ := classData.2.2[j₁]!
  set r := classData.1[k]!
  have hr : r < 4608 := hreps k hk
  have hE := eq_of_eqA (rep_compA (rep_eltH hi) (rep_eltH hj₁)) (rep_compA (rep_eltH hr)
    (rep_eltH hi)) heq
  set v := eltH i₁
  set σ₁ := σ.trans (MulAut.conj v)
  have hσ₁0 : σ₁ (gH 0) = eltH r := by
    have e : v * σ (gH 0) = eltH r * v := by
      rw [← hσ₁]
      exact mul_eq_of_mul_hom perm_injective edgePerm_mul hE
    simp only [σ₁, MulEquiv.trans_apply, MulAut.conj_apply]
    rw [e, mul_inv_cancel_right]
  have he₁ : σ₁ eH = aH := by
    simp only [σ₁, MulEquiv.trans_apply, MulAut.conj_apply, he]
    exact conj_apply_central aH_mem_center
  have ha₁ : σ₁ aH = eH := by
    simp only [σ₁, MulEquiv.trans_apply, MulAut.conj_apply, ha]
    exact conj_apply_central eH_mem_center
  have hp₁ : PlaneTest σ₁ := planeTest_conj hp v
  obtain ⟨j₂, hj₂, hσ₂⟩ := exists_eltH (σ₁ (gH 1))
  obtain ⟨j₃, hj₃, hσ₃⟩ := exists_eltH (σ₁ (gH 2))
  set Y : Array (Array ℕ) := #[hList[r]!, hList[j₂]!, hList[j₃]!]
  have hY : ∀ m < Y.size, Rep 276 Y[m]! (perm (σ₁ (gH m))) := by
    refine rep_arr3 (f := fun m => perm (σ₁ (gH m))) ?_ ?_ ?_
    · show Rep 276 hList[r]! (perm (σ₁ (gH 0)))
      rw [hσ₁0]; exact rep_eltH hr
    · show Rep 276 hList[j₂]! (perm (σ₁ (gH 1)))
      rw [← hσ₂]; exact rep_eltH hj₂
    · show Rep 276 hList[j₃]! (perm (σ₁ (gH 2)))
      rw [← hσ₃]; exact rep_eltH hj₃
  have ht₂ : testsOK #[hList[r]!, hList[j₂]!] wsE2 = true := by
    refine testsOK_of σ₁ he₁ ha₁ (rep_arr2 (f := fun m => perm (σ₁ (gH m))) ?_ ?_)
      fun w hw i hi => ?_
    · show Rep 276 hList[r]! (perm (σ₁ (gH 0)))
      rw [hσ₁0]; exact rep_eltH hr
    · show Rep 276 hList[j₂]! (perm (σ₁ (gH 1)))
      rw [← hσ₂]; exact rep_eltH hj₂
    · have := mem_testWords hw i hi
      simp; omega
  have ht₃ : testsOK Y wsE3 = true := by
    refine testsOK_of σ₁ he₁ ha₁ hY fun w hw i hi => ?_
    have := mem_testWords hw i hi
    simp [Y]; omega
  have hleaf := hlev23 k hk j₂ hj₂ ht₂ j₃ hj₃ ht₃
  rw [leafOK, Bool.or_eq_true] at hleaf
  rcases hleaf with hψ | hbad
  · obtain ⟨w, hw⟩ := psiForm_spec (fun m hm => hY m (by simpa [Y] using hm)) hψ
    refine ⟨v⁻¹ * w, fun x => ?_⟩
    have hx := congrArg (fun τ : MulAut edgeGroup => τ x) hw
    simp only [σ₁, MulEquiv.trans_apply, MulAut.conj_apply] at hx
    calc σ x = v⁻¹ * (v * σ x * v⁻¹) * v := by group
      _ = v⁻¹ * (w * psi x * w⁻¹) * v := by rw [hx]
      _ = v⁻¹ * w * psi x * (v⁻¹ * w)⁻¹ := by group
  · exact absurd hp₁ (not_planeTest hY hbad)

end CFSG.EvenSmallLie.SympSix.Co3Ident
