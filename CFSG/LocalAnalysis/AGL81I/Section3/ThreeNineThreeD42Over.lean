module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.D4TwoArr
public import Certificates.Data.CFSGNative.D42Over.Basic

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3.D42Over

open CFSG.AGLEmbedding.D4Two CFSG.Quasithin CFSG.D42Over.Native

theorem wordGL_reverse (w : List ℕ) : (wordGL w)⁻¹ = wordGL w.reverse := by
  have hl : ∀ l, letterGL l * letterGL l = 1 := fun l => Units.ext (letterMat_mul_self l)
  have hw : ∀ w : List ℕ, wordGL w * wordGL w.reverse = 1 := by
    intro w
    induction w with
    | nil => simp [wordGL]
    | cons l w ih =>
      have h1 : wordGL (l :: w) = letterGL l * wordGL w := by simp [wordGL]
      have h2 : wordGL (l :: w).reverse = wordGL w.reverse * letterGL l := by
        simp [wordGL, List.reverse_cons]
      rw [h1, h2, mul_assoc, ← mul_assoc (wordGL w), ih, one_mul, hl]
  exact inv_eq_of_mul_eq_one_right (hw w)

@[expose] def wordElt (w : List ℕ) : trialityGroup8 := ⟨wordGL w, wordGL_mem w⟩

end CFSG.LocalAnalysis.AGL81I.Section3.D42Over
