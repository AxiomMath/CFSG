module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BSClU6Frm
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BSClU6Dg
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BSClU6Lay

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265.BSCl

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.RankThree.PartOne.KCUnitaryModel

variable {K : Type} [Field K] [CharP K 2] [Finite K]

theorem exists_layer_pair_u6 (h : UnitaryFieldData 2 1 K)
    {A V : Subgroup (MulAut (primeFormP h (idGram K 6)))}
    {d y : MulAut (primeFormP h (idGram K 6))}
    (hA : IsElemAbelian 3 A) (h81 : 81 ≤ Nat.card A) (hAD : A ≤ primeFormD h (idGram K 6))
    (hdA : d ∈ A) (hd1 : d ≠ 1) (hyD : y ∈ primeFormD h (idGram K 6)) (hy : y ^ 11 = 1)
    (hy1 : y ≠ 1) (hdy : d * y = y * d) (hV2 : IsPGroup 2 V) (hV : V ≠ ⊥)
    (hVD : V ≤ primeFormD h (idGram K 6)) (hAV : ∀ a ∈ A, ∀ v ∈ V, a * v * a⁻¹ ∈ V) :
    ∃ e ∈ A, e * y ≠ y * e ∧ GLAPLayer 3 (fixSubgroup d ⊓ fixSubgroup e) ≠ ⊥ := by
  obtain ⟨ω, hζ⟩ := CFSG.RankThree.PartOne.KCUnitaryPlane.exists_primitiveRoot_of_dvd h
    Nat.prime_three (by norm_num)
  have hω : ω ^ 2 + ω + 1 = 0 := by
    have e1 : (ω - 1) * (ω ^ 2 + ω + 1) = ω ^ 3 - 1 := by ring
    rw [hζ.pow_eq_one, sub_self] at e1
    exact (mul_eq_zero.1 e1).resolve_left (sub_ne_zero.2 (hζ.ne_one (by norm_num)))
  obtain ⟨X₁, X₂, R, hX₁A, hX₂A, hR₁, hR₂⟩ :=
    exists_frame_six_of_twoGroup h hω hA (by norm_num; exact h81) hAD hV2 hV hVD hAV
  obtain ⟨X, hX, hXy, D, Q, k, k', ζ, hD, hkk', hζ', hQD, hQX⟩ :=
    exists_diag_pair_of_frame_six h hω (hAD hdA) hd1 (hA.2 d hdA) hyD hy hy1 hdy
      (hA.comm hdA hX₁A) (hA.comm hdA hX₂A) hR₁ hR₂
  refine ⟨primeFormConjHom h (idGram K 6) X, ?_, hXy, ?_⟩
  · rcases hX with rfl | rfl
    exacts [hX₁A, hX₂A]
  · rw [← hD]
    exact glaPLayer_ne_bot_of_diag_pair_six h hζ' hω hkk' hQD hQX

end CFSG.LocalAnalysis.GLTheoremA.S265.BSCl

end
