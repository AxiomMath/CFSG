module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveFive
import CFSG.LocalAnalysis.StandardType.GGL45NtGroupLemmas

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open scoped MatrixGroups
open CFSG.LocalAnalysis.RankThreeUC.AGL81C

theorem exists_orderOf_eq_three_psl_three (F : Type) [Field F] :
    ∃ x : PSL(3, F), orderOf x = 3 := by
  let w : Equiv.Perm (Fin 3) := finRotate 3
  let P : Matrix (Fin 3) (Fin 3) F := Matrix.permMatrixHom (R := F) w
  have hP3 : P ^ 3 = 1 := by
    change (Matrix.permMatrixHom (R := F) w) ^ 3 = 1
    rw [← map_pow, show w ^ 3 = 1 by decide, map_one]
  have hsign : Equiv.Perm.sign w = 1 := by
    change Equiv.Perm.sign (finRotate 3) = 1
    rw [sign_finRotate]
    norm_num
  have hdet : P.det = 1 := by
    change (Matrix.permMatrixHom (R := F) w).det = 1
    rw [Matrix.permMatrixHom_apply, Matrix.det_permutation, Equiv.Perm.sign_inv, hsign]
    norm_num
  let g : SL(3, F) := ⟨P, hdet⟩
  have hg3 : g ^ 3 = 1 := by
    apply Subtype.ext
    show ((g : Matrix (Fin 3) (Fin 3) F) ^ 3) = 1
    simpa [g] using hP3
  let x : PSL(3, F) := QuotientGroup.mk' (Subgroup.center (SL(3, F))) g
  have hx3 : x ^ 3 = 1 := by
    change (QuotientGroup.mk' (Subgroup.center (SL(3, F))) g) ^ 3 = 1
    rw [← map_pow, hg3, map_one]
  have hx1 : x ≠ 1 := by
    intro hx
    change QuotientGroup.mk' (Subgroup.center (SL(3, F))) g = 1 at hx
    have hmem : g ∈ Subgroup.center (SL(3, F)) := (QuotientGroup.eq_one_iff g).mp hx
    obtain ⟨r, -, hscalar⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hmem
    have hentry : Matrix.scalar (Fin 3) r (1 : Fin 3) (0 : Fin 3) =
        (g : Matrix (Fin 3) (Fin 3) F) 1 0 :=
      congrFun (congrFun hscalar 1) 0
    have hP10 : P 1 0 = 1 := by
      change (Matrix.permMatrixHom (R := F) w) 1 0 = 1
      rw [Matrix.permMatrixHom_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
        Equiv.toPEquiv_apply]
      simp [w]
    have : (0 : F) = 1 := by
      simpa [g, Matrix.scalar_apply, hP10] using hentry
    exact zero_ne_one this
  exact ⟨x, orderOf_eq_prime hx3 hx1⟩

theorem exists_orderOf_three_fixed_of_isL3TwoPow {n : ℕ} {X : Type} [Group X] [Finite X]
    (hX : IsL3TwoPow n X) (φ : MulAut X) (hφ : φ ^ 3 = 1) :
    ∃ x : X, orderOf x = 3 ∧ φ x = x := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hX' : IsPSLType 3 (GaloisField 2 n) X := hX
  obtain ⟨e⟩ := hX'
  obtain ⟨y, hy⟩ := exists_orderOf_eq_three_psl_three (GaloisField 2 n)
  have h3 : 3 ∣ Nat.card (PSL(3, GaloisField 2 n)) := by
    simpa [hy] using orderOf_dvd_natCard y
  have h3' : 3 ∣ Nat.card X := by
    rwa [Nat.card_congr e.toEquiv]
  exact CFSG.HardMathSupport.C14Group.exists_fixed_of_order_p Nat.prime_three φ hφ h3'

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12

end
