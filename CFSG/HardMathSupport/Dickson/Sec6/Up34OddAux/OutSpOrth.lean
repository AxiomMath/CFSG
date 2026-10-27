module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.OutSpOrthAux.Psp
public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.OutSpOrthAux.OrthDescent

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.RankThree.PartTwo.KFacts CFSG.RankThree.PartOne.Sec66T
  CFSG.ComponentClassification.CatLeaf CFSG.HardMathSupport.Dickson.Sec6.I923

theorem noL34OuterAt_psp (hO : LieOrderFormulasInput) : NoL34OuterAt FamPsp := by
  intro P _ _ t n p f hadm ht hF hp5 hm ψ hψ3 hψ
  obtain ⟨rfl, hn2, -⟩ := hF
  have hC : StatedClassicalModel P .PSp n p f := (lieModel_classical_iff (by decide)).mp hm
  obtain ⟨-, K, _, _, hK, ⟨e0⟩⟩ := hC
  haveI : Finite (StatedProj (StatedSp n K)) := Finite.of_equiv P e0.toEquiv
  refine noL34Layer_congr e0 ?_
  have hψ3' : MulAut.congr e0 ψ ^ 3 = 1 := by rw [← map_pow, hψ3, map_one]
  have hninn : ¬ IsInnerAut (MulAut.congr e0 ψ) := fun h =>
    hψ ((congr_mem_inner_iff_of_equiv e0 ψ).mp h)
  obtain ⟨γ, σ, hσ, hψγ⟩ :=
    OutSpOrth.psp_field_descent hn2 hadm.1 hadm.2.1 hK hψ3' hninn
  rw [hψγ]
  exact noL34Layer_conj γ
    (OutSpOrth.noL34Layer_fieldAut_psp hO hn2 hσ hadm.1 hp5 hadm.2.1 hK)

theorem noL34OuterAt_orthOdd (hO : LieOrderFormulasInput) : NoL34OuterAt FamOrthOdd := by
  intro P _ _ t n p f _ _ hF _ hm ψ hψ3 hψ
  obtain rfl := hF
  have hC : StatedClassicalModel P .POmegaOdd n p f :=
    (lieModel_classical_iff (by decide)).mp hm
  exact OutSpOrth.noL34Layer_omega_odd_outer hO hC hψ3 fun a h => hψ ⟨a, h⟩

theorem noL34OuterAt_orthPlus (hO : LieOrderFormulasInput) : NoL34OuterAt FamOrthPlus := by
  intro P _ _ t n p f _ _ hF hp5 hm ψ hψ3 hψ
  obtain ⟨rfl, hn5⟩ := hF
  have hC : StatedClassicalModel P .POmegaPlus n p f :=
    (lieModel_classical_iff (by decide)).mp hm
  exact OutSpOrth.noL34Layer_omega_plus_outer hO hC (by omega) hn5 hψ3 fun a h => hψ ⟨a, h⟩

theorem noL34OuterAt_orthMinus (hO : LieOrderFormulasInput) : NoL34OuterAt FamOrthMinus := by
  intro P _ _ t n p f _ _ hF hp5 hm ψ hψ3 hψ
  obtain rfl := hF
  have hC : StatedClassicalModel P .POmegaMinus n p f :=
    (lieModel_classical_iff (by decide)).mp hm
  exact OutSpOrth.noL34Layer_omega_minus_outer hO hC (by omega) hψ3 fun a h => hψ ⟨a, h⟩

end CFSG.HardMathSupport.Dickson.Sec6
