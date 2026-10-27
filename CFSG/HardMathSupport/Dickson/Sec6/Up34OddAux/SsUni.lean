module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.SsUniAux.Inner
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.PsuGoodAux.Descent

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open Matrix CFSG CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.ComponentClassification.CatLeaf
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.HardMathSupport.Dickson.Sec6.I923

section Core

variable {ℓ f n : ℕ} {K : Type} [Field K]

theorem noL34Layer_primeFormConjHom (hO : LieOrderFormulasInput) (h : UnitaryFieldData ℓ f K)
    (hℓ : 5 ≤ ℓ) (A : primeFormUnitary h (idGram K n)) {c : Kˣ}
    (hA : (A : GL (Fin n) K) ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin n) c) :
    NoL34Layer (primeFormConjHom h (idGram K n) A) :=
  LieSemisimple.noL34Layer_primeFormConjHom_aux hO h hℓ A hA

theorem noL34Layer_of_mem_primeFormD (hO : LieOrderFormulasInput) (h : UnitaryFieldData ℓ f K)
    (hℓ : 5 ≤ ℓ) (hn : 3 ≤ n) {ψ : MulAut (primeFormP h (idGram K n))}
    (hψD : ψ ∈ primeFormD h (idGram K n)) (hψ3 : ψ ^ 3 = 1) : NoL34Layer ψ := by
  obtain ⟨A, rfl⟩ := hψD
  have hq : 3 < ℓ ^ f := by
    have : ℓ ≤ ℓ ^ f := Nat.le_self_pow (by have := h.one_le; omega) ℓ
    omega
  have h1 : primeFormConjHom h (idGram K n) (A ^ 3) = 1 := by rw [map_pow]; exact hψ3
  obtain ⟨c, -, hc⟩ := (primeFormConjHom_eq_one_iff hn hq (A ^ 3)).mp h1
  exact noL34Layer_primeFormConjHom hO h hℓ A (c := c) (by rw [← Subgroup.coe_pow]; exact hc)

end Core

section Psu

theorem noL34InnAt_psu (hO : LieOrderFormulasInput) :
    NoL34InnAt (fun t n _ _ => t = .PSU ∧ 3 ≤ n) := by
  intro P _ _ t n p f hadm ht hF hp5 hm ψ hψ3 hψ
  obtain ⟨rfl, hn3⟩ := hF
  obtain ⟨K, _, h, ⟨e0⟩⟩ := exists_psu_model hadm hm
  haveI : Finite (primeFormP h (idGram K n)) := Finite.of_equiv P e0.toEquiv
  refine noL34Layer_congr e0 ?_
  have hψ3' : (MulAut.congr e0 ψ) ^ 3 = 1 := by rw [← map_pow, hψ3, map_one]
  obtain ⟨s, hs⟩ := (mem_inner_primeFormP h (idGram K n) _).mp
    ((congr_mem_inner_iff_of_equiv e0 ψ).mpr hψ)
  exact noL34Layer_of_mem_primeFormD hO h hp5 hn3 ⟨⟨s, s.2.1⟩, hs.symm⟩ hψ3'

theorem noL34InnAt_psuGood (hO : LieOrderFormulasInput) : NoL34InnAt FamPsuGood :=
  fun P _ _ t n p f hadm ht hF => noL34InnAt_psu hO P t n p f hadm ht ⟨hF.1, hF.2.1⟩

theorem noL34InnAt_psuBad (hO : LieOrderFormulasInput) : NoL34InnAt FamPsuBad :=
  fun P _ _ t n p f hadm ht hF => noL34InnAt_psu hO P t n p f hadm ht ⟨hF.1, hF.2.1⟩

end Psu

end CFSG.HardMathSupport.Dickson.Sec6
