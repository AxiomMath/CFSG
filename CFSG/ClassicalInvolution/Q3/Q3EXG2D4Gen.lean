module

public import CFSG.ClassicalInvolution.Q3.Q3EXG2D4GenMax
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87G2ThreeMax

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3W.EX

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.Blueprint.Chevalley


theorem lieModel_modelG2 (n : ℕ) : CFSG.Blueprint.LieModel (CompData.model .G2 n).G .G2 0 3 1 := by
  have hcard : Nat.card (GaloisField 3 1) = 3 ^ 1 := GaloisField.card 3 1 (by norm_num)
  exact GH74.GLS.IVK.Proofs2.Ivk47ab.lieModel_G2g (F := GaloisField 3 1) (p := 3) (f := 1)
    Nat.prime_three le_rfl (by norm_num) hcard

theorem centralizer_coatom_model_g2 (n : ℕ)
    (r : (CompData.model .G2 n).G) (hr2 : r * r = 1) (hr1 : r ≠ 1) :
    IsCoatom (Subgroup.centralizer ({r} : Set (CompData.model .G2 n).G)) := by
  have : Finite (CompData.model .G2 n).G :=
    inferInstanceAs (Finite ↥(adjointGroup .G2 (GaloisField 3 1)))
  have hZ : Subgroup.center (CompData.model .G2 n).G = ⊥ :=
    G2D4.center_modelUniv_g2d4_eq_bot (by norm_num) (Or.inl rfl) n le_rfl
  have hα2 : MulAut.conj r * MulAut.conj r = 1 := by
    rw [← map_mul, hr2, map_one]
  have hα1 : MulAut.conj r ≠ 1 := by
    intro h
    apply hr1
    have hmem : r ∈ Subgroup.center (CompData.model .G2 n).G := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h1 := DFunLike.congr_fun h g
      simp only [MulAut.conj_apply, MulAut.one_apply] at h1
      calc g * r = (r * g * r⁻¹) * r := by rw [h1]
        _ = r * g := by group
    rw [hZ] at hmem
    exact hmem
  have hm := GH74.GLS.Stage2.Signalizer.Odd87.g2ThreeMax_of_cert (CompData.model .G2 n).G
    (lieModel_modelG2 n) (MulAut.conj r) hα2 hα1
  have heq : (MulAut.conj r).toMonoidHom.eqLocus (MonoidHom.id (CompData.model .G2 n).G) =
      Subgroup.centralizer ({r} : Set (CompData.model .G2 n).G) := by
    ext y
    constructor
    · intro h
      have h' : r * y * r⁻¹ = y := h
      rw [mul_inv_eq_iff_eq_mul] at h'
      exact Subgroup.mem_centralizer_singleton_iff.mpr h'.symm
    · intro h
      have h' : y * r = r * y := Subgroup.mem_centralizer_singleton_iff.mp h
      show r * y * r⁻¹ = y
      rw [mul_inv_eq_iff_eq_mul]
      exact h'.symm
  rw [heq] at hm
  exact hm

theorem genFact3_g2 {n : ℕ} (hadm : StatedLieAdmissible .G2 n 3 1) :
    GenFact3 (CompData.model .G2 n) :=
  genFact3_g2_of_coatom hadm fun r hr2 hr1 => centralizer_coatom_model_g2 n r hr2 hr1

end CFSG.ClassicalInvolution.Q3.Q3W.EX
