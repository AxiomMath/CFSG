module

public import CFSG.LieType.Chevalley.RootDiagonalTorusWords
public import CFSG.LieType.Chevalley.LangRootArithmeticDet
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.Matrix.Adjugate

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {τ : Tag} {K : Type} [Field K]

theorem det_cartan_pos (τ : Tag) : 0 < τ.cartan.det := by
  cases τ
  · rw [det_cartan_G2]; norm_num
  · rw [det_cartan_F4]; norm_num
  · rw [det_cartan_D4]; norm_num
  · rw [det_cartan_E6]; norm_num
  · rw [det_cartan_E7]; norm_num
  · rw [det_cartan_E8]; norm_num

theorem cartanChar_prod_zpow_eq_smul {B : Matrix (Fin τ.rank) (Fin τ.rank) ℤ} {d : ℤ}
    (hB : B * τ.cartan = d • 1) (u : Fin τ.rank → Kˣ) :
    cartanChar (fun i => ∏ j, u j ^ B j i) = fun l => u l ^ d := by
  funext l
  calc ∏ i, (∏ j, u j ^ B j i) ^ τ.cartan i l
      = ∏ i, ∏ j, u j ^ (B j i * τ.cartan i l) := by
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [← Finset.prod_zpow]
        exact Finset.prod_congr rfl fun j _ => (zpow_mul _ _ _).symm
    _ = ∏ j, ∏ i, u j ^ (B j i * τ.cartan i l) := Finset.prod_comm
    _ = ∏ j, u j ^ ((B * τ.cartan) j l) := by
        refine Finset.prod_congr rfl fun j _ => ?_
        rw [Matrix.mul_apply, Finset.prod_zpow_eq_zpow_sum]
    _ = u l ^ d := by
        rw [hB]
        simp [Matrix.one_apply]

theorem exceptional_Lang_adjoint_diagonal_lift
    (τ : Tag) (L : Type) [Field L] [IsAlgClosed L]
    (a : Fin τ.rank → Lˣ) :
    rootDiagUnit τ a ∈ adjointGroup τ L ∧
      ∃ t : Fin τ.rank → Lˣ,
        rootDiagUnit τ a = ((List.finRange τ.rank).map fun j => torusElt τ L j (t j)).prod := by
  have hd := det_cartan_pos τ
  have hroot : ∀ j, ∃ u : Lˣ, u ^ τ.cartan.det = a j := by
    intro j
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (a j : L) (n := τ.cartan.det.toNat)
      (by omega)
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [zero_pow (by omega)] at hz
      exact (a j).ne_zero hz.symm
    refine ⟨Units.mk0 z hz0, Units.ext ?_⟩
    rw [← Int.toNat_of_nonneg hd.le, zpow_natCast, Units.val_pow_eq_pow_val, Units.val_mk0, hz]
  choose u hu using hroot
  have he : rootDiagUnit τ a = ((List.finRange τ.rank).map fun j =>
      torusElt τ L j (∏ i, u i ^ τ.cartan.adjugate i j)).prod := by
    rw [list_prod_torusElt_eq_rootDiagUnit, cartanChar_prod_zpow_eq_smul (Matrix.adjugate_mul _)]
    congr 1
    funext l
    exact (hu l).symm
  refine ⟨?_, _, he⟩
  rw [he]
  refine Subgroup.list_prod_mem _ fun g hg => ?_
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hg
  exact torusElt_mem_adjointGroup i _

end CFSG.LieType.Chevalley
