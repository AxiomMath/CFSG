module

public import CFSG.ClassicalInvolution.Phan.PhanDn.QTwo.ModelStripChar
public import CFSG.ClassicalInvolution.Phan.PhanDn.QTwo.ModelStripTorus
public import CFSG.ClassicalInvolution.Phan.PhanDn.QTwo.ModelStripLevi
public import CFSG.ClassicalInvolution.Phan.PhanDn.QTwo.ModelParabProd
public import CFSG.LieType.CurtisTits.AmalgamStrip
public import CFSG.ClassicalInvolution.Phan.PhanDn.FlagResidueD
public import CFSG.ClassicalInvolution.Phan.PhanDn.PanelParab

public section

namespace CFSG.ClassicalInvolution.PhanDn.QTwo

open CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.PhanDn
open CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.LieType.BorelTits CFSG.LieType.Steinberg
open CFSG.ClassicalGroups.Unitary
open CFSG.LieType.Universal.Unitary

variable {F K : Type} [Field F] [Field K] [Finite K] [Algebra F K] [CharP K 2]
variable (E : QuadExt F K (unitaryInvolution K 2 1))

theorem iSup_qTwoTor_inf_qTwoStdFamily_levi_le (hK : Nat.card K = 4) (m : ℕ) (hm : 3 ≤ m)
    (C : Set (Fin (m + 1))) :
    (⨆ i, qTwoTor E m hm i) ⊓ (qTwoStdFamily E hK m hm).levi C ≤
      ⨆ i ∈ C, qTwoTor E m hm i := by
  rintro x ⟨hxT, hxL⟩
  have hmem : (x : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) ∈
      diagTorusV F (unitaryInvolution K 2 1) (m + 1) := by
    rw [← map_qTwoTor_iSup_eq_diagTorus E hK m hm]
    exact Subgroup.mem_map_of_mem _ hxT
  obtain ⟨t, ht⟩ := hmem
  exact mem_iSup_qTwoTor_of_prod E hK m hm C ht.symm
    (fun _ hk hk2 => prod_ite_le_eq_one_of_mem_qTwoStdFamily_levi E hK hm hxL ht.symm hk hk2)
    (fun hC => prod_eq_one_of_mem_qTwoStdFamily_levi E hK hm hC hxL ht.symm)
    (fun hC => prod_update_last_eq_one_of_mem_qTwoStdFamily_levi E hK hm hC hxL ht.symm)

theorem qTwoStrip (hK : Nat.card K = 4) (m : ℕ) (hm : 3 ≤ m) :
    CFSG.LieType.CurtisTits.StripData
      (qTwoShape (CFSG.StandardType.ggCoxeterMatrixD (m + 1)))
      (qTwoParab E m) (qTwoStdFamily E hK m hm).levi (qTwoTor E m hm) where
  small _ hC := mem_qTwoShape_of_ncard_le_three (by omega) hC
  L_mono _ _ h := (qTwoStdFamily E hK m hm).levi_mono h
  L_le C _ := qTwoStdFamily_levi_le_qTwoParab E hK m hm C
  T_le := qTwoTor_le_levi E hK m hm
  T_comm i j _ _ hx _ hy := qTwoTor_commute E hK m hm i j hx hy
  T_indep := iSupIndep_qTwoTor E hK m hm
  norm C _ _ ht _ hl := qTwoTor_conj_mem_levi E hK m hm C ht hl
  prod _ hC _ hx := qTwoParab_prod E hK m hm hC hx
  inter C _ := iSup_qTwoTor_inf_qTwoStdFamily_levi_le E hK m hm C
  gen C _ := (qTwoStdFamily E hK m hm).levi_eq_iSup_small C

end CFSG.ClassicalInvolution.PhanDn.QTwo
