module

public import CFSG.GH74.GLS.SP.Local.SPLPGL2Cartan
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2OuterInvolutionFusion

public section

namespace CFSG.GH74.GLS.SP.Local

open Subgroup in
theorem pgl2_outer_involutions_conj {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F)
    {M : Type} [Group M] (e : M ≃* CFSG.GorensteinWalter.PGL2 F) (L : Subgroup M) (hL : L.index = 2)
    (v v' : M) (hv : v * v = 1) (hv' : v' * v' = 1) (hvL : v ∉ L) (hv'L : v' ∉ L) :
    ∃ l ∈ L, l * v * l⁻¹ = v' := by
  have hK : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card F) :=
    PGL2Cartan.isOddPrimePower_of_odd hodd
  have hLI : (L.map e.toMonoidHom).index = 2 := (Subgroup.index_map_equiv L e).trans hL
  have hLmap : L.map e.toMonoidHom =
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range :=
    PGL2Cartan.eq_psl2Range_of_index_two hodd h5 hLI
  have hcomm : commutator (CFSG.GorensteinWalter.PGL2 F) = L.map e.toMonoidHom := by
    rw [hLmap]
    exact CFSG.GorensteinWalter.pgl2_commutator_eq_psl2_range_of_card_gt_three F hK (by omega)
  have hmemL : ∀ x : M, x ∈ L ↔ e x ∈ commutator (CFSG.GorensteinWalter.PGL2 F) := by
    intro x
    rw [hcomm, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
  have hinv : ∀ x : M, x * x = 1 → x ∉ L →
      BenderSuzuki.PFAppendixIII.IsInvolution (e x) := by
    intro x hx hxL
    refine ⟨fun h1 => hxL ?_, ?_⟩
    · have hx1 : x = 1 := e.injective (by rw [h1, map_one])
      rw [hx1]
      exact one_mem L
    · rw [pow_two, ← map_mul, hx, map_one]
  obtain ⟨c, hc⟩ := isConj_iff.mp
    (CFSG.GorensteinWalter.pgl2_outer_involutions_conjugate F hK (by omega)
      (hinv v hv hvL) (hinv v' hv' hv'L)
      (fun h => hvL ((hmemL v).mpr h)) (fun h => hv'L ((hmemL v').mpr h)))
  have hg : e.symm c * v * (e.symm c)⁻¹ = v' := by
    apply e.injective
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    exact hc
  by_cases hgL : e.symm c ∈ L
  · exact ⟨e.symm c, hgL, hg⟩
  · refine ⟨e.symm c * v, ?_, ?_⟩
    · rw [Subgroup.mul_mem_iff_of_index_two hL]
      exact iff_of_false hgL hvL
    · rw [← hg]
      group

end CFSG.GH74.GLS.SP.Local
