module

public import CFSG.GF2Type.Smith1979W3.CaseD.Transfer
public import CFSG.GroupTheory.WeirSylow.OrthogonalModels
public import CFSG.LargeExtraspecial.S3bConj

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979W3.CaseD

open CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.SmallOmegaSix CFSG.LargeExtraspecial
  Module

variable {G : Type} [Group G] [Finite G] (S : Setting G)

theorem exists_isometry_model_of_totallySingular (hn : S.width = 3) {W : Submodule (ZMod 2) S.Qt}
    (hW : ∀ w ∈ W, S.q w = 0) (hW3 : finrank (ZMod 2) W = 3) :
    ∃ E : S.Qt ≃ₗ[ZMod 2] (ι6 → ZMod 2), ∀ v, Q6 (E v) = S.q v := by
  have hV : finrank (ZMod 2) S.Qt = 2 * 3 := by
    rw [S.finrank_Qt_eq_two_mul_width, hn]
  have hplus : CFSG.GroupTheory.WeirSylow.IsPlusType S.q :=
    ⟨W, by rw [hW3, hV], hW⟩
  obtain ⟨ι⟩ := CFSG.GroupTheory.WeirSylow.nonempty_isometry_quadPlus
    (K := ZMod 2) (V := S.Qt) (Q := S.q) (n := 3) S.q_nondegenerate hV hplus
  refine ⟨ι.toLinearEquiv, fun v => ?_⟩
  have hcoe : ∀ x : ι6 → ZMod 2, Q6 x = CFSG.LieType.Universal.Spin.quadPlus 3 (ZMod 2) x :=
    fun x => (congrFun (CFSG.LieType.Universal.Spin.coe_quadPlus 3 (ZMod 2)) x).symm
  exact (hcoe (ι.toLinearEquiv v)).trans (ι.map_app v)

theorem not_exists_invariant_of_not_isReducible (hirr : ¬ S.IsReducible) :
    ¬ ∃ W : Submodule (ZMod 2) S.Qt, W ≠ ⊥ ∧ W ≠ ⊤ ∧
      ∀ g ∈ S.Mbar, ∀ v ∈ W, (g : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ W := by
  rintro ⟨W, hW0, hWtop, hWinv⟩
  refine hirr ⟨W, hW0, hWtop, ?_⟩
  intro m v hv
  exact hWinv (S.ρ m) ⟨m, rfl⟩ v hv

theorem exists_nine_le_stab (hn : S.width = 3) {W : Submodule (ZMod 2) S.Qt}
    (hW : ∀ w ∈ W, S.q w = 0) (hW3 : finrank (ZMod 2) W = 3) (hirr : ¬ S.IsReducible)
    {s : S.O} (hs : s ∈ S.Mbar) (hsC : IsTypeC S.q (s : S.Qt ≃ₗ[ZMod 2] S.Qt) 2)
    {x : S.Qt} (hx0 : x ≠ 0) (hx : S.q x = 0) :
    ∃ P : Subgroup S.O, P ≤ S.Mbar ∧ Nat.card P = 9 ∧
      ∀ p ∈ P, (p : S.Qt ≃ₗ[ZMod 2] S.Qt) x = x := by
  obtain ⟨E, hE⟩ := exists_isometry_model_of_totallySingular S hn hW hW3
  exact exists_nine_le_stab_of_model (V := S.Qt) (q := S.q) E hE
    (not_exists_invariant_of_not_isReducible S hirr) hs hsC hx0 hx

end CFSG.GF2Type.Smith1979W3.CaseD
