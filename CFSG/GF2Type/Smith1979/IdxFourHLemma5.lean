module

public import CFSG.GF2Type.Smith1979.IdxFourHBasic
public import CFSG.LargeExtraspecial.S14Early
public import CFSG.LargeExtraspecial.S11Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.IdxFour

open Subgroup Module QuadraticMap CFSG.LargeExtraspecial CFSG.RankThree.OrthogonalInvolutions

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem no_conj_z_class_mem (hTI : CFSG.LargeExtraspecial.WeaklyClosedTITransitive.{0})
    (hw : S.width = 6) (hirr : ¬ S.IsReducible) (hnoAll : CFSG.LargeExtraspecial.S11.NoA2All S)
    {W : Submodule (ZMod 2) S.Qt}
    (hL5 : ∀ w ∈ W, w ≠ 0 → ∀ P : Subgroup S.O, P ≤ stab S w →
      (∀ s ∈ stab S w, ∀ p ∈ P, s * p * s⁻¹ ∈ P) → IsPGroup 2 P → Nat.card P ≠ 2 ^ 5)
    {h : G} (hQ : h * S.z * h⁻¹ ∈ S.QG) (hne : h * S.z * h⁻¹ ≠ S.z)
    (hW : S.cl (h * S.z * h⁻¹) ∈ W) : False := by
  have hno := hnoAll h hQ hne
  have H := S14.hyp4_of hTI (by omega) hQ hne hno hirr
  have C := S14.cons311_of hTI (by omega) hQ hne hno hirr
  have hw0 : S.cl (h * S.z * h⁻¹) ≠ 0 := S4.cl_conj_z_ne_zero S hQ hne
  have hfix : ∀ x ∈ S.Lbar h,
      (x : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (h * S.z * h⁻¹)) = S.cl (h * S.z * h⁻¹) := by
    have hmem : S.cl (h * S.z * h⁻¹) ∈ S4.fixSub S (S.Lbar h) := by
      rw [H.fixSub_eq]
      exact Submodule.mem_span_singleton_self _
    exact (S4.mem_fixSub S).mp hmem
  have hle : S.Lbar h ≤ stab S (S.cl (h * S.z * h⁻¹)) :=
    fun x hx => mem_stab.mpr ⟨S.Lbar_le_Mbar h hx, hfix x hx⟩
  have hnorm : ∀ s ∈ stab S (S.cl (h * S.z * h⁻¹)), ∀ p ∈ S.Lbar h, s * p * s⁻¹ ∈ S.Lbar h := by
    intro s hs p hp
    have hs' := mem_stab.mp hs
    have hN := S4.mem_normalizer_of_fix (S := S) (g := h) (h := 1) H.conj_mem H.conj_ne hs'.1
      (by simpa using hs'.2)
    have hN' : s ∈ normalizer (S.Lbar h : Set S.O) := by simpa using hN
    exact (mem_normalizer_iff.mp hN' p).mp hp
  haveI := S.isElementaryAbelian_Lbar hQ
  exact hL5 _ hW hw0 (S.Lbar h) hle hnorm (CFSG.IsElementaryAbelian.isPGroup 2 _)
    (by rw [C.card_Lbar, hw])

end CFSG.GF2Type.Smith1979.IdxFour
