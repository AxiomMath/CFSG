module

public import CFSG.LargeExtraspecial.S10EightA
public import CFSG.LargeExtraspecial.S13TwoA

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S13

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.S10

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G} {K : Subgroup S.O}

theorem three_le_finrank_of_mem {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] {W : Submodule (ZMod 2) V} {u v w : V} (hu : u ∈ W)
    (hv : v ∈ W) (hw : w ∈ W) (hu0 : u ≠ 0) (hv0 : v ≠ 0) (huv : u ≠ v)
    (hwU : w ∉ Submodule.span (ZMod 2) {u, v}) : 3 ≤ finrank (ZMod 2) W := by
  set U := Submodule.span (ZMod 2) ({u, v} : Set V) with hU
  have hU2 : finrank (ZMod 2) U = 2 := by
    have h := finrank_span_eq_card (linearIndependent_pair_zmod2 hu0 hv0 huv)
    have hr : Set.range ![u, v] = ({u, v} : Set V) := by
      rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union]
    rw [hr, Fintype.card_fin] at h
    rw [hU]
    exact h
  have hw0 : w ≠ 0 := fun h => hwU (h ▸ zero_mem _)
  have hinf : U ⊓ (ZMod 2) ∙ w = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨hyU, hyw⟩ := Submodule.mem_inf.mp hy
    rcases mem_span_cl_iff.mp hyw with h | h
    · rw [h]; exact zero_mem _
    · exact absurd (h ▸ hyU) hwU
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq U ((ZMod 2) ∙ w)
  rw [hinf, finrank_bot, hU2, finrank_span_singleton hw0] at h1
  have hle : U ⊔ (ZMod 2) ∙ w ≤ W := sup_le (Submodule.span_le.mpr
    (Set.insert_subset hu (Set.singleton_subset_iff.mpr hv)))
    ((Submodule.span_singleton_le_iff_mem _ _).mpr hw)
  have h2 := Submodule.finrank_mono hle
  omega

namespace Hyp13

variable (Y : Hyp13 S g K)
include Y

theorem Rbar_ne_Lbar_of_mem {τ : S.O} {e : S.M} (hτe : τ ∈ S.Lbar ((e : G) * g))
    (hea : S.cl (g * S.z * g⁻¹) ≠ S.cl ((e : G) * g * S.z * ((e : G) * g)⁻¹)) :
    Rbar S g τ ≠ S.Lbar g := by
  intro hR
  have hle : S.Lbar ((e : G) * g) ≤ S.Lbar g := hR ▸ le_Rbar (Lbar_mul_mem_Dset hτe)
  have Ye : Hyp13 S ((e : G) * g) K := Y.mul rfl
  have hfix : S.cl (g * S.z * g⁻¹) ∈ fixSub S (S.Lbar ((e : G) * g)) := fun l hl =>
    Lbar_apply_cl Y.H (hle hl)
  rw [Ye.H.fixSub_eq] at hfix
  rcases mem_span_cl_iff.mp hfix with h | h
  · exact cl_conj_z_ne_zero S Y.haQ Y.hne h
  · exact hea h

theorem linCase_of {τ : S.O} (hτ : τ ∈ S.Lbar g) (hτE : τ ∉ Ebar S g K)
    (hii : ∀ τ' (hτ' : τ' ∈ S.Lbar g), τ' ∉ Ebar S g K → Rbar S g τ' = S.Lbar g ∨
      LinCase S g hτ')
    {e : S.M} (hτe : τ ∈ S.Lbar ((e : G) * g))
    (hea : S.cl (g * S.z * g⁻¹) ≠ S.cl ((e : G) * g * S.z * ((e : G) * g)⁻¹)) :
    LinCase S g hτ :=
  (hii τ hτ hτE).resolve_left (Y.Rbar_ne_Lbar_of_mem hτe hea)

theorem exists_Xb_not_mem_Fbar {t : S.O} (X : Hyp10 S g t) {Xb Yb : Subgroup S.O}
    (D : Dec108 X Xb Yb) (hE : Ebar S g K = S.Lbar g ⊓ Xb) :
    ∃ ξ ∈ Xb, (ξ : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) ∉ Fbar S g K := by
  by_contra hcon
  push Not at hcon
  have hY : ∀ υ ∈ Yb, ∀ v ∈ Fbar S g K, (υ : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ Fbar S g K := by
    intro υ hυ v hv
    refine mem_Fbar.mpr fun ε hε => ?_
    have hεX : ε ∈ Xb := (Subgroup.mem_inf.mp (hE ▸ hε)).2
    have hc := D.dec.comm ε hεX υ hυ
    rw [← LinearEquiv.mul_apply, ← Subgroup.coe_mul, hc, Subgroup.coe_mul,
      LinearEquiv.mul_apply, mem_Fbar.mp hv ε hε]
  have horb : orbit S g t ⊆ Fbar S g K := by
    rintro _ ⟨r, hr, rfl⟩
    rw [← D.dec.sup] at hr
    obtain ⟨ξ, hξ, υ, hυ, rfl⟩ := exists_mul_of_mem_sup_of_commute D.dec.comm hr
    rw [D.dec.comm ξ hξ υ hυ, Subgroup.coe_mul, LinearEquiv.mul_apply]
    exact hY υ hυ _ (hcon ξ hξ)
  have hle : Vt S g t ≤ Fbar S g K := by
    rw [Vt_eq_span_orbit X.H X.ht]
    exact Submodule.span_le.mpr horb
  have h1 := Submodule.finrank_mono hle
  rw [X.h4, Y.finrank_Fbar] at h1
  omega

end Hyp13

end CFSG.LargeExtraspecial.S13
