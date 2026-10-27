module

public import CFSG.LargeExtraspecial.S13SevenB
public import CFSG.LargeExtraspecial.S13SevenA
public import CFSG.LargeExtraspecial.S13Three

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S13

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.S10

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G} {K : Subgroup S.O}

theorem eq_of_mem_finrank_one {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] {W : Submodule (ZMod 2) V} (hW : finrank (ZMod 2) W = 1)
    {x y : V} (hx : x ∈ W) (hx0 : x ≠ 0) (hy : y ∈ W) : y = 0 ∨ y = x := by
  have hle : (ZMod 2) ∙ x ≤ W := (Submodule.span_singleton_le_iff_mem _ _).mpr hx
  have heq := Submodule.eq_of_le_of_finrank_le hle (by
    rw [hW, finrank_span_singleton hx0])
  rw [← heq] at hy
  exact mem_span_cl_iff.mp hy

namespace Hyp13

variable (hCE : CentralExtInput.{u}) (Y : Hyp13 S g K) {c : S.M}
  (hperp : ∀ u ∈ Fbar S g K, ∀ v ∈ Fbar S ((c : G) * g) K, polar S.q u v = 0)
  (hne : Fbar S ((c : G) * g) K ≠ Fbar S g K)
include hCE Y hperp hne

theorem mem_clSub_of_not_mem_Dbar {x : S.Qt} (hx : x ∈ Fbar S ((c : G) * g) K)
    (hxP : x ∈ S.clSub (S.QG ⊓ S.Qa g)) (hx0 : x ≠ 0) {e : S.M}
    (heP : S.cl ((e : G) * g * S.z * ((e : G) * g)⁻¹) ∈ S.clSub (S.QG ⊓ S.Qa g))
    (heD : S.cl ((e : G) * g * S.z * ((e : G) * g)⁻¹) ∉ Fbar S g K ⊔ Fbar S ((c : G) * g) K)
    (hperpe : ∀ u ∈ Fbar S ((e : G) * g) K, ∀ v ∈ Fbar S ((c : G) * g) K, polar S.q u v = 0)
    (hnee : Fbar S ((c : G) * g) K ≠ Fbar S ((e : G) * g) K) :
    x ∈ S.clSub (S.QG ⊓ S.Qa ((e : G) * g)) := by
  set D := Fbar S g K ⊔ Fbar S ((c : G) * g) K with hD
  have Yc : Hyp13 S ((c : G) * g) K := Y.mul rfl
  have Ye : Hyp13 S ((e : G) * g) K := Y.mul rfl
  set ep := S.cl ((e : G) * g * S.z * ((e : G) * g)⁻¹) with hep
  have h1 := timmesfeld_13_3 hCE Y (rfl : (c : G) * g = (c : G) * g) hperp hne
  have h2 := timmesfeld_13_3 hCE Ye (coe_mul_inv_mul c e g).symm hperpe hnee
  have hfix := fixSub_T₀_eq Y (rfl : (c : G) * g = (c : G) * g) hperp hne
  obtain ⟨l, hl, hle⟩ : ∃ l ∈ Ebar S g K ⊓ ptStab S D, (l : S.Qt ≃ₗ[ZMod 2] S.Qt) ep ≠ ep := by
    by_contra hcon
    push Not at hcon
    apply heD
    rw [hD, ← hfix]
    exact fun l hl => hcon l hl
  obtain ⟨hlE, hlD⟩ := Subgroup.mem_inf.mp hl
  have hlL := Ebar_le_Lbar hlE
  have hlea : (l : S.Qt ≃ₗ[ZMod 2] S.Qt) ep = ep + S.cl (g * S.z * g⁻¹) := by
    rcases mem_span_cl_iff.mp (S.sub_mem_span_of_mem_clSub hlL heP) with h | h
    · exact absurd (sub_eq_zero.mp h) hle
    · rw [← h]; abel
  obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (fun h0 => by
    rw [h0, finrank_bot] at h2; omega : Fbar S ((c : G) * g) K ⊓ S.clSub (S.QG ⊓ S.Qa
      ((e : G) * g)) ≠ ⊥)
  obtain ⟨hyF, hyP⟩ := Submodule.mem_inf.mp hy
  obtain ⟨my, -, rfl⟩ := Yc.exists_eq_cl_of_mem_Fbar hyF hy0
  have hyl : (l : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl ((my : G) * ((c : G) * g) * S.z *
      ((my : G) * ((c : G) * g))⁻¹)) =
      S.cl ((my : G) * ((c : G) * g) * S.z * ((my : G) * ((c : G) * g))⁻¹) :=
    hlD _ (Submodule.mem_sup_right hyF)
  obtain ⟨ml, rfl⟩ := MonoidHom.mem_range.mp (Hyp13.Ebar_le_Mbar hlE)
  have hyc : (my : G) * ((c : G) * g) = ((my * c : S.M) : G) * g := by
    rw [Subgroup.coe_mul, mul_assoc]
  rw [hyc] at hyl hyP hyF hy0
  have hyP' := apply_mem_clSub_Qa_mul ml ((e : G) * g) hyP
  rw [hyl, ← mul_assoc, ← Subgroup.coe_mul] at hyP'
  have hpt : S.cl (((ml * e : S.M) : G) * g * S.z * (((ml * e : S.M) : G) * g)⁻¹) =
      ep + S.cl (g * S.z * g⁻¹) := by
    have heQ := conj_mem_QG' S e.2 Y.haQ
    rw [← hlea, hep, ρ_cl_conj_z S ml heQ, Subgroup.coe_mul, mul_assoc (ml : G) (e : G) g]
  have hsum : ep + S.cl (((ml * e : S.M) : G) * g * S.z * (((ml * e : S.M) : G) * g)⁻¹) =
      S.cl (((1 : S.M) : G) * g * S.z * (((1 : S.M) : G) * g)⁻¹) := by
    rw [hpt]
    simp only [OneMemClass.coe_one, one_mul]
    have h2e : ep + ep = 0 := by
      rw [← two_smul (ZMod 2) ep, show (2 : ZMod 2) = 0 from rfl, zero_smul]
    rw [← add_assoc, h2e, zero_add]
  have hya := cl_mem_clSub_of_add Y.H hsum hyP hyP'
  simp only [OneMemClass.coe_one, one_mul] at hya
  rcases eq_of_mem_finrank_one h1 (Submodule.mem_inf.mpr ⟨hx, hxP⟩) hx0
    (Submodule.mem_inf.mpr ⟨hyF, hya⟩) with h | h
  · exact absurd h hy0
  · rw [← h]
    exact hyP

end Hyp13

end CFSG.LargeExtraspecial.S13
