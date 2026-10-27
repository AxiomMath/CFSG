module

public import CFSG.LargeExtraspecial.GLW4Siegel
public import CFSG.LargeExtraspecial.GLRLinInv
public import CFSG.LargeExtraspecial.S3bConj

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.GLW4

open Subgroup Module QuadraticMap CFSG.LargeExtraspecial.GLR

variable {G : Type*} [Group G] [Finite G] {S : Setting G}

theorem apply_mem_clSub_inf {g : G} (hxQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z)
    {h : G} (hh : h ∈ S.M)
    (hfix : (S.ρ ⟨h, hh⟩ : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) = S.cl (g * S.z * g⁻¹))
    {w : S.Qt} (hw : w ∈ S.clSub (S.QG ⊓ S.Qa g)) :
    (S.ρ ⟨h, hh⟩ : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈ S.clSub (S.QG ⊓ S.Qa g) := by
  obtain ⟨y, hy, hyQ, rfl⟩ := S.mem_clSub_iff.mp hw
  rw [S.ρ_cl ⟨h, hh⟩ hyQ]
  have hx' : (h * g) * S.z * (h * g)⁻¹ = h * (g * S.z * g⁻¹) * h⁻¹ := by group
  have hcl : S.cl ((h * g) * S.z * (h * g)⁻¹) = S.cl (g * S.z * g⁻¹) := by
    rw [hx']
    exact (S.ρ_cl ⟨h, hh⟩ hxQ).symm.trans hfix
  have hQ' : (h * g) * S.z * (h * g)⁻¹ ∈ S.QG := by rw [hx']; exact S.conj_mem_QG hh hxQ
  have heq : S.QG ⊓ S.Qa (h * g) = S.QG ⊓ S.Qa g := by
    rcases (S.cl_eq_cl_iff hxQ hQ').mp hcl.symm with e | e
    · rw [S.Qa_eq_of_conj_eq e]
    · exact S.QG_inf_Qa_eq_of_conj_eq_mul_z hxQ hne e
  have hmem : h * y * h⁻¹ ∈ S.QG ⊓ S.Qa g := by
    rw [← heq]
    exact ⟨S.conj_mem_QG hh hyQ, S.conj_mem_Qa_mul hy.2⟩
  exact S.cl_mem_clSub hmem hmem.1

theorem exists_mem_inf_cl_eq {X : Subgroup S.O} {A B : Submodule (ZMod 2) S.Qt}
    (hP : Pair S X A B) (hXM : X ≤ S.Mbar) {g : G} (hxQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) {a b : S.Qt} (ha : a ∈ A) (hb : b ∈ B)
    (hcl : S.cl (g * S.z * g⁻¹) = a + b)
    (h3 : 3 ≤ finrank (ZMod 2) (S.clSub (S.QG ⊓ S.Qa g))) :
    ∃ y ∈ S.QG ⊓ S.Qa g, S.cl y = a := by
  set W := S.clSub (S.QG ⊓ S.Qa g) with hW
  have hxW : a + b ∈ W := hcl ▸ S.cl_mem_clSub ⟨hxQ, S.conj_z_mem_Qa g⟩ hxQ
  have hab : polar S.q a b = 0 := by
    have h0 := S.q_cl_conj_z hxQ
    rw [hcl, QuadraticMap.map_add S.q a b, hP.q_A a ha, hP.q_B b hb, zero_add, zero_add] at h0
    exact h0
  have hperp : ∀ w ∈ W, polar S.q w (a + b) = 0 := by
    intro w hw
    obtain ⟨y, hy, hyQ, rfl⟩ := S.mem_clSub_iff.mp hw
    rw [← hcl]
    exact (S.polar_cl_eq_zero_iff hyQ hxQ).mpr
      (S.QG_inf_Qa_comm hne hy ⟨hxQ, S.conj_z_mem_Qa g⟩)
  have hinv : ∀ x ∈ X, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) (a + b) = a + b →
      ∀ w ∈ W, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈ W := by
    intro x hx hxf w hw
    obtain ⟨⟨h, hh⟩, rfl⟩ := hXM hx
    exact apply_mem_clSub_inf hxQ hne hh (by rw [hcl]; exact hxf) hw
  have hle2 : ∀ v w : S.Qt, finrank (ZMod 2) (Submodule.span (ZMod 2) ({v, w} : Set S.Qt)) < 3 :=
    fun v w => (finrank_span_le_two v w).trans_lt (by norm_num)
  obtain ⟨w₁, hw₁, hw₁n⟩ : ∃ w ∈ W, w ∉ Submodule.span (ZMod 2) {a + b} := by
    by_contra hc
    push Not at hc
    have h1 := Submodule.finrank_mono (show W ≤ Submodule.span (ZMod 2) ({a + b, a + b} : Set _)
      by rw [Set.pair_eq_singleton]; exact hc)
    have := hle2 (a + b) (a + b)
    omega
  obtain ⟨w₂, hw₂, hw₂n⟩ : ∃ w ∈ W, w ∉ Submodule.span (ZMod 2) {a + b, w₁} := by
    by_contra hc
    push Not at hc
    have h1 := Submodule.finrank_mono (show W ≤ Submodule.span (ZMod 2) ({a + b, w₁} : Set _)
      from hc)
    have := hle2 (a + b) w₁
    omega
  have haW := mem_of_siegel_invariant hP ha hb hab hxW hperp hw₁ hw₂ hw₁n hw₂n hinv
  obtain ⟨y, hy, -, hya⟩ := S.mem_clSub_iff.mp haW
  exact ⟨y, hy, hya⟩

end CFSG.LargeExtraspecial.GLW4
