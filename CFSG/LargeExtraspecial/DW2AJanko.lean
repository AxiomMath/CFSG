module

public import CFSG.LargeExtraspecial.DW2AFour
public import CFSG.LargeExtraspecial.S3bThirteen

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW

open Subgroup Module QuadraticMap

variable {G : Type*} [Group G] [Finite G]

theorem mem_of_conj_mem {T : Setting G} {A : Subgroup G} (hA : A ≤ T.QG)
    (hM : T.M ≤ normalizer (A : Set G)) (hD : ∀ h : G, h * T.z * h⁻¹ ∈ T.QG → h * T.z * h⁻¹ ∈ A)
    {y k : G} (hyQ : y ∈ T.QG) (hky : k * y * k⁻¹ ∈ A) : y ∈ A := by
  by_cases h1 : y = 1
  · rw [h1]
    exact A.one_mem
  by_cases hz : y = T.z
  · have := hD 1 (by simpa using T.z_mem_QG)
    simpa [hz] using this
  by_cases hc : ∃ g, g * T.z * g⁻¹ = y
  · obtain ⟨g, rfl⟩ := hc
    exact hD g hyQ
  push Not at hc
  obtain ⟨m, hm, hmy⟩ := T.janko_control_fusion hyQ h1 hz hc (hA hky)
  have := (mem_normalizer_iff.mp (hM (T.M.inv_mem hm)) _).mp hky
  rw [← hmy] at this
  simpa [mul_assoc] using this

variable {S : Setting G} {W : Submodule (ZMod 2) S.Qt}

section Closed

variable (hW : IsMbarInvariant S W)
  (hDQ : ∀ h : G, h * S.z * h⁻¹ ∈ S.QG → S.cl (h * S.z * h⁻¹) ∈ W)
include hW hDQ

theorem mem_clPre_of_mem_conjSub {g y : G} (hyQ : y ∈ S.QG)
    (hy : y ∈ conjSub (S.clPre W) g) : y ∈ S.clPre W :=
  mem_of_conj_mem (S.clPre_le_QG W) (M_le_normalizer_clPre hW) (fun h hh => ⟨hh, hDQ h hh⟩)
    hyQ (k := g⁻¹) (by simpa using mem_conjSub.mp hy)

theorem mem_conjSub_of_mem_Qa {g y : G} (hyQ : y ∈ S.Qa g) (hy : y ∈ S.clPre W) :
    y ∈ conjSub (S.clPre W) g := by
  set T := S.conjBy g
  have hle : conjSub (S.clPre W) g ≤ T.QG := by
    rw [show T.QG = S.Qa g from rfl, Setting.Qa_eq_map]
    exact Subgroup.map_mono (S.clPre_le_QG W)
  have hTD : ∀ h : G, h * T.z * h⁻¹ ∈ T.QG → h * T.z * h⁻¹ ∈ conjSub (S.clPre W) g := by
    intro h hh
    rw [Setting.conjBy_z] at hh ⊢
    rw [mem_conjSub]
    have hQ : g⁻¹ * (h * (g * S.z * g⁻¹) * h⁻¹) * g ∈ S.QG := by
      rw [show T.QG = S.Qa g from rfl, Setting.Qa_eq_map] at hh
      obtain ⟨q, hq, hqe⟩ := hh
      have e : g⁻¹ * (h * (g * S.z * g⁻¹) * h⁻¹) * g = q := by
        rw [← hqe]
        simp [mul_assoc]
      rw [e]
      exact hq
    have e2 : g⁻¹ * (h * (g * S.z * g⁻¹) * h⁻¹) * g =
        (g⁻¹ * h * g) * S.z * (g⁻¹ * h * g)⁻¹ := by group
    rw [e2] at hQ ⊢
    exact ⟨hQ, hDQ _ hQ⟩
  exact mem_of_conj_mem hle (conjBy_M_le_normalizer (M_le_normalizer_clPre hW) g) hTD hyQ
    (k := g) (conj_mem_conjSub hy)

variable (hWs : ∀ v ∈ W, S.q v = 0) {g : G} (hxQ : g * S.z * g⁻¹ ∈ S.QG)
  (hxW : S.cl (g * S.z * g⁻¹) ∈ W) (hxz : g * S.z * g⁻¹ ≠ S.z)

omit hDQ in
include hxQ hxW hxz in
theorem z_mem_conjSub_of_mem : S.z ∈ conjSub (S.clPre W) g := by
  obtain ⟨u, -, huz, hux⟩ := S.exists_swap rfl hxQ hxz
  rw [conjSub_eq_of_conj_eq (M_le_normalizer_clPre hW) (h' := u) huz.symm, mem_conjSub]
  have e : u⁻¹ * S.z * u = g * S.z * g⁻¹ := by
    nth_rewrite 1 [← hux]
    group
  rw [e]
  exact ⟨hxQ, hxW⟩

omit hDQ in
include hWs hxQ hxW hxz in
theorem conjSub_le_M_of_mem : conjSub (S.clPre W) g ≤ S.M := by
  intro b hb
  have hz := z_mem_conjSub_of_mem hW hxQ hxW hxz
  rw [mem_conjSub] at hb hz
  have hWW : W ≤ perp S W := fun w hw => mem_perp.mpr fun v hv => by
    rw [polar]
    have h1 := hWs _ (W.add_mem hv hw)
    rw [h1, hWs v hv, hWs w hw]
    rfl
  have hc := commute_of_mem_clPre hWW hb hz
  rw [S.mem_M_iff]
  have := congrArg (fun y => g * y * g⁻¹) hc
  simpa [mul_assoc] using this

include hWs hxQ hxW hxz in
theorem conj_mul_inv_mem_inf {a c : G} (ha : a ∈ conjSub (S.clPre W) g) (hcQ : c ∈ S.QG)
    (hcx : c * (g * S.z * g⁻¹) = (g * S.z * g⁻¹) * c) :
    a * c * a⁻¹ * c⁻¹ ∈ S.clPre W ⊓ conjSub (S.clPre W) g := by
  have haM := conjSub_le_M_of_mem hW hWs hxQ hxW hxz ha
  have hcM : c ∈ (S.conjBy g).M := by
    rw [(S.conjBy g).mem_M_iff, Setting.conjBy_z]
    exact hcx
  have h1 : a * c * a⁻¹ * c⁻¹ ∈ conjSub (S.clPre W) g := by
    have := (mem_normalizer_iff.mp (conjBy_M_le_normalizer (M_le_normalizer_clPre hW) g hcM)
      a⁻¹).mp ((conjSub (S.clPre W) g).inv_mem ha)
    rw [show a * c * a⁻¹ * c⁻¹ = a * (c * a⁻¹ * c⁻¹) by group]
    exact (conjSub (S.clPre W) g).mul_mem ha this
  have h2 : a * c * a⁻¹ * c⁻¹ ∈ S.QG := S.QG.mul_mem (S.conj_mem_QG haM hcQ) (S.QG.inv_mem hcQ)
  exact ⟨mem_clPre_of_mem_conjSub hW hDQ h2 h1, h1⟩

include hWs hxQ hxW hxz in
theorem ρ_sub_mem_clSub_inf {a : G} (ha : a ∈ conjSub (S.clPre W) g) {v : S.Qt}
    (hv : polar S.q (S.cl (g * S.z * g⁻¹)) v = 0) :
    ((S.ρ ⟨a, conjSub_le_M_of_mem hW hWs hxQ hxW hxz ha⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v ∈
      S.clSub (S.clPre W ⊓ conjSub (S.clPre W) g) := by
  obtain ⟨c, hcQ, rfl⟩ := S.exists_cl v
  have hcx : c * (g * S.z * g⁻¹) = (g * S.z * g⁻¹) * c :=
    ((S.polar_cl_eq_zero_iff hxQ hcQ).mp hv).symm
  have haM := conjSub_le_M_of_mem hW hWs hxQ hxW hxz ha
  have hmem := conj_mul_inv_mem_inf hW hDQ hWs hxQ hxW hxz ha hcQ hcx
  rw [S.ρ_cl _ hcQ]
  change S.cl (a * c * a⁻¹) - S.cl c ∈ _
  have e : S.cl (a * c * a⁻¹) - S.cl c = S.cl (a * c * a⁻¹ * c⁻¹) := by
    rw [S.cl_mul (S.conj_mem_QG haM hcQ) (S.QG.inv_mem hcQ), S.cl_inv hcQ, sub_eq_add_zmod2]
  rw [e]
  exact S.cl_mem_clSub hmem (hmem.1.1)

include hWs hxQ hxW hxz in
theorem ρ_sub_mem_span {a : G} (ha : a ∈ conjSub (S.clPre W) g) {w : S.Qt} (hw : w ∈ W) :
    ((S.ρ ⟨a, conjSub_le_M_of_mem hW hWs hxQ hxW hxz ha⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈
      ZMod 2 ∙ S.cl (g * S.z * g⁻¹) := by
  set τ : S.O := S.ρ ⟨a, conjSub_le_M_of_mem hW hWs hxQ hxW hxz ha⟩ with hτ
  have hττ : τ * τ = 1 := by
    rw [hτ, ← map_mul]
    have : (⟨a, conjSub_le_M_of_mem hW hWs hxQ hxW hxz ha⟩ : S.M) *
        ⟨a, conjSub_le_M_of_mem hW hWs hxQ hxW hxz ha⟩ = 1 :=
      Subtype.ext (mul_self_of_mem_conjSub hWs ha)
    rw [this, map_one]
  have hWW : ∀ u ∈ W, ∀ v ∈ W, polar S.q u v = 0 := fun u hu v hv => by
    rw [polar, hWs _ (W.add_mem hu hv), hWs u hu, hWs v hv]
    rfl
  rw [← perp_perp (ZMod 2 ∙ S.cl (g * S.z * g⁻¹)), mem_perp]
  intro u hu
  have hu' : polar S.q (S.cl (g * S.z * g⁻¹)) u = 0 :=
    mem_perp.mp hu _ (Submodule.mem_span_singleton_self _)
  rw [← polar_sub_eq_of_mul_self hττ]
  have h1 := ρ_sub_mem_clSub_inf hW hDQ hWs hxQ hxW hxz ha hu'
  have h2 : ((τ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u - u ∈ W := by
    have := S.clSub_mono (inf_le_left : S.clPre W ⊓ conjSub (S.clPre W) g ≤ S.clPre W) h1
    rwa [S.clSub_clPre] at this
  exact hWW _ h2 w hw

include hWs hxQ hxW hxz in
theorem ρ_sub_mem_span_of_mem_perp {a : G} (ha : a ∈ conjSub (S.clPre W) g) {w : S.Qt}
    (hw : w ∈ perp S W) :
    ((S.ρ ⟨a, conjSub_le_M_of_mem hW hWs hxQ hxW hxz ha⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈
      ZMod 2 ∙ S.cl (g * S.z * g⁻¹) := by
  set τ : S.O := S.ρ ⟨a, conjSub_le_M_of_mem hW hWs hxQ hxW hxz ha⟩ with hτ
  have hττ : τ * τ = 1 := by
    rw [hτ, ← map_mul]
    have : (⟨a, conjSub_le_M_of_mem hW hWs hxQ hxW hxz ha⟩ : S.M) *
        ⟨a, conjSub_le_M_of_mem hW hWs hxQ hxW hxz ha⟩ = 1 :=
      Subtype.ext (mul_self_of_mem_conjSub hWs ha)
    rw [this, map_one]
  rw [← perp_perp (ZMod 2 ∙ S.cl (g * S.z * g⁻¹)), mem_perp]
  intro u hu
  have hu' : polar S.q (S.cl (g * S.z * g⁻¹)) u = 0 :=
    mem_perp.mp hu _ (Submodule.mem_span_singleton_self _)
  rw [← polar_sub_eq_of_mul_self hττ]
  have h1 := ρ_sub_mem_clSub_inf hW hDQ hWs hxQ hxW hxz ha hu'
  have h2 : ((τ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u - u ∈ W := by
    have := S.clSub_mono (inf_le_left : S.clPre W ⊓ conjSub (S.clPre W) g ≤ S.clPre W) h1
    rwa [S.clSub_clPre] at this
  exact mem_perp.mp hw _ h2

include hWs hxQ hxW hxz in
theorem eq_one_of_fix_clSub {a : G} (ha : a ∈ conjSub (S.clPre W) g)
    (h : ∀ w ∈ W, ((S.ρ ⟨a, conjSub_le_M_of_mem hW hWs hxQ hxW hxz ha⟩ : S.O) :
      S.Qt ≃ₗ[ZMod 2] S.Qt) w = w) :
    S.ρ ⟨a, conjSub_le_M_of_mem hW hWs hxQ hxW hxz ha⟩ = 1 := by
  refine Subtype.ext (eq_one_of_trivial_perp hW (ρ_mem_Ybar _) h fun v hv => ?_)
  have hv' : polar S.q (S.cl (g * S.z * g⁻¹)) v = 0 := mem_perp.mp hv _ hxW
  have h1 := ρ_sub_mem_clSub_inf hW hDQ hWs hxQ hxW hxz ha hv'
  have := S.clSub_mono (inf_le_left : S.clPre W ⊓ conjSub (S.clPre W) g ≤ S.clPre W) h1
  rwa [S.clSub_clPre] at this

end Closed

end CFSG.LargeExtraspecial.DW
