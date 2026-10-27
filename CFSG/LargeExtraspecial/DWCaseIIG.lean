module

public import CFSG.LargeExtraspecial.DWCaseIIGBasic
public import CFSG.LargeExtraspecial.DWTransCaseI

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW

open Subgroup Module QuadraticMap CFSG.GroupTheory.GLnTwoSplitting
open scoped IsMulCommutative

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {A : Subgroup G}
  [IsElementaryAbelian 2 A]

namespace MaxEA

variable (hA : MaxEA S A) (hM : S.M ≤ normalizer (A : Set G))
include hA hM

omit hM in
theorem ρ_clMap {n : normalizer (A : Set G)} (hn : (n : G) ∈ S.M) (x : Additive (AN A)) :
    ((S.ρ ⟨n, hn⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (hA.clMap x) =
      hA.clMap (conjLinear (AN A) n x) := by
  rw [clMap_apply, clMap_apply, elt_conjLinear, S.ρ_cl ⟨n, hn⟩ (hA.le_QG (elt_mem x))]

omit [Finite G] [IsElementaryAbelian 2 A] hA in
theorem le_Qa_mul_of_le {g m : G} (hm : m ∈ S.M) (hg : A ≤ S.Qa g) : A ≤ S.Qa (m * g) := by
  rw [Qa_mul_eq_map]
  intro b hb
  have := (mem_normalizer_iff.mp (hM (S.M.inv_mem hm)) b).mp hb
  exact ⟨m⁻¹ * b * m⁻¹⁻¹, hg this, by simp [mul_assoc]⟩

theorem span_good_eq_top {g₀ : G} (hgA : g₀ * S.z * g₀⁻¹ ∈ A) (hne : g₀ * S.z * g₀⁻¹ ≠ S.z)
    (hQa : A ≤ S.Qa g₀) (U : Submodule (ZMod 2) (Additive (AN A)))
    (hU : {x | ∃ g : G, g * S.z * g⁻¹ = elt x ∧ A ≤ S.Qa g} ⊆ (U : Set (Additive (AN A)))) :
    U = ⊤ := by
  have : Finite (Additive (AN A)) := inferInstanceAs (Finite (AN A))
  have : FiniteDimensional (ZMod 2) (Additive (AN A)) := Module.Finite.of_finite
  set s : Set (Additive (AN A)) := {x | ∃ g : G, g * S.z * g⁻¹ = elt x ∧ A ≤ S.Qa g}
  by_contra hUt
  obtain ⟨f, hf0, hUf⟩ := U.exists_le_ker_of_lt_top (lt_top_iff_ne_top.mpr hUt)
  have hfs : ∀ x ∈ Submodule.span (ZMod 2) s, f x = 0 := fun x hx =>
    hUf ((Submodule.span_le.mpr hU) hx)
  set x₀ : Additive (AN A) := vec hgA
  have hx₀s : x₀ ∈ s := ⟨g₀, rfl, hQa⟩
  have hzs : hA.zVec ∈ s := ⟨1, by simp, by rw [S.Qa_one]; exact hA.le_QG⟩
  obtain ⟨t, ⟨n, rfl⟩, ht⟩ := hA.exists_conjLinear_transvection_of_le_Qa hQa (x := x₀) rfl
    (hfs x₀ (Submodule.subset_span hx₀s))
  have hnz : (n : G) * S.z * (n : G)⁻¹ = S.z := by
    have h1 := congrArg elt (ht hA.zVec)
    rw [elt_conjLinear, hfs _ (Submodule.subset_span hzs), zero_smul, add_zero] at h1
    exact h1
  have hnM : (n : G) ∈ S.M := mem_centralizer_singleton_iff.mpr (by
    calc (n : G) * S.z = (n : G) * S.z * (n : G)⁻¹ * n := by group
      _ = S.z * n := by rw [hnz])
  set W : Submodule (ZMod 2) S.Qt := (Submodule.span (ZMod 2) s).map hA.clMap
  have hsM : ∀ m : S.M, ∀ x ∈ s, conjLinear (AN A) ⟨m, hM m.2⟩ x ∈ s := by
    rintro m x ⟨g, hg, hgQ⟩
    refine ⟨(m : G) * g, ?_, le_Qa_mul_of_le hM m.2 hgQ⟩
    rw [elt_conjLinear, ← hg]
    group
  have hW : IsMbarInvariant S W := by
    rintro m _ ⟨x, hx, rfl⟩
    rw [hA.ρ_clMap (n := ⟨m, hM m.2⟩) m.2]
    refine ⟨_, ?_, rfl⟩
    have hle : Submodule.span (ZMod 2) s ≤
        (Submodule.span (ZMod 2) s).comap (conjLinear (AN A) ⟨m, hM m.2⟩).toLinearMap :=
      Submodule.span_le.mpr fun y hy => Submodule.subset_span (hsM m y hy)
    exact hle hx
  have hρ : ∀ y, ((S.ρ ⟨n, hnM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (hA.clMap y) =
      hA.clMap y + f y • hA.clMap x₀ := fun y => by
    rw [hA.ρ_clMap hnM, ht y, map_add, map_smul]
  have hρ1 : S.ρ ⟨n, hnM⟩ = 1 := by
    refine hA.eq_one_of_fix_of_sub_mem hM hW ⟨⟨n, hnM⟩, rfl⟩ ?_ fun v hv => ?_
    · rintro _ ⟨x, hx, rfl⟩
      rw [hρ, hfs x hx, zero_smul, add_zero]
    · obtain ⟨b, hbA, -, rfl⟩ := S.mem_clSub_iff.mp hv
      have e : S.cl b = hA.clMap (vec hbA) := by rw [clMap_apply, elt_vec]
      rw [e, hρ, add_sub_cancel_left]
      exact W.smul_mem _ ⟨x₀, Submodule.subset_span hx₀s, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y, f y ≠ 0 := by
    by_contra! h
    exact hf0 (LinearMap.ext h)
  have hy1 : f y = 1 := by
    rcases zmod_two_eq_zero_or_one (f y) with h | h
    · exact absurd h hy
    · exact h
  have h2 := hρ y
  rw [hρ1, hy1, one_smul] at h2
  have h3 : hA.clMap x₀ = 0 := by
    have := congrArg (· - hA.clMap y) h2
    simpa using this.symm
  rw [clMap_apply, elt_vec, S.cl_eq_zero_iff (hA.le_QG hgA)] at h3
  rcases h3 with h3 | h3
  · exact S.z_ne_one (by simpa [mul_assoc] using congrArg (fun t => g₀⁻¹ * t * g₀) h3)
  · exact hne h3

theorem caseII_hyp_of_good {g₀ : G} (hgA : g₀ * S.z * g₀⁻¹ ∈ A)
    (hne : g₀ * S.z * g₀⁻¹ ≠ S.z) (hQa : A ≤ S.Qa g₀) :
    (A ≤ closure {d : G | d ∈ A ∧ ∃ g : G, g * S.z * g⁻¹ = d}) ∧
      ∀ g : G, g * S.z * g⁻¹ ∈ A → A ≤ S.Qa g := by
  have : Finite (Additive (AN A)) := inferInstanceAs (Finite (AN A))
  have : FiniteDimensional (ZMod 2) (Additive (AN A)) := Module.Finite.of_finite
  have hsurj : Function.Surjective (conjLinear (AN A)) := by
    rw [← MonoidHom.range_eq_top]
    exact eq_top_of_transvections _ {x | ∃ g : G, g * S.z * g⁻¹ = elt x ∧ A ≤ S.Qa g}
      (hA.span_good_eq_top hM hgA hne hQa) fun x ⟨g, hg, hgQ⟩ f hf =>
        hA.exists_conjLinear_transvection_of_le_Qa hgQ hg.symm hf
  exact hA.conj_hyp_of_resAt_surjective hM (hA.resAt_surjective hM hsurj) hgA hne hQa

end MaxEA

end CFSG.LargeExtraspecial.DW
