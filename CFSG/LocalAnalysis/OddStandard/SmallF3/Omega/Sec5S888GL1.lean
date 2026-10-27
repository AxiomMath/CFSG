module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888R2

public section

open Subgroup

namespace CFSG.OddStandard.SmallF3.Omega

variable {G : Type} [Group G]

private theorem s888_gl1_isCyclic_sylow_of_le [Finite G] {D C : Subgroup G} (hDC : D ≤ C)
    (hC : ∀ P : Sylow 2 ↥C, IsCyclic (P : Subgroup ↥C)) :
    ∀ P : Sylow 2 ↥D, IsCyclic (P : Subgroup ↥D) := by
  intro P
  have hinj : Function.Injective (Subgroup.inclusion hDC) := Subgroup.inclusion_injective hDC
  obtain ⟨Q, hle⟩ := (P.isPGroup'.map (Subgroup.inclusion hDC)).exists_le_sylow
  haveI : IsCyclic ↥(Q : Subgroup ↥C) := hC Q
  have hcyc' : IsCyclic ↥((P : Subgroup ↥D).map (Subgroup.inclusion hDC)) :=
    Subgroup.isCyclic_of_le hle
  exact isCyclic_of_surjective
    (Subgroup.equivMapOfInjective (P : Subgroup ↥D) (Subgroup.inclusion hDC) hinj).symm
    (MulEquiv.surjective _)

private theorem s888_gl1_isCyclic_sylow_of_surjective {A B : Type*} [Group A] [Group B]
    [Finite A] (f : A →* B) (hf : Function.Surjective f)
    (hA : ∀ P : Sylow 2 A, IsCyclic (P : Subgroup A)) :
    ∀ Q : Sylow 2 B, IsCyclic (Q : Subgroup B) := by
  intro Q
  obtain ⟨P, hP⟩ := Sylow.mapSurjective_surjective (p := 2) hf Q
  rw [← hP, Sylow.coe_mapSurjective]
  haveI : IsCyclic ↥(P : Subgroup A) := hA P
  exact isCyclic_of_surjective (f.subgroupMap (P : Subgroup A))
    (f.subgroupMap_surjective (P : Subgroup A))

theorem relIndex_le_two_of_cyclic_sylow [Finite G] {C Y Y₀ Z : Subgroup G} (hYY : Y ≤ Y₀)
    (hcyc : ∀ P : Sylow 2 ↥Y₀, IsCyclic (P : Subgroup ↥Y₀))
    (hCY : ∀ y ∈ Y, ∀ c ∈ C, y * c * y⁻¹ ∈ C)
    (hZ : ∀ u ∈ Z, ∃ y ∈ Y, ∃ c ∈ C, u = y * c) (hab : IsElemAbelianModSub C Z) :
    C.relIndex Z ≤ 2 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let M : Subgroup G := Subgroup.normalizer (C : Set G)
  have hCM : C ≤ M := Subgroup.le_normalizer
  have hYM : Y ≤ M := Subgroup.le_normalizer_iff.mpr hCY
  have hZM : Z ≤ M := by
    intro u hu
    obtain ⟨y, hy, c, hc, rfl⟩ := hZ u hu
    exact M.mul_mem (hYM hy) (hCM hc)
  haveI hCnormal : (C.subgroupOf M).Normal := Subgroup.normal_in_normalizer
  let π : ↥M →* (↥M ⧸ C.subgroupOf M) := QuotientGroup.mk' (C.subgroupOf M)
  let Zb : Subgroup (↥M ⧸ C.subgroupOf M) := (Z.subgroupOf M).map π
  let Yb : Subgroup (↥M ⧸ C.subgroupOf M) := (Y.subgroupOf M).map π
  have hker : π.ker = C.subgroupOf M := QuotientGroup.ker_mk' _
  haveI : Finite (↥M ⧸ C.subgroupOf M) :=
    ((finite_iff_subgroup_quotient (C.subgroupOf M)).mp inferInstance).2
  have hcard : C.relIndex Z = Nat.card ↥Zb := by
    rw [show Zb = (Z.subgroupOf M).map π from rfl,
      ← Subgroup.relIndex_ker (f := π) (K := Z.subgroupOf M), hker]
    exact (Subgroup.relIndex_subgroupOf hZM).symm
  have hZble : Zb ≤ Yb := by
    intro x hx
    rw [show Zb = (Z.subgroupOf M).map π from rfl] at hx
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    have haZ : (a : G) ∈ Z := Subgroup.mem_subgroupOf.mp ha
    obtain ⟨y, hy, c, hc, hayc⟩ := hZ (a : G) haZ
    have hyM : y ∈ M := hYM hy
    have hcM : c ∈ M := hCM hc
    have haeq : a = (⟨y, hyM⟩ : ↥M) * ⟨c, hcM⟩ := Subtype.ext hayc
    have hc1 : π ⟨c, hcM⟩ = 1 := by
      rw [← MonoidHom.mem_ker, hker]
      exact Subgroup.mem_subgroupOf.mpr hc
    rw [haeq, map_mul, hc1, mul_one]
    exact Subgroup.mem_map.mpr ⟨⟨y, hyM⟩, Subgroup.mem_subgroupOf.mpr hy, rfl⟩
  have hYbcyc : ∀ Q : Sylow 2 ↥Yb, IsCyclic (Q : Subgroup ↥Yb) := by
    let ψ : ↥Y →* ↥Yb :=
      { toFun := fun y =>
          ⟨π ⟨y, hYM y.2⟩,
            Subgroup.mem_map.mpr ⟨⟨y, hYM y.2⟩, Subgroup.mem_subgroupOf.mpr y.2, rfl⟩⟩
        map_one' := by
          apply Subtype.ext
          change π (1 : ↥M) = 1
          rw [map_one]
        map_mul' := by
          intro a b
          apply Subtype.ext
          simp only [Subgroup.coe_mul, map_mul]
          rfl }
    have hψ : Function.Surjective ψ := by
      intro x
      obtain ⟨a, ha, hax⟩ := Subgroup.mem_map.mp x.2
      refine ⟨⟨(a : G), Subgroup.mem_subgroupOf.mp ha⟩, Subtype.ext ?_⟩
      show π ⟨(a : G), hYM (Subgroup.mem_subgroupOf.mp ha)⟩ = (x : ↥M ⧸ C.subgroupOf M)
      rw [show (⟨(a : G), hYM (Subgroup.mem_subgroupOf.mp ha)⟩ : ↥M) = a from Subtype.ext rfl]
      exact hax
    exact s888_gl1_isCyclic_sylow_of_surjective ψ hψ (s888_gl1_isCyclic_sylow_of_le hYY hcyc)
  have hsq : ∀ x ∈ Zb, x * x = 1 := by
    intro x hx
    rw [show Zb = (Z.subgroupOf M).map π from rfl] at hx
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    have haZ : (a : G) ∈ Z := Subgroup.mem_subgroupOf.mp ha
    have haa : (a : G) * (a : G) ∈ C := (hab (a : G) haZ (a : G) haZ).2
    have hmem : (a : ↥M) * a ∈ C.subgroupOf M :=
      Subgroup.mem_subgroupOf.mpr (by simpa using haa)
    rw [← map_mul, ← MonoidHom.mem_ker, hker]
    exact hmem
  have hle : Nat.card ↥Zb ≤ 2 := card_le_two_of_sq_eq_one hZble hYbcyc hsq
  rw [hcard]
  exact hle

end CFSG.OddStandard.SmallF3.Omega
