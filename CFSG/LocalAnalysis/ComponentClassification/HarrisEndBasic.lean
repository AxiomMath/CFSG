module

public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitKG
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitKGField

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

namespace HarrisEnd

open CFSG Subgroup

instance layer_normal (G : Type*) [Group G] : (layer G).Normal :=
  @Subgroup.normal_of_characteristic _ _ _ LocalCores.layer_characteristic

section Conj

variable {G : Type} [Group G] (N : Subgroup G) [N.Normal]

abbrev conjOn : G →* MulAut ↥N := MulAut.conjNormal

theorem conjOn_apply (g : G) (n : N) : ((conjOn N g n : N) : G) = g * n * g⁻¹ :=
  MulAut.conjNormal_apply g n

variable {N}

theorem mem_fixedPoints_conjOn {g : G} {n : N} :
    n ∈ fixedPoints (conjOn N g) ↔ g * (n : G) = n * g := by
  rw [mem_fixedPoints, ← Subtype.coe_inj, conjOn_apply]
  constructor
  · intro h
    calc g * (n : G) = g * n * g⁻¹ * g := by group
      _ = n * g := by rw [h]
  · intro h
    rw [h]
    group

theorem map_fixedPoints_conjOn (g : G) :
    (fixedPoints (conjOn N g)).map N.subtype = N ⊓ centralizer {g} := by
  ext x
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n.2, mem_centralizer_singleton_iff.mpr (mem_fixedPoints_conjOn.mp hn).symm⟩
  · rintro ⟨hxN, hx⟩
    exact ⟨⟨x, hxN⟩, mem_fixedPoints_conjOn.mpr (mem_centralizer_singleton_iff.mp hx).symm, rfl⟩

theorem fixedPoints_conjOn_eq (g : G) :
    fixedPoints (conjOn N g) = (centralizer ({g} : Set G)).subgroupOf N := by
  ext n
  rw [mem_fixedPoints_conjOn, mem_subgroupOf, mem_centralizer_singleton_iff, eq_comm]

theorem conjOn_eq_one_iff {g : G} : conjOn N g = 1 ↔ g ∈ centralizer (N : Set G) := by
  rw [mem_centralizer_iff]
  constructor
  · intro h n hn
    have h1 := congrArg (fun φ : MulAut ↥N => ((φ ⟨n, hn⟩ : N) : G)) h
    simp only [conjOn_apply, MulAut.one_apply] at h1
    calc n * g = g * n * g⁻¹ * g := by rw [h1]
      _ = g * n := by group
  · intro h
    ext n
    rw [conjOn_apply, MulAut.one_apply, ← h n n.2]
    group

theorem conjOn_mem_innAut_iff {g : G} :
    conjOn N g ∈ innAut ↥N ↔ ∃ n ∈ N, g * n⁻¹ ∈ centralizer (N : Set G) := by
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, n.2, mem_centralizer_iff.mpr fun m hm => ?_⟩
    have key : ∀ y : N, g * (y : G) * g⁻¹ = n * y * n⁻¹ := fun y => by
      have h1 := congrArg (fun φ : MulAut ↥N => ((φ y : N) : G)) hn
      simp only [conjOn_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] at h1
      exact h1.symm
    have h2 := key ⟨(n : G)⁻¹ * m * n, N.mul_mem (N.mul_mem (N.inv_mem n.2) hm) n.2⟩
    simp only at h2
    calc m * (g * (n : G)⁻¹) = g * ((n : G)⁻¹ * m * n) * g⁻¹ * (g * (n : G)⁻¹) := by
          rw [h2, InvMemClass.coe_inv]; group
      _ = g * (n : G)⁻¹ * m := by group
  · rintro ⟨n, hn, hc⟩
    refine ⟨⟨n, hn⟩, ?_⟩
    have h1 := conjOn_eq_one_iff.mpr hc
    rw [map_mul, map_inv, mul_inv_eq_one] at h1
    rw [h1]
    ext x
    simp

end Conj

end HarrisEnd

end CFSG.ComponentClassification.HarrisLit
