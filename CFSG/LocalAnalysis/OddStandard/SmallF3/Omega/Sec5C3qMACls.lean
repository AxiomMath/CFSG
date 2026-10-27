module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5BAab
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5BZClass
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5CHInv

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z r : G}
  {B A K₁ K₂ : Subgroup G} {h : G}

theorem sec5c3qma_A₂_conj (hS : Asc82SchurU43) (c : Sec5HCtx G t L S z r B A K₁ K₂ h) {x : G}
    (hxA : x ∈ A) (hxK : x ∈ CFSG.conjugate K₁ h ⊔ CFSG.conjugate K₂ h) (hx1 : x ≠ 1)
    (hxz : x ≠ z) : ∃ g : G, x = g * (t * z) * g⁻¹ := by
  have hR : Sec5RCtx G t L S z r B A := c.toSec5RCtx
  have hC : Sec5Ctx G t L S z := hR.toSec5Ctx
  have hΩ : IsOm6Z2 L := hC.toSec5Setting.isOm6Z2
  have hhz : h * z = z * h := Subgroup.mem_centralizer_singleton_iff.mp c.h_z
  have hyK : h * x * h⁻¹ ∈ K₁ ⊔ K₂ := by
    rw [← sec5b_conjugate_sup] at hxK
    exact sec5b_mem_conjugate_iff.mp hxK
  have hyA : h * x * h⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp c.h_mem x).mp hxA
  have hy1 : h * x * h⁻¹ ≠ 1 := by
    intro hy
    apply hx1
    calc x = h⁻¹ * (h * x * h⁻¹) * h := by group
      _ = 1 := by rw [hy]; group
  have hyz : h * x * h⁻¹ ≠ z := by
    intro hy
    apply hxz
    calc x = h⁻¹ * (h * x * h⁻¹) * h := by group
      _ = h⁻¹ * z * h := by rw [hy]
      _ = h⁻¹ * (z * h) := by group
      _ = h⁻¹ * (h * z) := by rw [hhz]
      _ = z := by group
  have hyTwo : h * x * h⁻¹ ∈ twoRes (L ⊓ centralizer ({z} : Set G)) := c.prod ▸ hyK
  obtain ⟨-, hsq⟩ := sec5b_A_elemAb hR
  have hord : orderOf (h * x * h⁻¹) = 2 :=
    orderOf_eq_prime (by rw [sq]; exact hsq _ hyA) hy1
  obtain ⟨g, -, hg⟩ := (asc82Fact512H_of hS).inv_class G L hΩ t hC.involution c.centre z c.pocket
    _ hyTwo hord hyz
  refine ⟨h⁻¹ * g, ?_⟩
  calc x = h⁻¹ * (h * x * h⁻¹) * h := by group
    _ = h⁻¹ * (g * (t * z) * g⁻¹) * h := by rw [hg]
    _ = (h⁻¹ * g) * (t * z) * (h⁻¹ * g)⁻¹ := by group

theorem sec5c3qma_wt_ne (hS : Asc82SchurU43) (hy : Sec5B59Hyp)
    (c : Sec5HCtx G t L S z r B A K₁ K₂ h) {φ : (Fin 6 → ZMod 2) → G}
    (hm : Sec5Model58 t L z r A φ) {v : Fin 6 → ZMod 2}
    (hvK : φ v ∈ CFSG.conjugate K₁ h ⊔ CFSG.conjugate K₂ h) (hv1 : φ v ≠ 1) (hvz : φ v ≠ z) :
    vecWeight v ≠ 3 ∧ vecWeight v ≠ 4 := by
  obtain ⟨g, hg⟩ := sec5c3qma_A₂_conj hS c (hm.perm.mem v) hvK hv1 hvz
  have hnot : φ v ∉ wclass φ 3 ∪ wclass φ 4 := by
    intro hmem
    rw [← sec5b_zM_eq hy c.toSec5RCtx hm] at hmem
    obtain ⟨m, -, hmz⟩ := hmem
    refine sec5_tz_not_conj_z hy.h36 hy.h37 hy.h52b hy.h53 hy.tab c.toSec5Ctx (m⁻¹ * g) ?_
    calc (m⁻¹ * g)⁻¹ * z * (m⁻¹ * g) = g⁻¹ * (m * z * m⁻¹) * g := by group
      _ = g⁻¹ * φ v * g := by rw [hmz]
      _ = t * z := by rw [hg]; group
  exact ⟨fun h3 => hnot (Or.inl ⟨v, h3, rfl⟩), fun h4 => hnot (Or.inr ⟨v, h4, rfl⟩)⟩

end CFSG.OddStandard.SmallF3.Omega
