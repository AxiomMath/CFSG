module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6FactDefs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

private theorem sec5b513_mem_conj {H : Subgroup G} {g x : G} :
    x ∈ CFSG.conjugate H g ↔ g * x * g⁻¹ ∈ H := by
  rw [CFSG.conjugate, Subgroup.mem_map]
  constructor
  · rintro ⟨a, ha, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    have h : g * (g⁻¹ * a * g) * g⁻¹ = a := by group
    rwa [h]
  · intro hx
    refine ⟨g * x * g⁻¹, hx, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    group

private theorem sec5b513_orderOf_conj (g x : G) : orderOf (g * x * g⁻¹) = orderOf x := by
  have h := MulEquiv.orderOf_eq (MulAut.conj g) x
  simpa only [MulAut.conj_apply] using h

theorem sec5b513_conjugate_eq_iff {H : Subgroup G} {g : G} :
    CFSG.conjugate H g = H ↔ g ∈ normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  constructor
  · intro h x
    exact (Subgroup.ext_iff.mp h x).symm.trans sec5b513_mem_conj
  · intro h
    ext x
    exact sec5b513_mem_conj.trans (h x).symm

theorem sec5b513_mem_normalizer_inf {A B : Subgroup G} {g : G} (hA : g ∈ normalizer (A : Set G))
    (hB : g ∈ normalizer (B : Set G)) : g ∈ normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hA hB ⊢
  intro x
  rw [Subgroup.mem_inf, Subgroup.mem_inf, hA x, hB x]

theorem sec5b513_mem_normalizer_twoRes {H : Subgroup G} {g : G}
    (hg : g ∈ normalizer (H : Set G)) : g ∈ normalizer ((twoRes H : Subgroup G) : Set G) := by
  have h1 : g ∈ normalizer ({x : G | x ∈ H ∧ Odd (orderOf x)} : Set G) := by
    rw [Subgroup.mem_normalizer_iff] at hg
    rw [Subgroup.mem_set_normalizer_iff]
    intro x
    simp only [Set.mem_setOf_eq, sec5b513_orderOf_conj]
    rw [← hg x]
  exact Subgroup.normalizer_le_normalizer_closure _ h1

theorem sec5b513_twoRes_conjugate (H : Subgroup G) (g : G) :
    twoRes (CFSG.conjugate H g) = CFSG.conjugate (twoRes H) g := by
  unfold twoRes CFSG.conjugate
  rw [MonoidHom.map_closure]
  congr 1
  ext y
  simp only [Set.mem_setOf_eq, Set.mem_image, Subgroup.mem_map]
  have hord : ∀ x : G, orderOf ((MulAut.conj g⁻¹).toMonoidHom x) = orderOf x := fun x =>
    MulEquiv.orderOf_eq (MulAut.conj g⁻¹) x
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hodd⟩
    exact ⟨x, ⟨hx, by rwa [hord] at hodd⟩, rfl⟩
  · rintro ⟨x, ⟨hx, hodd⟩, rfl⟩
    exact ⟨⟨x, hx, rfl⟩, by rwa [hord]⟩

theorem sec5b513_conjugate_inf_centralizer (L : Subgroup G) {z x : G}
    (hx : x ∈ centralizer ({z} : Set G)) :
    CFSG.conjugate (L ⊓ centralizer ({z} : Set G)) x =
      CFSG.conjugate L x ⊓ centralizer ({z} : Set G) := by
  ext y
  rw [sec5b513_mem_conj, Subgroup.mem_inf, Subgroup.mem_inf, sec5b513_mem_conj]
  refine and_congr_right fun _ => ?_
  exact (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hx) y).symm

end CFSG.OddStandard.SmallF3.Omega
