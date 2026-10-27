module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Helpers
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.GH74.GLS.Stage1.Thm6.Prod.Transport

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
open scoped commutatorElement

section Transport

variable {G : Type} [Group G]

theorem LC_conj_mem [Finite G] {z g : G} (hg : g ∈ Cen z) {x : G} (hx : x ∈ LC z) :
    g * x * g⁻¹ ∈ LC z := by
  have hxC : x ∈ Cen z := Subgroup.map_subtype_le _ hx
  have hN := Stage1.Thm6.Prod.LC_normal z
  have hx' : (⟨x, hxC⟩ : ↥(Cen z)) ∈ (LC z).subgroupOf (Cen z) := hx
  exact hN.conj_mem _ hx' ⟨g, hg⟩

theorem conjugate_le_LC [Finite G] {z g : G} (hg : g ∈ Cen z) {V : Subgroup G} (h : V ≤ LC z) :
    conjugate V g ≤ LC z := by
  intro w hw
  rw [mem_conjugate_iff] at hw
  have h1 := LC_conj_mem (Subgroup.inv_mem _ hg) (h hw)
  have e : g⁻¹ * (g * w * g⁻¹) * g⁻¹⁻¹ = w := by group
  rwa [e] at h1

omit [Group G] in
theorem isElementaryAbelian_of_mulEquiv {p : ℕ} {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    [IsElementaryAbelian p A] : IsElementaryAbelian p B :=
  CFSG.IsElementaryAbelian.of_mulEquiv e inferInstance

theorem isFour_conjugate {V : Subgroup G} (g : G) (h : IVK.IsFourSubgroup V) :
    IVK.IsFourSubgroup (conjugate V g) := by
  have e : ↥V ≃* ↥(conjugate V g) :=
    Subgroup.equivMapOfInjective V (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective
  have : IsElementaryAbelian 2 ↥V := h.1
  refine ⟨isElementaryAbelian_of_mulEquiv e, ?_⟩
  rw [← h.2]
  exact (Nat.card_congr e.toEquiv).symm

theorem centralizer_conjugate (V : Subgroup G) (g : G) :
    centralizer ((conjugate V g : Subgroup G) : Set G) = conjugate (centralizer (V : Set G)) g := by
  ext x
  rw [mem_conjugate_iff, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h v hv
    have hu : g⁻¹ * v * g ∈ (conjugate V g : Subgroup G) := by
      rw [mem_conjugate_iff]
      have e : g * (g⁻¹ * v * g) * g⁻¹ = v := by group
      rw [e]
      exact hv
    have := h _ hu
    calc v * (g * x * g⁻¹) = g * ((g⁻¹ * v * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * v * g)) * g⁻¹ := by rw [this]
      _ = (g * x * g⁻¹) * v := by group
  · intro h u hu
    have hu' : g * u * g⁻¹ ∈ V := (mem_conjugate_iff.mp hu)
    have := h _ hu'
    calc u * x = g⁻¹ * ((g * u * g⁻¹) * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * x * g⁻¹) * (g * u * g⁻¹)) * g := by rw [this]
      _ = x * u := by group

theorem normalizer_conjugate (V : Subgroup G) (g : G) :
    normalizer ((conjugate V g : Subgroup G) : Set G) = conjugate (normalizer (V : Set G)) g :=
  (Subgroup.map_normalizer_eq_of_bijective V (f := (MulAut.conj g⁻¹).toMonoidHom)
    (MulAut.conj g⁻¹).bijective).symm

theorem conjugate_self {A : Subgroup G} {g : G} (hg : g ∈ A) : conjugate A g = A := by
  ext x
  rw [mem_conjugate_iff]
  constructor
  · intro h
    have := A.mul_mem (A.mul_mem (A.inv_mem hg) h) hg
    simpa [mul_assoc] using this
  · intro h
    exact A.mul_mem (A.mul_mem hg h) (A.inv_mem hg)

theorem autOrd_conjugate {A V : Subgroup G} {g : G} (hg : g ∈ A) :
    AutOrd A (conjugate V g) = AutOrd A V := by
  unfold AutOrd
  rw [centralizer_conjugate, normalizer_conjugate]
  have hinj : Function.Injective (MulAut.conj g⁻¹).toMonoidHom := (MulAut.conj g⁻¹).injective
  have hA := conjugate_self hg
  have e : ∀ X : Subgroup G, conjugate X g ⊓ A = conjugate (X ⊓ A) g := fun X => by
    have h1 : conjugate (X ⊓ A) g = conjugate X g ⊓ conjugate A g := Subgroup.map_inf_eq _ _ _ hinj
    rw [h1, hA]
  rw [e, e]
  exact Subgroup.relIndex_map_map_of_injective _ _ hinj

end Transport

end CFSG.GH74.GLS.Stage2.Bender.Thm1
