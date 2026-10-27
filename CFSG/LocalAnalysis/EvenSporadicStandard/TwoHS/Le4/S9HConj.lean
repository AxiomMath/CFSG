module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S8Coord

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup Matrix

namespace ECoord

variable {G : Type*} [Group G]

@[expose] noncomputable def conj (C : ECoord G) (g : G) : ECoord G where
  E := C.E.map (MulAut.conj g).toMonoidHom
  φ := (MulEquiv.subgroupMap (MulAut.conj g) C.E).symm.trans C.φ

theorem mem_conj_E (C : ECoord G) (g : G) (x : G) : x ∈ (C.conj g).E ↔ g⁻¹ * x * g ∈ C.E :=
  Subgroup.mem_map_equiv (f := MulAut.conj g)

theorem elt_conj (C : ECoord G) (g : G) (v : V4) : (C.conj g).elt v = g * C.elt v * g⁻¹ := rfl

theorem vec_conj_of_mem (C : ECoord G) (g : G) {e : G} (he : e ∈ C.E) :
    (C.conj g).vec (g * e * g⁻¹) = C.vec e := by
  have h : g * e * g⁻¹ = (C.conj g).elt (C.vec e) := by
    rw [elt_conj, C.elt_vec he]
  rw [h, (C.conj g).vec_elt]

theorem normalizer_conj (C : ECoord G) (g : G) {x : G} :
    x ∈ normalizer ((C.conj g).E : Set G) ↔ g⁻¹ * x * g ∈ normalizer (C.E : Set G) := by
  rw [mem_normalizer_iff, mem_normalizer_iff]
  constructor
  · intro h h'
    have h1 := h (g * h' * g⁻¹)
    rw [mem_conj_E, mem_conj_E] at h1
    have e1 : g⁻¹ * (g * h' * g⁻¹) * g = h' := by group
    have e2 : g⁻¹ * (x * (g * h' * g⁻¹) * x⁻¹) * g = g⁻¹ * x * g * h' * (g⁻¹ * x * g)⁻¹ := by
      group
    rwa [e1, e2] at h1
  · intro h h'
    have h1 := h (g⁻¹ * h' * g)
    rw [mem_conj_E, mem_conj_E]
    have e2 : g⁻¹ * (x * h' * x⁻¹) * g = g⁻¹ * x * g * (g⁻¹ * h' * g) * (g⁻¹ * x * g)⁻¹ := by
      group
    rwa [e2]

theorem act_conj (C : ECoord G) (g : G) {x : G} (hx : g⁻¹ * x * g ∈ normalizer (C.E : Set G))
    (v : V4) : (C.conj g).act x v = C.act (g⁻¹ * x * g) v := by
  have hmem : g⁻¹ * x * g * C.elt v * (g⁻¹ * x * g)⁻¹ ∈ C.E :=
    (mem_normalizer_iff.1 hx (C.elt v)).1 (C.elt_mem v)
  have e : x * (C.conj g).elt v * x⁻¹ = g * (g⁻¹ * x * g * C.elt v * (g⁻¹ * x * g)⁻¹) * g⁻¹ := by
    rw [elt_conj]
    group
  rw [act, e, vec_conj_of_mem C g hmem]
  rfl

theorem mat_conj (C : ECoord G) (g : G) {x : G} (hx : g⁻¹ * x * g ∈ normalizer (C.E : Set G)) :
    (C.conj g).mat x = C.mat (g⁻¹ * x * g) := by
  ext i j
  simp only [mat, Matrix.of_apply, act_conj C g hx]

end ECoord

end CFSG.EvenSporadicStandard.TwoHS
