module

public import CFSG.ClassicalInvolution.Q3.Q3T8B17S
public import CFSG.ClassicalInvolution.Q3.Q3T8B17M
public import CFSG.ClassicalInvolution.Q3.Q3PPFundPSL3

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Uniform CFSG.Blueprint
open scoped MatrixGroups

section Iso

variable {Q Q' : Type} [Group Q] [Group Q']

theorem LinkModelFacts.of_mulEquiv (e : Q ≃* Q') (h : LinkModelFacts Q') : LinkModelFacts Q := by
  refine ⟨fun u v hu hu1 hv hv1 => ?_, fun u v hu hu1 hv hv1 huv hcomm => ?_⟩
  · obtain ⟨g, hg⟩ := h.1 (e u) (e v) (by rw [← map_mul, hu, map_one])
      ((e.map_ne_one_iff).mpr hu1) (by rw [← map_mul, hv, map_one]) ((e.map_ne_one_iff).mpr hv1)
    refine ⟨e.symm g, e.injective ?_⟩
    simpa using hg
  · have hgen := h.2 (e u) (e v) (by rw [← map_mul, hu, map_one]) ((e.map_ne_one_iff).mpr hu1)
      (by rw [← map_mul, hv, map_one]) ((e.map_ne_one_iff).mpr hv1) (e.injective.ne huv)
      (by rw [← map_mul, ← map_mul, hcomm])
    have hcent : ∀ x : Q, Subgroup.centralizer ({e x} : Set Q') ≤
        (Subgroup.centralizer ({x} : Set Q)).map e.toMonoidHom := by
      intro x y hy
      refine Subgroup.mem_map.mpr ⟨e.symm y, ?_, by simp⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
      apply e.injective
      simpa using hy
    have hmap : (⊤ : Subgroup Q') ≤
        (Subgroup.centralizer ({u} : Set Q) ⊔ Subgroup.centralizer ({v} : Set Q) ⊔
          Subgroup.centralizer ({u * v} : Set Q)).map e.toMonoidHom := by
      rw [← hgen]
      refine sup_le (sup_le ?_ ?_) ?_
      · exact (hcent u).trans (Subgroup.map_mono (le_sup_of_le_left le_sup_left))
      · exact (hcent v).trans (Subgroup.map_mono (le_sup_of_le_left le_sup_right))
      · rw [← map_mul]
        exact (hcent (u * v)).trans (Subgroup.map_mono le_sup_right)
    rw [eq_top_iff]
    intro x _
    obtain ⟨y, hyW, hyx⟩ := hmap (Subgroup.mem_top (e x))
    have hxy : y = x := e.injective hyx
    rwa [hxy] at hyW

end Iso

section Sections

variable {Y : Type} [Group Y] {Φ : Set (Subgroup Y)}

theorem linkModelFacts_of_psl (D : LieSystemDataU 3 1 (Fin 1) Y Φ)
    (hc : CompIs 3 1 (D.kind 0) .PSL 3) : LinkModelFacts Y := by
  obtain ⟨e, he, -, -, hc'⟩ := hc
  have he1 : e = 1 := by
    rcases he with h | ⟨h, -⟩
    · exact h
    · exact absurd h (by decide)
  subst he1
  have hsurj : Function.Surjective (D.hom 0) := Q3T6.lieSystemDataU_surjective_hom D 0
  have hsurj' : Function.Surjective (castHom hc' (D.hom 0)) := by
    rw [← MonoidHom.range_eq_top, range_castHom, MonoidHom.range_eq_top]
    exact hsurj
  have hker := castHom_ker_le_center hc' _ (D.ker_le_center 0)
  have hZ : Subgroup.center SL(3, GaloisField 3 1) = ⊥ :=
    Q3PP.center_sl3_eq_bot Q3PP.natCard_gf3
  have hinj : Function.Injective (castHom hc' (D.hom 0)) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hker.trans hZ.le
  exact LinkModelFacts.of_mulEquiv
    (MulEquiv.ofBijective (castHom hc' (D.hom 0)) ⟨hinj, hsurj'⟩).symm
    (linkModelFacts_sl3 Q3PP.natCard_gf3)

theorem linkModelFacts_of_m11 (D : LieSystemDataU 3 1 (Fin 1) Y Φ)
    (hc : D.kind 0 = Q3.CompData.m11) : LinkModelFacts Y := by
  have hsurj : Function.Surjective (D.hom 0) := Q3T6.lieSystemDataU_surjective_hom D 0
  have hsurj' : Function.Surjective (castHom hc (D.hom 0)) := by
    rw [← MonoidHom.range_eq_top, range_castHom, MonoidHom.range_eq_top]
    exact hsurj
  have hker := castHom_ker_le_center hc _ (D.ker_le_center 0)
  have hZ : Subgroup.center ↥NativeSporadic.M11 = ⊥ := Q3.center_m11_eq_bot Q3.m11Facts
  have hinj : Function.Injective (castHom hc (D.hom 0)) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hker.trans hZ.le
  exact LinkModelFacts.of_mulEquiv
    (MulEquiv.ofBijective (castHom hc (D.hom 0)) ⟨hinj, hsurj'⟩).symm linkModelFacts_m11

end Sections

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77
