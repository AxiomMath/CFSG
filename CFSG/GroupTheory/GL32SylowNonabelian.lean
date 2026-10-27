module

public import CFSG.Quasithin.Vol2.Ch12Sec7IdentSL32

public section

namespace CFSG.GroupTheory

open Subgroup
open scoped Pointwise
open CFSG.Quasithin.H13.I1277 CFSG.LargeExtraspecial.DW.W3

theorem exists_not_commute_of_sylow_two_of_mulEquiv_GL32 {X : Type*} [Group X] [Finite X]
    (e : X ≃* GL (Fin 3) (ZMod 2)) (P : Sylow 2 X) :
    ∃ x ∈ (P : Subgroup X), ∃ y ∈ (P : Subgroup X), x * y ≠ y * x := by
  classical
  let D : Sylow 2 (GL (Fin 3) (ZMod 2)) :=
    IsPGroup.toSylow dih_isPGroup dih_index_not_dvd
  have key : ∀ Q : Sylow 2 (GL (Fin 3) (ZMod 2)),
      ∃ x ∈ (Q : Subgroup (GL (Fin 3) (ZMod 2))),
        ∃ y ∈ (Q : Subgroup (GL (Fin 3) (ZMod 2))), x * y ≠ y * x := by
    intro Q
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (GL (Fin 3) (ZMod 2)) D Q
    have hQD : (Q : Subgroup (GL (Fin 3) (ZMod 2))) = MulAut.conj g • dih := by
      rw [← hg, Sylow.coe_subgroup_smul]
      rfl
    refine ⟨MulAut.conj g sU, ?_, MulAut.conj g tU, ?_, ?_⟩
    · rw [hQD]
      exact Subgroup.smul_mem_pointwise_smul _ _ _ sU_mem_dih
    · rw [hQD]
      exact Subgroup.smul_mem_pointwise_smul _ _ _ tU_mem_dih
    · intro h
      apply sU_mul_tU_ne
      have h' : MulAut.conj g (sU * tU) = MulAut.conj g (tU * sU) := by
        rw [map_mul, map_mul]
        exact h
      exact (MulAut.conj g).injective h'
  let Q : Sylow 2 (GL (Fin 3) (ZMod 2)) :=
    P.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨x₀, hx₀, y₀, hy₀, hxy₀⟩ := key Q
  have hQ : (Q : Subgroup (GL (Fin 3) (ZMod 2))) = (P : Subgroup X).map e.toMonoidHom :=
    Sylow.coe_mapSurjective (f := e.toMonoidHom) e.surjective P
  rw [hQ] at hx₀ hy₀
  obtain ⟨x, hxP, hx⟩ := Subgroup.mem_map.mp hx₀
  obtain ⟨y, hyP, hy⟩ := Subgroup.mem_map.mp hy₀
  refine ⟨x, hxP, y, hyP, ?_⟩
  intro hxy
  apply hxy₀
  rw [← hx, ← hy, ← map_mul, ← map_mul, hxy]

end CFSG.GroupTheory
