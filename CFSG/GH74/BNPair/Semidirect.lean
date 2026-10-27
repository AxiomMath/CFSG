module

public import Mathlib.GroupTheory.Frattini
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.GH74.BNPair

universe u

open scoped commutatorElement

section Frattini

variable (Q : Type*) [Group Q]

@[expose] noncomputable def frattiniAutHom : MulAut Q →* MulAut (Q ⧸ frattini Q) where
  toFun σ := QuotientGroup.congr (frattini Q) (frattini Q) σ
    (Subgroup.characteristic_iff_map_eq.mp inferInstance σ)
  map_one' := by
    ext x
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    rfl
  map_mul' σ τ := by
    ext x
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    rfl

end Frattini

section Regular

variable {X : Type*} [Group X]

@[expose] def frattiniIn (Q : Subgroup X) : Subgroup X :=
  (frattini Q).map Q.subtype

instance frattiniIn_normal (Q : Subgroup X) [Q.Normal] : (frattiniIn Q).Normal where
  conj_mem := by
    intro x hx g
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    refine Subgroup.mem_map.2 ⟨MulAut.conjNormal g y, ?_, ?_⟩
    · have := Subgroup.characteristic_iff_map_eq.mp (inferInstance : (frattini Q).Characteristic)
        (MulAut.conjNormal g)
      rw [← this]
      exact Subgroup.mem_map_of_mem _ hy
    · rfl

end Regular


end CFSG.GH74.BNPair
