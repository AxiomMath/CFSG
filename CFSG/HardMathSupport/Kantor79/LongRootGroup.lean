module

public import CFSG.HardMathSupport.Kantor79.LongRoot

public section

namespace CFSG.HardMathSupport.Kantor79

open CFSG.HardMathSupport.GuralnickMalle QuadraticMap LinearMap Module

variable {K E : Type*} [Field K] [CharP K 2] [AddCommGroup E] [Module K E]

noncomputable def longRootGroup (Q : QuadraticForm K E) (a b : E) (ha : Q a = 0) (hb : Q b = 0)
    (hab : QuadraticMap.polarBilin Q a b = 0) : Subgroup (E ≃ₗ[K] E) where
  carrier := Set.range fun c : K => siegelEquiv Q a b ha hb hab c
  one_mem' := ⟨0, siegelEquiv_zero Q a b ha hb hab⟩
  mul_mem' := by
    rintro _ _ ⟨c, rfl⟩ ⟨d, rfl⟩
    exact ⟨c + d, (siegelEquiv_mul Q a b ha hb hab c d).symm⟩
  inv_mem' := by
    rintro _ ⟨c, rfl⟩
    exact ⟨c, (siegelEquiv_inv Q a b ha hb hab c).symm⟩

theorem mem_longRootGroup_iff {Q : QuadraticForm K E} {a b : E} {ha : Q a = 0} {hb : Q b = 0}
    {hab : QuadraticMap.polarBilin Q a b = 0} {g : E ≃ₗ[K] E} :
    g ∈ longRootGroup Q a b ha hb hab ↔ ∃ c : K, siegelEquiv Q a b ha hb hab c = g :=
  Iff.rfl

theorem siegelEquiv_mem_longRootGroup {Q : QuadraticForm K E} {a b : E} {ha : Q a = 0}
    {hb : Q b = 0} {hab : QuadraticMap.polarBilin Q a b = 0} (c : K) :
    siegelEquiv Q a b ha hb hab c ∈ longRootGroup Q a b ha hb hab :=
  ⟨c, rfl⟩

theorem mem_longRootGroup_isLongRootElement {Q : QuadraticForm K E} {a b : E} {ha : Q a = 0}
    {hb : Q b = 0} {hab : QuadraticMap.polarBilin Q a b = 0}
    (hnd : ∀ x, (∀ y, polar Q x y = 0) → x = 0) (hli : LinearIndependent K ![a, b])
    {g : E ≃ₗ[K] E} (hg : g ∈ longRootGroup Q a b ha hb hab) (h1 : g ≠ 1) :
    IsLongRootElement Q g ∧ movedSpace g = Submodule.span K ({a, b} : Set E) := by
  obtain ⟨c, rfl⟩ := mem_longRootGroup_iff.mp hg
  have hc : c ≠ 0 := by
    rintro rfl
    exact h1 (siegelEquiv_zero Q a b ha hb hab)
  exact isLongRootElement_siegelEquiv Q a b ha hb hab hnd hli hc

end CFSG.HardMathSupport.Kantor79
