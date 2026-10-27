module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryTransvectionGeneration

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open CFSG.LinearGroups
open scoped commutatorElement

variable {p f : ℕ} {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem unitary_perfect (h : UnitaryFieldData p f K) {B : V →ₛₗ[h.bar] V →ₗ[K] K}
    (hB : B.IsSymm) (hBl : B.SeparatingLeft) (hn : 3 ≤ Module.finrank K V)
    (hnq : (Module.finrank K V, p ^ f) ≠ (3, 2)) :
    Group.IsPerfect (sesqSpecialUnitaryGroup B) := by
  have : FiniteDimensional K V := FiniteDimensional.of_finrank_pos (by omega)
  set G := sesqSpecialUnitaryGroup B
  have hgen : Subgroup.closure (unitaryTransvections h B) = G :=
    unitary_transvection_generation h hB hBl (by omega) hnq
  have hle : G ≤ (commutator G).map G.subtype := by
    refine hgen.ge.trans ((Subgroup.closure_le _).mpr ?_)
    rintro _ ⟨a, ha, c, hc, rfl⟩
    obtain ⟨g₁, hg₁, g₂, hg₂, heq⟩ := unitary_transvection_commutator h hB hBl hn ha hc
    refine ⟨⁅(⟨g₁, hg₁⟩ : G), ⟨g₂, hg₂⟩⁆,
      Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _), ?_⟩
    rw [heq, commutatorElement_def]
    rfl
  refine ⟨eq_top_iff.mpr fun x _ => ?_⟩
  obtain ⟨y, hy, hyx⟩ := hle x.2
  rwa [show y = x from Subtype.ext hyx] at hy

end CFSG.LocalAnalysis.ComponentInitial
