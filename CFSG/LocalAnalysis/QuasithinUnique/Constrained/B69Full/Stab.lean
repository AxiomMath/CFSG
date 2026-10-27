module

public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Algebra.Group.Action.End
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Data.Finset.Attr
public import Mathlib.GroupTheory.GroupAction.Defs

public section

namespace CFSG.Quasithin

theorem nonempty_mulEquiv_stabilizer_perm (n : ℕ) (p : Fin (n + 1)) :
    Nonempty (↥(MulAction.stabilizer (Equiv.Perm (Fin (n + 1))) p) ≃* Equiv.Perm (Fin n)) := by
  have hrange : (Equiv.Perm.ofSubtype :
      Equiv.Perm {x : Fin (n + 1) // x ≠ p} →* Equiv.Perm (Fin (n + 1))).range
      = MulAction.stabilizer (Equiv.Perm (Fin (n + 1))) p := by
    ext x
    rw [MonoidHom.mem_range, MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def]
    constructor
    · rintro ⟨y, rfl⟩
      exact Equiv.Perm.ofSubtype_apply_of_not_mem (a := p) y (fun h => h rfl)
    · intro hx
      have key : ∀ y, x y ≠ p ↔ y ≠ p := fun y => by
        constructor
        · intro h1 h2
          apply h1
          rw [h2, hx]
        · intro h1 h2
          apply h1
          have hxy : x y = x p := by rw [h2, hx]
          exact x.injective hxy
      refine ⟨Equiv.Perm.subtypePerm (p := fun y : Fin (n + 1) => y ≠ p) x key, ?_⟩
      exact Equiv.Perm.ofSubtype_subtypePerm (p := fun y : Fin (n + 1) => y ≠ p) key
        (fun y hy hyp => hy (by rw [hyp, hx]))
  have hinj : Function.Injective
      (Equiv.Perm.ofSubtype :
        Equiv.Perm {x : Fin (n + 1) // x ≠ p} →* Equiv.Perm (Fin (n + 1))) :=
    Equiv.Perm.ofSubtype_injective
  let eS : ↥(MulAction.stabilizer (Equiv.Perm (Fin (n + 1))) p) ≃*
      Equiv.Perm {x : Fin (n + 1) // x ≠ p} :=
    (MulEquiv.subgroupCongr hrange).symm.trans (MonoidHom.ofInjective hinj).symm
  exact ⟨eS.trans (finSuccAboveEquiv p).permCongrHom.symm⟩

end CFSG.Quasithin
