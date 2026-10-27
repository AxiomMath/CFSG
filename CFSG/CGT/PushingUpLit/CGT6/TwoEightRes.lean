module

public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Subgroup.Defs

public section

namespace CFSG.CGT.PushingUpLit.CGT6.TwoEight

section Res

variable {V : Type*} [CommGroup V] (P : Subgroup V)

@[expose] def stabP : Subgroup (MulAut V) where
  carrier := {g | ∀ p ∈ P, g p ∈ P ∧ g⁻¹ p ∈ P}
  one_mem' := fun p hp => ⟨hp, hp⟩
  mul_mem' := by
    rintro g h hg hh p hp
    refine ⟨?_, ?_⟩
    · exact (hg _ (hh p hp).1).1
    · rw [mul_inv_rev, MulAut.mul_apply]
      exact (hh _ (hg p hp).2).2
  inv_mem' := fun {g} hg p hp => ⟨(hg p hp).2, by simpa using (hg p hp).1⟩

variable {W : Type*} [AddCommGroup W] (φ : P ≃ W)

@[expose] def resPerm (g : MulAut V) (hg : g ∈ stabP P) : Equiv.Perm W where
  toFun w := φ ⟨g (φ.symm w), (hg _ (φ.symm w).2).1⟩
  invFun w := φ ⟨g⁻¹ (φ.symm w), (hg _ (φ.symm w).2).2⟩
  left_inv w := by
    simp only [Equiv.symm_apply_apply]
    simp
  right_inv w := by
    simp only [Equiv.symm_apply_apply]
    simp

omit [AddCommGroup W] in
theorem resPerm_apply (g : MulAut V) (hg : g ∈ stabP P) (p : P) :
    resPerm P φ g hg (φ p) = φ ⟨g p, (hg _ p.2).1⟩ := by
  simp [resPerm]

omit [AddCommGroup W] in
theorem resPerm_mul (g h : MulAut V) (hg : g ∈ stabP P) (hh : h ∈ stabP P) :
    resPerm P φ (g * h) ((stabP P).mul_mem hg hh) = resPerm P φ g hg * resPerm P φ h hh := by
  ext w : 1
  obtain ⟨p, rfl⟩ := φ.surjective w
  simp only [Equiv.Perm.mul_apply, resPerm_apply]
  rfl

omit [AddCommGroup W] in
theorem resPerm_one : resPerm P φ 1 ((stabP P).one_mem) = 1 := by
  ext w : 1
  obtain ⟨p, rfl⟩ := φ.surjective w
  rw [resPerm_apply]
  rfl

@[expose] def resHom : stabP P →* Equiv.Perm W where
  toFun g := resPerm P φ g g.2
  map_one' := resPerm_one P φ
  map_mul' g h := resPerm_mul P φ g h g.2 h.2

end Res

end CFSG.CGT.PushingUpLit.CGT6.TwoEight
