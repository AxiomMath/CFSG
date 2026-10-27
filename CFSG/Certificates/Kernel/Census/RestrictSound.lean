module

public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.KC.Census.Restrict

open Subgroup

variable {n m : ℕ} (O : Fin m → Fin n)

@[expose] def stab : Subgroup (Equiv.Perm (Fin n)) where
  carrier := {g | ∀ x, x ∈ Set.range O ↔ g x ∈ Set.range O}
  mul_mem' := by
    intro a b ha hb x
    rw [Equiv.Perm.mul_apply, hb x]
    exact ha (b x)
  one_mem' := fun _ => Iff.rfl
  inv_mem' := by
    intro g hg x
    have := hg (g⁻¹ x)
    simpa using this.symm

variable {O}

theorem mem_stab_of_maps (hO : Function.Injective O) {g : Equiv.Perm (Fin n)}
    (h : ∀ i, ∃ j, g (O i) = O j) : g ∈ stab O := by
  choose f hf using h
  have hinj : Function.Injective f := fun a b hab =>
    hO (g.injective (by rw [hf, hf, hab]))
  have hsurj := Finite.injective_iff_surjective.1 hinj
  intro x
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨f i, (hf i).symm⟩
  · rintro ⟨j, hj⟩
    obtain ⟨i, hi⟩ := hsurj j
    refine ⟨i, g.injective ?_⟩
    rw [hf, hi, hj]

variable (hO : Function.Injective O)

@[expose] noncomputable def resFun (g : stab O) : Equiv.Perm (Fin m) :=
  (Equiv.ofInjective O hO).symm.permCongr
    ((g : Equiv.Perm (Fin n)).subtypePerm fun x => (g.2 x).symm)

theorem O_resFun (g : stab O) (i : Fin m) : O (resFun hO g i) = (g : Equiv.Perm (Fin n)) (O i) := by
  simp [resFun, Equiv.permCongr_apply, Equiv.apply_ofInjective_symm]

@[expose] noncomputable def resHom : stab O →* Equiv.Perm (Fin m) where
  toFun := resFun hO
  map_one' := by
    ext i
    refine congrArg Fin.val (hO ?_)
    rw [O_resFun hO]
    rfl
  map_mul' := by
    intro a b
    ext i
    refine congrArg Fin.val (hO ?_)
    simp only [O_resFun hO, Equiv.Perm.mul_apply, Subgroup.coe_mul]

theorem O_resHom (g : stab O) (i : Fin m) :
    O (resHom hO g i) = (g : Equiv.Perm (Fin n)) (O i) :=
  O_resFun hO g i

theorem resHom_eq {g : stab O} {σ : Equiv.Perm (Fin m)}
    (h : ∀ i, (g : Equiv.Perm (Fin n)) (O i) = O (σ i)) : resHom hO g = σ := by
  ext i
  refine congrArg Fin.val (hO ?_)
  rw [O_resHom hO, h]

end CFSG.KC.Census.Restrict

namespace CFSG.KC.Census

theorem injective_of_card_le_range {G H : Type*} [Group G] [Group H] [Finite G] (f : G →* H)
    (h : Nat.card G ≤ Nat.card f.range) : Function.Injective f := by
  have hs : Function.Surjective f.rangeRestrict := MonoidHom.rangeRestrict_surjective f
  have hb := hs.bijective_of_nat_card_le h
  intro a b hab
  exact hb.1 (Subtype.ext hab)

end CFSG.KC.Census
