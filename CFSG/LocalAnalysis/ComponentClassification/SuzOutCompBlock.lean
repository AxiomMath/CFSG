module

public import Certificates.Data.SuzOutComp

public section

namespace CFSG.ComponentClassification.SuzOutComp

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native Native

variable {n m : ℕ}

@[expose] def blockStab (n m : ℕ) (lab : Fin n → ℕ) : Subgroup (Equiv.Perm (Fin n)) where
  carrier := {g | (∀ x, lab x < m ↔ lab (g x) < m) ∧
    ∀ x y, lab x < m → lab y < m → (lab x = lab y ↔ lab (g x) = lab (g y))}
  one_mem' := ⟨fun _ => Iff.rfl, fun _ _ _ _ => Iff.rfl⟩
  mul_mem' := fun {a b} ha hb =>
    ⟨fun x => (hb.1 x).trans (ha.1 (b x)), fun x y hx hy =>
      (hb.2 x y hx hy).trans (ha.2 (b x) (b y) ((hb.1 x).1 hx) ((hb.1 y).1 hy))⟩
  inv_mem' := fun {a} ha => by
    have h1 : ∀ x, lab x < m ↔ lab (a⁻¹ x) < m := fun x => by
      simpa using (ha.1 (a⁻¹ x)).symm
    refine ⟨h1, fun x y hx hy => ?_⟩
    have := ha.2 (a⁻¹ x) (a⁻¹ y) ((h1 x).1 hx) ((h1 y).1 hy)
    simpa using this.symm

theorem lab_eq_of_lab_eq {lab : Fin n → ℕ} {g : Equiv.Perm (Fin n)} (hg : g ∈ blockStab n m lab)
    {x y : Fin n} (hx : lab x < m) (hxy : lab x = lab y) : lab (g x) = lab (g y) :=
  (hg.2 x y hx (hxy ▸ hx)).1 hxy

section Hom

variable {lab : Fin n → ℕ} {rep : Fin m → Fin n} (hrep : ∀ j, lab (rep j) = j)
include hrep

theorem lab_lt_of_mem {g : Equiv.Perm (Fin n)} (hg : g ∈ blockStab n m lab) (j : Fin m) :
    lab (g (rep j)) < m :=
  (hg.1 (rep j)).1 (by rw [hrep]; exact j.2)

@[expose] def blockFun (g : blockStab n m lab) (j : Fin m) : Fin m :=
  ⟨lab (g.1 (rep j)), lab_lt_of_mem hrep g.2 j⟩

theorem lab_rep_lab {x : Fin n} (hx : lab x < m) : lab (rep ⟨lab x, hx⟩) = lab x := hrep _

theorem lab_apply (g : blockStab n m lab) {x : Fin n} (hx : lab x < m) :
    lab (g.1 x) = blockFun hrep g ⟨lab x, hx⟩ :=
  lab_eq_of_lab_eq g.2 hx (lab_rep_lab hrep hx).symm

theorem blockFun_mul (g h : blockStab n m lab) (j : Fin m) :
    blockFun hrep (g * h) j = blockFun hrep g (blockFun hrep h j) := by
  apply Fin.ext
  show lab ((g.1 * h.1) (rep j)) = lab (g.1 (rep ⟨lab (h.1 (rep j)), _⟩))
  rw [Equiv.Perm.mul_apply]
  exact lab_eq_of_lab_eq g.2 (lab_lt_of_mem hrep h.2 j)
    (hrep ⟨lab (h.1 (rep j)), lab_lt_of_mem hrep h.2 j⟩).symm

theorem blockFun_one (j : Fin m) : blockFun hrep (1 : blockStab n m lab) j = j :=
  Fin.ext (hrep j)

@[expose] def blockHom : blockStab n m lab →* Equiv.Perm (Fin m) where
  toFun g :=
    { toFun := blockFun hrep g
      invFun := blockFun hrep g⁻¹
      left_inv := fun j => by
        rw [← blockFun_mul, inv_mul_cancel, blockFun_one]
      right_inv := fun j => by
        rw [← blockFun_mul, mul_inv_cancel, blockFun_one] }
  map_one' := Equiv.ext fun j => blockFun_one hrep j
  map_mul' g h := Equiv.ext fun j => blockFun_mul hrep g h j

theorem blockHom_apply (g : blockStab n m lab) (j : Fin m) :
    (blockHom hrep g j : ℕ) = lab (g.1 (rep j)) := rfl

end Hom

theorem rep_blockArr {labA repA : Array ℕ} {lab : Fin n → ℕ} {rep : Fin m → Fin n}
    (hrep : ∀ j, lab (rep j) = j) (hlab : ∀ x : Fin n, lab x = labA[(x : ℕ)]!)
    (hrepA : ∀ j : Fin m, (rep j : ℕ) = repA[(j : ℕ)]!) {t : Array ℕ}
    (g : blockStab n m lab) (ht : Rep n t g.1) :
    Rep m (blockArr labA repA m t) (blockHom hrep g) := fun j => by
  rw [blockArr, getElem!_ofFn_nat _ j.2, blockHom_apply, hlab, ← ht, hrepA]

theorem mem_blockStab_of_blockOK {labA repA t : Array ℕ} {g : Equiv.Perm (Fin n)}
    (ht : Rep n t g) (h : blockOK n m labA repA t = true) :
    g ∈ blockStab n m (fun x => labA[(x : ℕ)]!) := by
  simp only [blockOK, Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have hdom : ∀ x : Fin n, labA[(x : ℕ)]! < m ↔ labA[(g x : ℕ)]! < m := fun x => by
    have := allLt_spec h1 x.2
    rw [ht x] at this
    simpa using this
  have himg : ∀ x : Fin n, labA[(x : ℕ)]! < m →
      labA[(g x : ℕ)]! = (blockArr labA repA m t)[labA[(x : ℕ)]!]! := fun x hx => by
    have := allLt_spec h2 x.2
    rw [ht x] at this
    simpa [hx] using this
  refine ⟨hdom, fun x y hx hy => ?_⟩
  have hx : labA[(x : ℕ)]! < m := hx
  have hy : labA[(y : ℕ)]! < m := hy
  show labA[(x : ℕ)]! = labA[(y : ℕ)]! ↔ labA[(g x : ℕ)]! = labA[(g y : ℕ)]!
  rw [himg x hx, himg y hy]
  constructor
  · intro hxy
    rw [hxy]
  · intro hxy
    have hx' := (isInvA_spec h3 hx).2
    have hy' := (isInvA_spec h3 hy).2
    rw [hxy] at hx'
    exact hx'.symm.trans hy'

end CFSG.ComponentClassification.SuzOutComp
