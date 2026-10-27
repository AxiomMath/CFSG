module

import all CFSG.Fischer.F4
public import CFSG.Fischer.TransvectionPointsBase

public section

namespace CFSG.Fischer

@[expose] def perp (p q : Fin 693) : Prop := hermStd (uVec p) (uVec q) = 0

instance : DecidableRel perp := fun _ _ => inferInstanceAs (Decidable (hermStd _ _ = 0))

theorem perp_iff {p q : Fin 693} : perp p q ↔ hermStd (uVec p) (uVec q) = 0 := Iff.rfl

@[expose] def lineThru (x y : Fin 693) : Set (Fin 693) :=
  {z | ∃ a b : F4, uVec z = a • uVec x + b • uVec y}

@[expose] def IsLine (L : Set (Fin 693)) : Prop := ∃ x y, x ≠ y ∧ perp x y ∧ L = lineThru x y

structure IsClosedHyperoval (O : Set (Fin 693)) : Prop where
  inter : ∀ L, IsLine L → (L ∩ O).ncard = 0 ∨ (L ∩ O).ncard = 2
  closed : ∀ x ∈ O, tvP x '' O = O

@[expose] def weight (v : Fin 6 → F4) : ℕ := (Finset.univ.filter fun k => v k ≠ 0).card

@[expose] def hypRoot (i : Fin 3) : Set (Fin 693) :=
  {p | weight (uVec p) = 2 ∨ (weight (uVec p) = 6 ∧ ∏ k, uVec p k = F4.ω ^ (i : ℕ))}

@[expose] def hypOrbit (i : Fin 3) : Set (Set (Fin 693)) :=
  {O | ∃ g ∈ T46, O = ⇑g '' hypRoot i}

theorem hypRoot_mem_hypOrbit (i : Fin 3) : hypRoot i ∈ hypOrbit i :=
  ⟨1, T46.one_mem, by simp⟩

theorem F4.ω_ne_zero : F4.ω ≠ 0 := by decide

@[expose] noncomputable def delta : Equiv.Perm (Fin 693) :=
  piGU ⟨diagGL (unitOf F4.ω F4.ω_ne_zero), diagGL_isom _⟩

@[expose] def xiRoot : hypOrbit 0 := ⟨hypRoot 0, hypRoot_mem_hypOrbit 0⟩

end CFSG.Fischer
