module

public import CFSG.ClassicalGroups.Orthogonal.Restrict
public import Mathlib.FieldTheory.Finiteness

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open CFSG.ClassicalGroups.Orthogonal QuadraticMap

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

@[expose] def cl24_perpIn (P : HypPair Q) (D : Submodule K P.perp) : Set P.perp :=
  {v | ∀ d ∈ D, polar Q (v : V) (d : V) = 0}

theorem cl24_mem_perpIn (P : HypPair Q) (D : Submodule K P.perp) (v : P.perp) :
    v ∈ cl24_perpIn P D ↔ ∀ d ∈ D, polar Q (v : V) (d : V) = 0 :=
  Iff.rfl

theorem cl24_zero_mem_perpIn (P : HypPair Q) (D : Submodule K P.perp) :
    (0 : P.perp) ∈ cl24_perpIn P D := by
  intro d _
  exact polar_zero_left Q _

private theorem cl24_perpIn_eq (P : HypPair Q) (D : Submodule K P.perp) :
    cl24_perpIn P D =
      ((LinearMap.BilinForm.orthogonal (polarBilin (Q.restrict P.perp)) D :
        Submodule K P.perp) : Set P.perp) := by
  ext v
  rw [cl24_mem_perpIn]
  simp only [LinearMap.BilinForm.mem_orthogonal_iff, SetLike.mem_coe]
  constructor
  · intro h d hd
    simpa [polarBilin_apply_apply, polar_restrict, polar_comm] using h d hd
  · intro h d hd
    simpa [polarBilin_apply_apply, polar_restrict, polar_comm] using h d hd

theorem cl24_card_mul_card_perpIn [Finite K] [FiniteDimensional K V]
    (hQ : (polarBilin Q).Nondegenerate) (P : HypPair Q) (D : Submodule K P.perp) :
    Nat.card D * Nat.card (cl24_perpIn P D) = Nat.card P.perp := by
  have hB : (polarBilin (Q.restrict P.perp)).Nondegenerate :=
    nondegenerate_polarBilin_restrict (HypPair.polarNondegOn_perp hQ P)
  rw [cl24_perpIn_eq]
  change Nat.card D *
      Nat.card (LinearMap.BilinForm.orthogonal (polarBilin (Q.restrict P.perp)) D) =
    Nat.card P.perp
  rw [Module.natCard_eq_pow_finrank (K := K) (V := D),
    Module.natCard_eq_pow_finrank (K := K)
      (V := LinearMap.BilinForm.orthogonal (polarBilin (Q.restrict P.perp)) D),
    Module.natCard_eq_pow_finrank (K := K) (V := P.perp),
    LinearMap.BilinForm.finrank_orthogonal hB D,
    ← pow_add,
    Nat.add_sub_cancel' (Submodule.finrank_le D)]

theorem cl24_exists_ne_zero_mem_perpIn [Finite K] [FiniteDimensional K V]
    (hQ : (polarBilin Q).Nondegenerate) (P : HypPair Q) (D : Submodule K P.perp) (hD : D ≠ ⊤) :
    ∃ v : P.perp, v ≠ 0 ∧ v ∈ cl24_perpIn P D := by
  have hB : (polarBilin (Q.restrict P.perp)).Nondegenerate :=
    nondegenerate_polarBilin_restrict (HypPair.polarNondegOn_perp hQ P)
  have hlt : Module.finrank K D < Module.finrank K P.perp := Submodule.finrank_lt hD
  have hpos : 0 < Module.finrank K
      (LinearMap.BilinForm.orthogonal (polarBilin (Q.restrict P.perp)) D) := by
    rw [LinearMap.BilinForm.finrank_orthogonal hB D]
    exact Nat.sub_pos_of_lt hlt
  have hbot : LinearMap.BilinForm.orthogonal (polarBilin (Q.restrict P.perp)) D ≠ ⊥ :=
    Submodule.one_le_finrank_iff.mp hpos
  obtain ⟨x, hxmem, hxne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  exact ⟨x, hxne, by rw [cl24_perpIn_eq]; exact hxmem⟩

end CFSG.OddStandard.SmallF3.HypA2Leaves
