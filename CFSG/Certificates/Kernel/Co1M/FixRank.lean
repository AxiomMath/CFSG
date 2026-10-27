module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.KC.FixRank

open Matrix in
theorem ncard_fix_le_of_indep {N : Matrix (Fin 24) (Fin 24) (ZMod 2)} {k : ℕ}
    (b : Fin k → (Fin 24 → ZMod 2)) (hind : ∀ c : Fin k → ZMod 2, ∑ i, c i • b i = 0 → c = 0)
    (hbr : ∀ i, ∃ w, N *ᵥ w - w = b i) :
    {v : Fin 24 → ZMod 2 | N *ᵥ v = v}.ncard ≤ 2 ^ (24 - k) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hb : LinearIndependent (ZMod 2) b :=
    Fintype.linearIndependent_iff.2 fun g hg i => congrFun (hind g hg) i
  let f : (Fin 24 → ZMod 2) →ₗ[ZMod 2] (Fin 24 → ZMod 2) := Matrix.mulVecLin N - LinearMap.id
  have hker : {v : Fin 24 → ZMod 2 | N *ᵥ v = v} = (LinearMap.ker f : Set (Fin 24 → ZMod 2)) := by
    ext v
    simp [f, sub_eq_zero]
  have hbr' : ∀ i, b i ∈ LinearMap.range f := fun i => by
    obtain ⟨w, hw⟩ := hbr i
    exact ⟨w, by simpa [f] using hw⟩
  let b' : Fin k → LinearMap.range f := fun i => ⟨b i, hbr' i⟩
  have hb' : LinearIndependent (ZMod 2) b' :=
    LinearIndependent.of_comp (LinearMap.range f).subtype hb
  have h9 := hb'.fintype_card_le_finrank
  rw [Fintype.card_fin] at h9
  have hrn := LinearMap.finrank_range_add_finrank_ker (K := ZMod 2) (V := Fin 24 → ZMod 2) f
  rw [Module.finrank_fin_fun] at hrn
  rw [hker, ← Nat.card_coe_set_eq, SetLike.coe_sort_coe, Nat.card_eq_fintype_card,
    Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

end CFSG.KC.FixRank

end
