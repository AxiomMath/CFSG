module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5VLike

public section

namespace CFSG.ComponentClassification.GMS78.VLike

variable {K : Type*} [Field K] [Fintype K] [CharP K 2]

@[expose] def perp (a : ℕ) (c : K) (Λ : AddSubgroup K) (x : K × K × K) : Set (K × K × K) :=
  {z | z.2.2 ∈ Λ ∧ commMap a c x z = 0}

variable {a : ℕ} {c e : K}

omit [Fintype K] in
theorem sqMap_add (x y : K × K × K) :
    sqMap a c e (x + y) = sqMap a c e x + sqMap a c e y + commMap a c x y := by
  have h1 : (x.1 + y.1) ^ (2 ^ (a + 1) + 1) =
      (x.1 ^ 2 ^ (a + 1) + y.1 ^ 2 ^ (a + 1)) * (x.1 + y.1) := by
    rw [pow_succ, add_pow_two_pow]
  have h2 : ((x.1 + y.1) * (x.2.1 + y.2.1)) ^ 2 ^ a = (x.1 * x.2.1) ^ 2 ^ a +
      (x.1 * y.2.1) ^ 2 ^ a + (y.1 * x.2.1) ^ 2 ^ a + (y.1 * y.2.1) ^ 2 ^ a := by
    rw [show (x.1 + y.1) * (x.2.1 + y.2.1) =
        x.1 * x.2.1 + x.1 * y.2.1 + y.1 * x.2.1 + y.1 * y.2.1 by ring,
      add_pow_two_pow, add_pow_two_pow, add_pow_two_pow]
  simp only [sqMap, commMap, Prod.fst_add, Prod.snd_add, h1, h2]
  ring

omit [Fintype K] in
theorem commMap_add_right (x z z' : K × K × K) :
    commMap a c x (z + z') = commMap a c x z + commMap a c x z' := by
  have h := commMap_sub (a := a) (c := c) x (z + z') z'
  rw [add_sub_cancel_right] at h
  rw [h, sub_add_cancel]

omit [Fintype K] in
theorem add_mem_perp {Λ : AddSubgroup K} {x z z' : K × K × K} (hz : z ∈ perp a c Λ x)
    (hz' : z' ∈ perp a c Λ x) : z + z' ∈ perp a c Λ x :=
  ⟨by simpa using Λ.add_mem hz.1 hz'.1, by rw [commMap_add_right, hz.2, hz'.2, add_zero]⟩

omit [Fintype K] [CharP K 2] in
theorem sqMap_mem_closure {Λ : AddSubgroup K} {x z : K × K × K} (hz : z ∈ perp a c Λ x) :
    sqMap a c e z ∈ AddSubgroup.closure (sqMap a c e '' perp a c Λ x) :=
  AddSubgroup.subset_closure ⟨z, hz, rfl⟩

omit [Fintype K] in
theorem commMap_mem_closure {Λ : AddSubgroup K} {x z z' : K × K × K} (hz : z ∈ perp a c Λ x)
    (hz' : z' ∈ perp a c Λ x) :
    commMap a c z z' ∈ AddSubgroup.closure (sqMap a c e '' perp a c Λ x) := by
  have h := sqMap_add (a := a) (c := c) (e := e) z z'
  have hmem : sqMap a c e (z + z') - sqMap a c e z - sqMap a c e z' ∈
      AddSubgroup.closure (sqMap a c e '' perp a c Λ x) :=
    AddSubgroup.sub_mem _ (AddSubgroup.sub_mem _ (sqMap_mem_closure (add_mem_perp hz hz'))
      (sqMap_mem_closure hz)) (sqMap_mem_closure hz')
  rwa [h, show sqMap a c e z + sqMap a c e z' + commMap a c z z' - sqMap a c e z -
      sqMap a c e z' = commMap a c z z' by ring] at hmem

end CFSG.ComponentClassification.GMS78.VLike
