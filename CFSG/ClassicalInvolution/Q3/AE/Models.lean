module

public import CFSG.ClassicalInvolution.Q3.AE.Group

public section

namespace CFSG.ClassicalInvolution.Q3.AE

open Wr

variable {n : ℕ}

@[expose] def permHom (n : ℕ) : Wr n →* Equiv.Perm (Fin n) where
  toFun a := a.perm
  map_one' := rfl
  map_mul' _ _ := rfl

@[expose] def aeSubOver (A : Subgroup (Equiv.Perm (Fin n))) : Subgroup (Wr n) :=
  aeSub n ⊓ A.comap (permHom n)

@[expose] def aeBarOver (A : Subgroup (Equiv.Perm (Fin n))) : Subgroup (AEQ n) :=
  (aeSubOver A).map (mkQ n)

@[expose] def stabFamily (F : List (Finset (Fin n))) : Subgroup (Equiv.Perm (Fin n)) where
  carrier := {σ | ∀ s ∈ F, s.map σ.toEmbedding ∈ F ∧ s.map σ⁻¹.toEmbedding ∈ F}
  mul_mem' {σ τ} hσ hτ s hs := by
    refine ⟨?_, ?_⟩
    · have h1 := (hτ s hs).1
      have h2 := (hσ _ h1).1
      rwa [Finset.map_map] at h2
    · have h1 := (hσ s hs).2
      have h2 := (hτ _ h1).2
      rw [Finset.map_map] at h2
      rwa [mul_inv_rev]
  one_mem' s hs := by
    have h1 : s.map (1 : Equiv.Perm (Fin n)).toEmbedding = s := by
      ext x
      simp only [Finset.mem_map_equiv]
      rfl
    refine ⟨?_, ?_⟩
    · rw [h1]
      exact hs
    · rw [inv_one, h1]
      exact hs
  inv_mem' {σ} hσ s hs := ⟨(hσ s hs).2, by simpa using (hσ s hs).1⟩

@[expose] def fanoLines : List (Finset (Fin 7)) :=
  [{0, 1, 3}, {1, 2, 4}, {2, 3, 5}, {3, 4, 6}, {4, 5, 0}, {5, 6, 1}, {6, 0, 2}]

@[expose] def l32 : Subgroup (Equiv.Perm (Fin 7)) := stabFamily fanoLines

@[expose] def e64Sub : Subgroup (AEQ 7) := aeBarOver l32

@[expose] def e64Sets : Set (Finset (Fin 7)) := {α | ∃ ℓ ∈ fanoLines, α = ℓᶜ}

@[expose] def affinePlanes : List (Finset (Fin 8)) :=
  [{0, 2, 4, 6}, {1, 3, 5, 7}, {0, 1, 4, 5}, {2, 3, 6, 7}, {0, 3, 4, 7}, {1, 2, 5, 6},
    {0, 1, 2, 3}, {4, 5, 6, 7}, {0, 2, 5, 7}, {1, 3, 4, 6}, {0, 1, 6, 7}, {2, 3, 4, 5},
    {0, 3, 5, 6}, {1, 2, 4, 7}]

@[expose] def agl32 : Subgroup (Equiv.Perm (Fin 8)) := stabFamily affinePlanes

@[expose] def e29Sub : Subgroup (AEQ 8) := aeBarOver agl32

@[expose] def e29Sets : Set (Finset (Fin 8)) := {α | α ∈ affinePlanes}

end CFSG.ClassicalInvolution.Q3.AE
