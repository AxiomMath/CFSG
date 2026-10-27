module

public import Certificates.Data.Holder272.E29Model

public section

namespace CFSG.ClassicalInvolution.Q3.E29Ker

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr
open CFSG.ClassicalInvolution.Q3.E29Data

@[expose] def α0 : Finset (Fin 8) := {0, 2, 4, 6}

theorem α0_card : α0.card = 4 := by decide

private theorem a0_emb (i : Fin 4) : emb α0 α0_card i = ![0, 2, 4, 6] i := by
  have h := Finset.orderEmbOfFin_unique (s := α0) α0_card (f := ![0, 2, 4, 6])
    (by intro x; fin_cases x <;> decide) (by
      intro i j hij
      fin_cases i <;> fin_cases j <;> first | exact absurd hij (by decide) | decide)
  exact (congrFun h i).symm

theorem α0_mem_e29Sets : α0 ∈ e29Sets := by
  show α0 ∈ affinePlanes
  decide

private theorem a0_not_mem {x : Fin 8} (hx : x ∉ Set.range (emb α0 α0_card)) : x ∉ α0 := by
  rw [range_emb] at hx
  exact fun h => hx (Finset.mem_coe.mpr h)

private theorem a0_vec_nA : ∀ x : Fin 8, x ∉ α0 → nA.vec x = 0 := by
  decide +kernel

private theorem a0_perm_nA : ∀ x : Fin 8, x ∉ α0 → cycPerm8 [[0, 2], [4, 6]] x = x := by
  decide +kernel

private theorem a0_vec_nB : ∀ x : Fin 8, x ∉ α0 → nB.vec x = 0 := by
  decide +kernel

private theorem a0_perm_nB : ∀ x : Fin 8, x ∉ α0 → cycPerm8 [[0, 4], [2, 6]] x = x := by
  decide +kernel

private theorem a0_nA : nA = embed (emb α0 α0_card) ⟨vec4 [0, 2], d₁⟩ := by
  refine Wr.ext (funext fun x => ?_) (Equiv.ext fun x => ?_)
  · rw [embed_vec]
    by_cases hx : x ∈ Set.range (emb α0 α0_card)
    · obtain ⟨i, rfl⟩ := hx
      rw [embedVec_apply, a0_emb]
      fin_cases i <;> decide
    · rw [embedVec_of_not_mem _ _ hx]
      exact a0_vec_nA x (a0_not_mem hx)
  · rw [embed_perm]
    show cycPerm8 [[0, 2], [4, 6]] x = embedPerm (emb α0 α0_card) d₁ x
    by_cases hx : x ∈ Set.range (emb α0 α0_card)
    · obtain ⟨i, rfl⟩ := hx
      rw [embedPerm_apply, a0_emb, a0_emb]
      fin_cases i <;> decide
    · rw [embedPerm_of_not_mem _ _ hx]
      exact a0_perm_nA x (a0_not_mem hx)

private theorem a0_nB : nB = embed (emb α0 α0_card) ⟨vec4 [0, 3], d₂⟩ := by
  refine Wr.ext (funext fun x => ?_) (Equiv.ext fun x => ?_)
  · rw [embed_vec]
    by_cases hx : x ∈ Set.range (emb α0 α0_card)
    · obtain ⟨i, rfl⟩ := hx
      rw [embedVec_apply, a0_emb]
      fin_cases i <;> decide
    · rw [embedVec_of_not_mem _ _ hx]
      exact a0_vec_nB x (a0_not_mem hx)
  · rw [embed_perm]
    show cycPerm8 [[0, 4], [2, 6]] x = embedPerm (emb α0 α0_card) d₂ x
    by_cases hx : x ∈ Set.range (emb α0 α0_card)
    · obtain ⟨i, rfl⟩ := hx
      rw [embedPerm_apply, a0_emb, a0_emb]
      fin_cases i <;> decide
    · rw [embedPerm_of_not_mem _ _ hx]
      exact a0_perm_nB x (a0_not_mem hx)

theorem nA_mem_memAt : nA ∈ memAt α0 α0_card true := by
  rw [a0_nA]
  exact ⟨⟨vec4 [0, 2], d₁⟩, mem_kQ.mpr (by decide +kernel), rfl⟩

theorem nB_mem_memAt : nB ∈ memAt α0 α0_card true := by
  rw [a0_nB]
  exact ⟨⟨vec4 [0, 3], d₂⟩, mem_kQ.mpr (by decide +kernel), rfl⟩

end CFSG.ClassicalInvolution.Q3.E29Ker
