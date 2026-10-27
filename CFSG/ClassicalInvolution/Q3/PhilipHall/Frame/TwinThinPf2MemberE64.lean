module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf2DataE64
public import Mathlib.Data.Fin.VecNotation

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

@[expose] def α0 : Finset (Fin 7) := {2, 4, 5, 6}

theorem α0_card : α0.card = 4 := by decide

@[expose] def f0 : Fin 4 → Fin 7 := ![2, 4, 5, 6]

theorem emb_α0 (i : Fin 4) : emb α0 α0_card i = f0 i := by
  have h := Finset.orderEmbOfFin_unique (s := α0) α0_card (f := f0)
    (by intro x; fin_cases x <;> decide) (by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [f0])
  exact (congrFun h i).symm

theorem range_α0 : Set.range (emb α0 α0_card) = (α0 : Set (Fin 7)) := range_emb α0 α0_card

theorem aW_eq : aW = embed (emb α0 α0_card) ⟨vec4 [0, 2], d₁⟩ := by
  have e0 := emb_α0 0
  have e1 := emb_α0 1
  have e2 := emb_α0 2
  have e3 := emb_α0 3
  simp only [f0] at e0 e1 e2 e3
  have hn : ∀ x : Fin 7, x ∉ α0 → x ∉ Set.range (emb α0 α0_card) := by
    intro x hx hr; rw [range_α0] at hr; exact hx hr
  refine Wr.ext (funext fun x => ?_) (Equiv.ext fun x => ?_)
  · rw [embed_vec]
    fin_cases x
    · rw [embedVec_of_not_mem _ _ (hn _ (by decide))]; decide
    · rw [embedVec_of_not_mem _ _ (hn _ (by decide))]; decide
    · have : (2 : Fin 7) = emb α0 α0_card 0 := by simpa using e0.symm
      show _ = embedVec _ _ 2
      rw [this, embedVec_apply]; decide
    · rw [embedVec_of_not_mem _ _ (hn _ (by decide))]; decide
    · have : (4 : Fin 7) = emb α0 α0_card 1 := by simpa using e1.symm
      show _ = embedVec _ _ 4
      rw [this, embedVec_apply]; decide
    · have : (5 : Fin 7) = emb α0 α0_card 2 := by simpa using e2.symm
      show _ = embedVec _ _ 5
      rw [this, embedVec_apply]; decide
    · have : (6 : Fin 7) = emb α0 α0_card 3 := by simpa using e3.symm
      show _ = embedVec _ _ 6
      rw [this, embedVec_apply]; decide
  · rw [embed_perm]
    have p2 : embedPerm (emb α0 α0_card) d₁ 2 = 4 := by
      have := embedPerm_apply (emb α0 α0_card) d₁ 0
      rwa [e0, show d₁ 0 = 1 by decide, e1] at this
    have p4 : embedPerm (emb α0 α0_card) d₁ 4 = 2 := by
      have := embedPerm_apply (emb α0 α0_card) d₁ 1
      rwa [e1, show d₁ 1 = 0 by decide, e0] at this
    have p5 : embedPerm (emb α0 α0_card) d₁ 5 = 6 := by
      have := embedPerm_apply (emb α0 α0_card) d₁ 2
      rwa [e2, show d₁ 2 = 3 by decide, e3] at this
    have p6 : embedPerm (emb α0 α0_card) d₁ 6 = 5 := by
      have := embedPerm_apply (emb α0 α0_card) d₁ 3
      rwa [e3, show d₁ 3 = 2 by decide, e2] at this
    show pc [[2, 4], [5, 6]] x = embedPerm (emb α0 α0_card) d₁ x
    fin_cases x
    · rw [embedPerm_of_not_mem _ _ (hn _ (by decide))]; decide
    · rw [embedPerm_of_not_mem _ _ (hn _ (by decide))]; decide
    · show _ = embedPerm (emb α0 α0_card) d₁ 2
      rw [p2]; decide
    · rw [embedPerm_of_not_mem _ _ (hn _ (by decide))]; decide
    · show _ = embedPerm (emb α0 α0_card) d₁ 4
      rw [p4]; decide
    · show _ = embedPerm (emb α0 α0_card) d₁ 5
      rw [p5]; decide
    · show _ = embedPerm (emb α0 α0_card) d₁ 6
      rw [p6]; decide

theorem bW_eq : bW = embed (emb α0 α0_card) ⟨vec4 [0, 3], d₂⟩ := by
  have e0 := emb_α0 0
  have e1 := emb_α0 1
  have e2 := emb_α0 2
  have e3 := emb_α0 3
  simp only [f0] at e0 e1 e2 e3
  have hn : ∀ x : Fin 7, x ∉ α0 → x ∉ Set.range (emb α0 α0_card) := by
    intro x hx hr; rw [range_α0] at hr; exact hx hr
  refine Wr.ext (funext fun x => ?_) (Equiv.ext fun x => ?_)
  · rw [embed_vec]
    fin_cases x
    · rw [embedVec_of_not_mem _ _ (hn _ (by decide))]; decide
    · rw [embedVec_of_not_mem _ _ (hn _ (by decide))]; decide
    · have : (2 : Fin 7) = emb α0 α0_card 0 := by simpa using e0.symm
      show _ = embedVec _ _ 2
      rw [this, embedVec_apply]; decide
    · rw [embedVec_of_not_mem _ _ (hn _ (by decide))]; decide
    · have : (4 : Fin 7) = emb α0 α0_card 1 := by simpa using e1.symm
      show _ = embedVec _ _ 4
      rw [this, embedVec_apply]; decide
    · have : (5 : Fin 7) = emb α0 α0_card 2 := by simpa using e2.symm
      show _ = embedVec _ _ 5
      rw [this, embedVec_apply]; decide
    · have : (6 : Fin 7) = emb α0 α0_card 3 := by simpa using e3.symm
      show _ = embedVec _ _ 6
      rw [this, embedVec_apply]; decide
  · rw [embed_perm]
    have p2 : embedPerm (emb α0 α0_card) d₂ 2 = 5 := by
      have := embedPerm_apply (emb α0 α0_card) d₂ 0
      rwa [e0, show d₂ 0 = 2 by decide, e2] at this
    have p4 : embedPerm (emb α0 α0_card) d₂ 4 = 6 := by
      have := embedPerm_apply (emb α0 α0_card) d₂ 1
      rwa [e1, show d₂ 1 = 3 by decide, e3] at this
    have p5 : embedPerm (emb α0 α0_card) d₂ 5 = 2 := by
      have := embedPerm_apply (emb α0 α0_card) d₂ 2
      rwa [e2, show d₂ 2 = 0 by decide, e0] at this
    have p6 : embedPerm (emb α0 α0_card) d₂ 6 = 4 := by
      have := embedPerm_apply (emb α0 α0_card) d₂ 3
      rwa [e3, show d₂ 3 = 1 by decide, e1] at this
    show pc [[2, 5], [4, 6]] x = embedPerm (emb α0 α0_card) d₂ x
    fin_cases x
    · rw [embedPerm_of_not_mem _ _ (hn _ (by decide))]; decide
    · rw [embedPerm_of_not_mem _ _ (hn _ (by decide))]; decide
    · show _ = embedPerm (emb α0 α0_card) d₂ 2
      rw [p2]; decide
    · rw [embedPerm_of_not_mem _ _ (hn _ (by decide))]; decide
    · show _ = embedPerm (emb α0 α0_card) d₂ 4
      rw [p4]; decide
    · show _ = embedPerm (emb α0 α0_card) d₂ 5
      rw [p5]; decide
    · show _ = embedPerm (emb α0 α0_card) d₂ 6
      rw [p6]; decide


theorem aW_mem_memAt : aW ∈ memAt α0 α0_card true := by
  rw [aW_eq]
  exact ⟨⟨vec4 [0, 2], d₁⟩, mem_kQ.mpr (by decide +kernel), rfl⟩

theorem bW_mem_memAt : bW ∈ memAt α0 α0_card true := by
  rw [bW_eq]
  exact ⟨⟨vec4 [0, 3], d₂⟩, mem_kQ.mpr (by decide +kernel), rfl⟩

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf
