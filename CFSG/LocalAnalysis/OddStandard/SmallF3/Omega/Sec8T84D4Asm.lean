module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84EDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84D3Quot

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {E X1 X2 E1 E2 : Subgroup G}

theorem sec8t84d4_E_inf_Y (h : Sec8T84DCtx G t E X1 X2) (hd : Sec8T84DDec G t E X1 X2 E1 E2) :
    E ⊓ Sec8T84Y X1 = E1 := by
  apply le_antisymm
  · intro x hx
    exact sec8t84d3_Y_inf_E h hd (by simpa [inf_comm] using hx)
  · exact le_inf hd.le1 (sec8t84d3_E1_le_Y h hd)

theorem sec8t84d4_C_le (h : Sec8T84DCtx G t E X1 X2) (hd : Sec8T84DDec G t E X1 X2 E1 E2) :
    centralizer (E : Set G) ≤ Sec8T84Y X1 ⊔ Sec8T84Y X2 := by
  intro c hc
  obtain ⟨e, he, o, ho, rfl⟩ := sec8t84d3_C_decomp h hc
  obtain ⟨e1, he1, e2, he2, rfl⟩ := sec8t84d3_E_decomp h hd he
  exact Subgroup.mul_mem _
    (Subgroup.mul_mem _
      (Subgroup.mem_sup_left (sec8t84d3_E1_le_Y h hd he1))
      (Subgroup.mem_sup_right (sec8t84d3_E1_le_Y h.symm hd.symm he2)))
    (Subgroup.mem_sup_left (sec8t84d3_O_le_Y h ho))

theorem sec8t84d4_core (h : Sec8T84DCtx G t E X1 X2) (hd : Sec8T84DDec G t E X1 X2 E1 E2) :
    Sec8T84XCore G t E (Sec8T84Y X1) (Sec8T84Y X2) := by
  have hEY1 : E ⊓ Sec8T84Y X1 = E1 := sec8t84d4_E_inf_Y h hd
  have hEY2 : E ⊓ Sec8T84Y X2 = E2 := sec8t84d4_E_inf_Y h.symm hd.symm
  exact
    { o_le1 := sec8t84d3_O_le_Y h
      o_le2 := sec8t84d3_O_le_Y h.symm
      le1 := (sec8t84y_le X1).trans h.hX.le1
      le2 := (sec8t84y_le X2).trans h.hX.le2
      comm := fun a ha b hb => sec8t84d3_comm_Y h hd ha hb
      inf := by
        intro y hy
        have hy1 : y ∈ Sec8T84Y X1 := hy.1
        have hy2 : y ∈ Sec8T84Y X2 := hy.2
        have hyC : y ∈ centralizer (E : Set G) :=
          h.hX.inf ⟨sec8t84y_le X1 hy1, sec8t84y_le X2 hy2⟩
        obtain ⟨e, he, o, ho, hyeo⟩ := sec8t84d3_C_decomp h hyC
        have heo : e = y * o⁻¹ := by rw [hyeo]; group
        have heY1 : e ∈ Sec8T84Y X1 := by
          rw [heo]
          exact Subgroup.mul_mem _ hy1 (Subgroup.inv_mem _ (sec8t84d3_O_le_Y h ho))
        have heY2 : e ∈ Sec8T84Y X2 := by
          rw [heo]
          exact Subgroup.mul_mem _ hy2 (Subgroup.inv_mem _ (sec8t84d3_O_le_Y h.symm ho))
        have heE1 : e ∈ E1 := sec8t84d3_Y_inf_E h hd ⟨heY1, he⟩
        have heE2 : e ∈ E2 := sec8t84d3_Y_inf_E h.symm hd.symm ⟨heY2, he⟩
        have he_one : e = 1 := by
          have : e ∈ E1 ⊓ E2 := ⟨heE1, heE2⟩
          simpa [hd.inf] using this
        simpa [hyeo, he_one] using ho
      sup := by
        apply le_antisymm
        · refine sup_le (sup_le ?_ ?_) ?_
          · intro x hx
            exact h.hX.le1 (sec8t84y_le X1 hx)
          · intro x hx
            exact h.hX.le2 (sec8t84y_le X2 hx)
          · intro x hx
            rw [← h.hX.sup]
            exact Subgroup.mem_sup_right hx
        · rw [← h.hX.sup]
          refine sup_le (sup_le ?_ ?_) ?_
          · intro x hx
            obtain ⟨k, hk, y, hy, rfl⟩ := sec8t84y_exists_mul h.hX.quot1 hx
            exact Subgroup.mul_mem _
              (Subgroup.mem_sup_left (sec8t84d4_C_le h hd hk))
              (Subgroup.mem_sup_left (Subgroup.mem_sup_left hy))
          · intro x hx
            obtain ⟨k, hk, y, hy, rfl⟩ := sec8t84y_exists_mul h.hX.quot2 hx
            exact Subgroup.mul_mem _
              (Subgroup.mem_sup_left (sec8t84d4_C_le h hd hk))
              (Subgroup.mem_sup_left (Subgroup.mem_sup_right hy))
          · intro x hx
            exact Subgroup.mem_sup_right hx
      t_not := by
        intro ht
        exact h.hX.t_not (sup_le_sup (sec8t84y_le X1) (sec8t84y_le X2) ht)
      swap1 := fun a ha => sec8t84y_conj (H := X1) (H' := X2) (g := t) h.hX.swap1 ha
      swap2 := fun a ha => sec8t84y_conj (H := X2) (H' := X1) (g := t) h.hX.swap2 ha
      E_sup := by rw [hEY1, hEY2]; exact hd.sup.symm
      e16_1 := by rw [hEY1]; exact hd.e16_1
      e16_2 := by rw [hEY2]; exact hd.e16_2
      quot1 := by rw [hEY1]; exact sec8t84d3_quot h hd
      quot2 := by rw [hEY2]; exact sec8t84d3_quot h.symm hd.symm
      cent1 := by rw [hEY1]; exact sec8t84d3_cent h hd
      cent2 := by rw [hEY2]; exact sec8t84d3_cent h.symm hd.symm
      trans1 := by rw [hEY1]; exact sec8t84d3_trans h hd
      trans2 := by rw [hEY2]; exact sec8t84d3_trans h.symm hd.symm }

end CFSG.OddStandard.SmallF3.Omega
