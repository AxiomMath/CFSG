module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3Fields

public noncomputable section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaSec3

open CFSG.Fischer Subgroup

theorem wP_mem_zpowers (w : List ℕ) : wP w ∈ zpowers (wP w) := mem_zpowers _

theorem chK2_eq_gen :
    chK2.grp = chX1.grp ⊔ chX2.grp ⊔ zpowers (wP [15]) ⊔ zpowers (wP [16]) := by
  apply le_antisymm
  · refine grp_le fun w hw => ?_
    simp only [chK2, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
    · exact mem_sup_left (mem_sup_left (mem_sup_left (wP_mem_grp (by simp [chX1]))))
    · exact mem_sup_left (mem_sup_left (mem_sup_left (wP_mem_grp (by simp [chX1]))))
    · exact mem_sup_left (mem_sup_left (mem_sup_right (wP_mem_grp (by simp [chX2]))))
    · exact mem_sup_left (mem_sup_left (mem_sup_right (wP_mem_grp (by simp [chX2]))))
    · exact mem_sup_left (mem_sup_right (wP_mem_zpowers _))
    · exact mem_sup_right (wP_mem_zpowers _)
  · refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_
    · refine grp_le fun w hw => wP_mem_grp ?_
      simp only [chX1, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl <;> simp [chK2]
    · refine grp_le fun w hw => wP_mem_grp ?_
      simp only [chX2, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl <;> simp [chK2]
    · exact zpowers_le.2 (wP_mem_grp (by simp [chK2]))
    · exact zpowers_le.2 (wP_mem_grp (by simp [chK2]))

theorem chK1_eq_gen :
    chK1.grp = chX2.grp ⊔ chX3.grp ⊔ zpowers (wP [16]) ⊔ zpowers (wP [17]) := by
  apply le_antisymm
  · refine grp_le fun w hw => ?_
    simp only [chK1, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl
    · exact mem_sup_left (mem_sup_left (mem_sup_left (wP_mem_grp (by simp [chX2]))))
    · exact mem_sup_left (mem_sup_left (mem_sup_left (wP_mem_grp (by simp [chX2]))))
    · exact mem_sup_left (mem_sup_left (mem_sup_right (wP_mem_grp (by simp [chX3]))))
    · exact mem_sup_left (mem_sup_right (wP_mem_zpowers _))
    · exact mem_sup_right (wP_mem_zpowers _)
  · refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_
    · refine grp_le fun w hw => wP_mem_grp ?_
      simp only [chX2, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl <;> simp [chK1]
    · refine grp_le fun w hw => wP_mem_grp ?_
      simp only [chX3, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl
      simp [chK1]
    · exact zpowers_le.2 (wP_mem_grp (by simp [chK1]))
    · exact zpowers_le.2 (wP_mem_grp (by simp [chK1]))

theorem chL_le_gen : chL.grp ≤ chX1.grp ⊔ chX2.grp ⊔ chX3.grp ⊔ zpowers (wP [15]) ⊔
    zpowers (wP [16]) ⊔ zpowers (wP [17]) := by
  refine grp_le fun w hw => ?_
  simp only [chL, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact mem_sup_left (mem_sup_left (mem_sup_left (mem_sup_left (mem_sup_left
      (wP_mem_grp (by simp [chX1]))))))
  · exact mem_sup_left (mem_sup_left (mem_sup_left (mem_sup_left (mem_sup_left
      (wP_mem_grp (by simp [chX1]))))))
  · exact mem_sup_left (mem_sup_left (mem_sup_left (mem_sup_left (mem_sup_right
      (wP_mem_grp (by simp [chX2]))))))
  · exact mem_sup_left (mem_sup_left (mem_sup_left (mem_sup_left (mem_sup_right
      (wP_mem_grp (by simp [chX2]))))))
  · exact mem_sup_left (mem_sup_left (mem_sup_left (mem_sup_right
      (wP_mem_grp (by simp [chX3])))))
  · exact mem_sup_left (mem_sup_left (mem_sup_right (wP_mem_zpowers _)))
  · exact mem_sup_left (mem_sup_right (wP_mem_zpowers _))
  · exact mem_sup_right (wP_mem_zpowers _)

variable {G : Type} [Group G] {L : Subgroup G}
  {e : L ≃* T46}

theorem zpowers_wP_le_T46 {w : List ℕ} (hw : ∀ k ∈ w, k < 18) : zpowers (wP w) ≤ T46 :=
  zpowers_le.2 (wP_mem_T46 w hw)

theorem zpowers_sw0 : zpowers (sw e 0) = toG e (zpowers (wP [15])) := by
  rw [sw0, ← toG_zpowers]
  rfl

theorem zpowers_sw1 : zpowers (sw e 1) = toG e (zpowers (wP [16])) := by
  rw [sw1, ← toG_zpowers]
  rfl

theorem zpowers_sw2 : zpowers (sw e 2) = toG e (zpowers (wP [17])) := by
  rw [sw2, ← toG_zpowers]
  rfl

theorem L_le_gen : L ≤ sX₁ e ⊔ sX₂ e ⊔ sX₃ e ⊔ zpowers (sw e 0) ⊔ zpowers (sw e 1) ⊔
    zpowers (sw e 2) := by
  have h1 := grp_le_T46 gensOK_chX1
  have h2 := grp_le_T46 gensOK_chX2
  have h3 := grp_le_T46 gensOK_chX3
  have h4 := zpowers_wP_le_T46 (w := [15]) (by decide)
  have h5 := zpowers_wP_le_T46 (w := [16]) (by decide)
  have h6 := zpowers_wP_le_T46 (w := [17]) (by decide)
  calc L = toG e chL.grp := by rw [chL_eq_T46, toG_T46]
    _ ≤ toG e (chX1.grp ⊔ chX2.grp ⊔ chX3.grp ⊔ zpowers (wP [15]) ⊔ zpowers (wP [16]) ⊔
        zpowers (wP [17])) := toG_mono chL_le_gen
    _ = _ := by
      rw [toG_sup (sup_le (sup_le (sup_le (sup_le h1 h2) h3) h4) h5) h6,
        toG_sup (sup_le (sup_le (sup_le h1 h2) h3) h4) h5, toG_sup (sup_le (sup_le h1 h2) h3) h4,
        toG_sup (sup_le h1 h2) h3, toG_sup h1 h2, zpowers_sw0, zpowers_sw1, zpowers_sw2]
      rfl

theorem sK₂_eq_gen : sK₂ e = sX₁ e ⊔ sX₂ e ⊔ zpowers (sw e 0) ⊔ zpowers (sw e 1) := by
  have h1 := grp_le_T46 gensOK_chX1
  have h2 := grp_le_T46 gensOK_chX2
  have h4 := zpowers_wP_le_T46 (w := [15]) (by decide)
  have h5 := zpowers_wP_le_T46 (w := [16]) (by decide)
  rw [sK₂, chK2_eq_gen, toG_sup (sup_le (sup_le h1 h2) h4) h5, toG_sup (sup_le h1 h2) h4,
    toG_sup h1 h2, zpowers_sw0, zpowers_sw1]
  rfl

theorem sK₁_eq_gen : sK₁ e = sX₂ e ⊔ sX₃ e ⊔ zpowers (sw e 1) ⊔ zpowers (sw e 2) := by
  have h2 := grp_le_T46 gensOK_chX2
  have h3 := grp_le_T46 gensOK_chX3
  have h5 := zpowers_wP_le_T46 (w := [16]) (by decide)
  have h6 := zpowers_wP_le_T46 (w := [17]) (by decide)
  rw [sK₁, chK1_eq_gen, toG_sup (sup_le (sup_le h2 h3) h5) h6, toG_sup (sup_le h2 h3) h5,
    toG_sup h2 h3, zpowers_sw1, zpowers_sw2]
  rfl

end CFSG.EvenSmallLie.UnitarySix.YamadaSec3
