module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage2BridgeCheck
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage2Plus
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage2Minus

public section

namespace CFSG.EvenSmallLie.OmegaEight.Stage2

open CFSG.EvenSmallLie.OmegaEight.Stage1 Subgroup

theorem bridgeCheck_parts {ε : Eps} {cGens tGens : Array (ℕ × ℕ)} {cE tcE sE : Enum}
    (h : bridgeCheck ε cGens tGens cE tcE sE = true) :
    (∀ i < 6, memK cE.keys (kronK (genRows ε i)) = true) ∧
    enumOK (stage1Gens ε) sE = true ∧ gensIn cGens sE = true ∧
    tGens.size = 7 ∧ (tGens.getD 0 (0, 0)).1 = phiK ∧
    ∀ k < 6, (tGens.getD (k + 1) (0, 0)).1 = kronK (urRows ε k) ∧
      memK tcE.keys (kronK (urRows ε k)) = true := by
  simp only [bridgeCheck, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  exact ⟨h.1.1.1.1.1, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem stage1Gens_size (ε : Eps) : (stage1Gens ε).size = 7 := by
  simp [stage1Gens]

theorem genK_stage1Gens_zero (ε : Eps) : genK (stage1Gens ε) 0 = (phiK, phiK) := by
  simp [genK, stage1Gens, Array.getD_eq_getD_getElem?]

theorem genK_stage1Gens_succ (ε : Eps) {i : ℕ} (hi : i < 6) :
    genK (stage1Gens ε) (i + 1) = (kronK (genRows ε i), kronK (genInvRows ε i)) := by
  simp [genK, stage1Gens, Array.getD_eq_getD_getElem?, hi]

theorem stage1_le_closure (ε : Eps) (hg : gensOK (stage1Gens ε) = true) :
    grpOf (stage1Gens ε) ≤
      Subgroup.closure ({tbarG} ∪ {x | ∃ i : Fin 6, Rep (kronK (genRows ε i)) x}) := by
  rw [grpOf, Subgroup.closure_le]
  rintro _ ⟨j, hj, rfl⟩
  rw [stage1Gens_size] at hj
  rcases j with _ | i
  · refine Subgroup.subset_closure (Or.inl ?_)
    show glOf (genK (stage1Gens ε) 0).1 (genK (stage1Gens ε) 0).2 = tbarG
    rw [genK_stage1Gens_zero]
    rfl
  · refine Subgroup.subset_closure (Or.inr ⟨⟨i, by omega⟩, ?_⟩)
    have h1 := rep_genG hg (i + 1)
    rwa [genK_stage1Gens_succ ε (by omega)] at h1

theorem tc_le_closure (ε : Eps) {tGens : Array (ℕ × ℕ)} (hg : gensOK tGens = true)
    (hsz : tGens.size = 7) (h0 : (tGens.getD 0 (0, 0)).1 = phiK)
    (hk : ∀ k < 6, (tGens.getD (k + 1) (0, 0)).1 = kronK (urRows ε k)) :
    grpOf tGens ≤ Subgroup.closure ({tbarG} ∪ {x | ∃ k : Fin 6, Rep (kronK (urRows ε k)) x}) := by
  rw [grpOf, Subgroup.closure_le]
  rintro _ ⟨j, hj, rfl⟩
  have hgen : ∀ j < 7, (genK tGens j).1 = (tGens.getD j (0, 0)).1 := fun j hj => by
    simp [genK, Array.getD_eq_getD_getElem?, hsz, hj]
  rw [hsz] at hj
  rcases j with _ | k
  · refine Subgroup.subset_closure (Or.inl ?_)
    have h1 := rep_genG hg 0
    rw [hgen 0 (by norm_num), h0] at h1
    exact h1.unique rep_tbarG
  · refine Subgroup.subset_closure (Or.inr ⟨⟨k, by omega⟩, ?_⟩)
    have h1 := rep_genG hg (k + 1)
    rwa [hgen (k + 1) hj, hk k (by omega)] at h1

section Plus


theorem bridgeModel_plus :
    BridgeModel modelPlus (fun i : Fin 6 => genRows .plus i) (fun k : Fin 6 => urRows .plus k) := by
  obtain ⟨cE, tcE, sE, hc, htc, h⟩ := bridge_check_plus
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := bridgeCheck_parts h
  exact
    { tbar_eq := rfl
      tbar_mem_TC := Plus.tbar_mem_TC
      tbar_mem_CC := Plus.TC_le_CC Plus.tbar_mem_TC
      CC_p := fun i x hx => Enum.mem_of_memK hc (h1 i i.2) hx
      CC_le := (grpOf_le_of_gensIn (Enum.of_enumOK hc).1 h2 h3).trans
        (stage1_le_closure .plus (Enum.of_enumOK h2).1)
      TC_u := fun k x hx => Enum.mem_of_memK htc (h6 k k.2).2 hx
      TC_le := tc_le_closure .plus (Enum.of_enumOK htc).1 h4 h5
        fun k hk => (h6 k hk).1 }

theorem false_of_bridgeCore_plus {G : Type*} [Group G] [Finite G] (hG : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) {t : G} {Q R W P U : Subgroup G} {ψ : Vec6 → G}
    {p u : Fin 6 → G}
    (hB : BridgeCore t Q R W P U ψ (fun i : Fin 6 => genRows .plus i) p
      (fun k : Fin 6 => urRows .plus k) u) : False :=
  Plus.false_of_stage2Hyp hG hnab (hB.stage2Hyp bridgeModel_plus)

end Plus

section Minus


theorem bridgeModel_minus :
    BridgeModel modelMinus (fun i : Fin 6 => genRows .minus i)
      (fun k : Fin 6 => urRows .minus k) := by
  obtain ⟨cE, tcE, sE, hc, htc, h⟩ := bridge_check_minus
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := bridgeCheck_parts h
  exact
    { tbar_eq := rfl
      tbar_mem_TC := Minus.tbar_mem_TC
      tbar_mem_CC := Minus.TC_le_CC Minus.tbar_mem_TC
      CC_p := fun i x hx => Enum.mem_of_memK hc (h1 i i.2) hx
      CC_le := (grpOf_le_of_gensIn (Enum.of_enumOK hc).1 h2 h3).trans
        (stage1_le_closure .minus (Enum.of_enumOK h2).1)
      TC_u := fun k x hx => Enum.mem_of_memK htc (h6 k k.2).2 hx
      TC_le := tc_le_closure .minus (Enum.of_enumOK htc).1 h4 h5
        fun k hk => (h6 k hk).1 }

theorem false_of_bridgeCore_minus {G : Type*} [Group G] [Finite G] (hG : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) {t : G} {Q R W P U : Subgroup G} {ψ : Vec6 → G}
    {p u : Fin 6 → G}
    (hB : BridgeCore t Q R W P U ψ (fun i : Fin 6 => genRows .minus i) p
      (fun k : Fin 6 => urRows .minus k) u) : False :=
  Minus.false_of_stage2Hyp hG hnab (hB.stage2Hyp bridgeModel_minus)

end Minus

end CFSG.EvenSmallLie.OmegaEight.Stage2
