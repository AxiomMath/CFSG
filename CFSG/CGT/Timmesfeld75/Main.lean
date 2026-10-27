module

public import CFSG.CGT.Timmesfeld75.TheoremA1
public import CFSG.CGT.Timmesfeld75.Forms
public import CFSG.CGT.Timmesfeld75.O2Lift

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open

theorem timmesfeldTransitivity_of_inputs (hS : SimpleCaseStmt) (h215 : Lemma215Stmt) :
    TimmesfeldTransitivity :=
  fun _ _ _ _ hL hO2 => (theoremA1_of_simpleCase hS h215 hL hO2).2

theorem timmesfeldTransitivityTI_of_inputs (hS : SimpleCaseStmt) (h215 : Lemma215Stmt) :
    TimmesfeldTransitivityTI :=
  transitivityTI_of_transitivity (timmesfeldTransitivity_of_inputs hS h215)

theorem eq_bot_of_normal_isPGroup_quotient_pCore {K : Type*} [Group K]
    (P : Subgroup (K ⧸ CFSG.pCore 2 K)) (hP : P.Normal) (hP2 : IsPGroup 2 P) : P = ⊥ := by
  have hPc : IsPGroup 2 (P.comap (QuotientGroup.mk' (CFSG.pCore 2 K))) := by
    refine hP2.comap_of_ker_isPGroup _ ?_
    rw [QuotientGroup.ker_mk']
    exact CFSG.pCore_isPGroup
  have hPn : (P.comap (QuotientGroup.mk' (CFSG.pCore 2 K))).Normal := hP.comap _
  have hle : P.comap (QuotientGroup.mk' (CFSG.pCore 2 K)) ≤ CFSG.pCore 2 K :=
    le_sSup ⟨hPn, hPc⟩
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective x
  have := hle (Subgroup.mem_comap.2 hx)
  rw [Subgroup.mem_bot]
  exact (QuotientGroup.eq_one_iff k).2 this

theorem theoremAStmt_of_inputs (hS : SimpleCaseStmt) (h215 : Lemma215Stmt) : TheoremAStmt := by
  intro G _ _ T hT
  set K := Subgroup.normalClosure (T : Set G) with hKdef
  have hTK : IsWC (T.subgroupOf K) := isWC_subgroupOf_normalClosure hT
  have hKtop := normalClosure_subgroupOf_eq_top hT
  have hWC := isWC_map_pCore hTK hKtop
  have hKb : Subgroup.normalClosure
      ((((T.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 K)) :
        Subgroup (K ⧸ CFSG.pCore 2 K)) : Set (K ⧸ CFSG.pCore 2 K))) = ⊤ := by
    rw [Subgroup.coe_map, ← Subgroup.map_normalClosure _ _ (QuotientGroup.mk'_surjective _),
      hKtop, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  obtain ⟨hc, htrans⟩ := conclusion_of_simpleCase hS h215 hWC hKb
    eq_bot_of_normal_isPGroup_quotient_pCore
  refine conclusionFor_of_pCore_quotient hTK hKtop ?_
  rcases hc with ⟨-, h2⟩ | ⟨h4, hcov⟩
  · exact Or.inl h2
  · exact Or.inr ⟨h4, hcov, htrans⟩

end CFSG.CGT.Timmesfeld75
