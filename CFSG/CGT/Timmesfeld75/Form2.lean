module

public import CFSG.CGT.Timmesfeld75.StdPair
public import CFSG.CGT.Timmesfeld75.TheoremA1

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open

@[expose] def Form2Conclusion (K : Type) [Group K] (T : Subgroup K) : Prop :=
  ZStarCase K ∨
    (4 ≤ Nat.card T ∧ commutator K = ⊤ ∧ Odd (Nat.card (Subgroup.center K)) ∧
      IsSimpleGroup (K ⧸ Subgroup.center K) ∧
      StdPair (K ⧸ Subgroup.center K) (T.map (QuotientGroup.mk' (Subgroup.center K))))

theorem form2_core_of_simpleCase (hS : SimpleCaseStmt) (h215 : Lemma215Stmt)
    (hI : ListWCIdentification) {K : Type} [Group K] [Finite K] {T : Subgroup K} (hT : IsWC T)
    (hK : Subgroup.normalClosure (T : Set K) = ⊤)
    (hO2 : ∀ N : Subgroup K, N.Normal → IsPGroup 2 N → N = ⊥) : Form2Conclusion K T := by
  by_cases hTbot : T = ⊥
  · subst hTbot
    refine Or.inl ?_
    have hK1 : (⊤ : Subgroup K) = ⊥ := by
      rw [← hK]; exact (Subgroup.normalClosure_eq_self (⊥ : Subgroup K))
    refine zStarCase_of_commutative fun a b => ?_
    have ha : a = 1 := (Subgroup.mem_bot).1 (hK1 ▸ Subgroup.mem_top a)
    have hb : b = 1 := (Subgroup.mem_bot).1 (hK1 ▸ Subgroup.mem_top b)
    rw [ha, hb]
  by_cases h2 : Nat.card T = 2
  · refine Or.inl ?_
    have h := zStarCase_normalClosure_of_card_two hT h2
    rw [hK] at h
    exact zStarCase_of_mulEquiv Subgroup.topEquiv h
  have h4 : 4 ≤ Nat.card T := four_le_card_of_isElemAbelian hT.1 hTbot h2
  refine Or.inr ?_
  have hZodd := odd_card_center hO2
  have hrad := solvable_radical_bot_quotient hT h4 hK hO2
  set Z : Subgroup K := Subgroup.center K with hZdef
  have hWCb : IsWC (T.map (QuotientGroup.mk' Z)) := hT.map_quotient_central_odd Z le_rfl hZodd
  have hKb : Subgroup.normalClosure
      ((T.map (QuotientGroup.mk' Z) : Subgroup (K ⧸ Z)) : Set (K ⧸ Z)) = ⊤ := by
    rw [Subgroup.coe_map, ← Subgroup.map_normalClosure _ _ (QuotientGroup.mk'_surjective _), hK,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  have h4b := four_le_card_map_central_odd hT.1 Z hZodd h4
  have hsimple : IsSimpleGroup (K ⧸ Z) := h215 (K ⧸ Z) _ hWCb h4b hKb hrad
  have hnab : ∃ a b : K ⧸ Z, a * b ≠ b * a := by
    by_contra hcomm
    push Not at hcomm
    have hsolv : Group.IsSolvable (⊤ : Subgroup (K ⧸ Z)) :=
      Group.isSolvable_of_comm fun a b => Subtype.ext (hcomm a b)
    have htop := hrad ⊤ inferInstance hsolv
    have hbot : T.map (QuotientGroup.mk' Z) = ⊥ := by
      rw [eq_bot_iff]
      intro x _
      rw [← htop]
      exact Subgroup.mem_top x
    rw [hbot, Subgroup.card_bot] at h4b
    omega
  obtain ⟨hlist, -⟩ := hS (K ⧸ Z) hnab _ hWCb h4b
  have hcomm_top : commutator K = ⊤ :=
    commutator_eq_top_of_odd_center hT.1 hK hZodd (center_sup_commutator_eq_top hsimple hnab)
  exact ⟨h4, hcomm_top, hZodd, hsimple, hI (K ⧸ Z) hlist _ hWCb h4b⟩

abbrev Form2Q (X : Type) [Group X] (L : Subgroup X) : Type :=
  ↥(Subgroup.normalClosure (L : Set X)) ⧸ CFSG.pCore 2 ↥(Subgroup.normalClosure (L : Set X))

@[expose] def Form2L (X : Type) [Group X] (L : Subgroup X) : Subgroup (Form2Q X L) :=
  (L.subgroupOf (Subgroup.normalClosure (L : Set X))).map (QuotientGroup.mk' _)

end CFSG.CGT.Timmesfeld75
