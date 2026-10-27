module

public import CFSG.LargeExtraspecial.S4TwoInput
public import CFSG.CGT.Timmesfeld75.Main

public section

namespace CFSG.LargeExtraspecial.TI75

open CFSG.CGT.Timmesfeld75

theorem form2StrongConclusion_of_inputs (hS : SimpleCaseStmt) (h215 : Lemma215Stmt)
    (hI : ListWCIdentification) {K : Type} [Group K] [Finite K] {T : Subgroup K} (hT : IsWC T)
    (hK : Subgroup.normalClosure (T : Set K) = ⊤)
    (hO2 : ∀ N : Subgroup K, N.Normal → IsPGroup 2 N → N = ⊥) :
    S4.Form2StrongConclusion K T := by
  by_cases hle : Nat.card T ≤ 2
  · rcases form2_core_of_simpleCase hS h215 hI hT hK hO2 with h | ⟨h4, -⟩
    · exact Or.inl ⟨hle, h⟩
    · omega
  have hTbot : T ≠ ⊥ := by
    rintro rfl
    rw [Subgroup.card_bot] at hle
    omega
  have h4 : 4 ≤ Nat.card T := four_le_card_of_isElemAbelian hT.1 hTbot (by omega)
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

theorem form2StrongStmt_of_inputs (hS : SimpleCaseStmt) (h215 : Lemma215Stmt)
    (hI : ListWCIdentification) : S4.Form2StrongStmt := by
  intro X _ _ L hL
  set K := Subgroup.normalClosure (L : Set X) with hKdef
  have hTK : IsWC (L.subgroupOf K) := isWC_subgroupOf_normalClosure hL
  have hKtop := normalClosure_subgroupOf_eq_top hL
  have hWC := isWC_map_pCore hTK hKtop
  have hKb : Subgroup.normalClosure
      ((((L.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 K)) :
        Subgroup (K ⧸ CFSG.pCore 2 K)) : Set (K ⧸ CFSG.pCore 2 K))) = ⊤ := by
    rw [Subgroup.coe_map, ← Subgroup.map_normalClosure _ _ (QuotientGroup.mk'_surjective _),
      hKtop, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  exact form2StrongConclusion_of_inputs hS h215 hI hWC hKb
    eq_bot_of_normal_isPGroup_quotient_pCore

end CFSG.LargeExtraspecial.TI75
