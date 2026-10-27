module

public import CFSG.CGT.Timmesfeld75.TheoremA1
public import CFSG.CGT.Timmesfeld75.StdPair

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG.Open CFSG.CGT.Timmesfeld75

theorem std_of_simpleCase (hS : SimpleCaseListStmt) (h215 : Lemma215Stmt) (hL : ListWCIdentification)
    {K : Type} [Group K] [Finite K] {T : Subgroup K} (hT : IsWC T)
    (hK : Subgroup.normalClosure (T : Set K) = ⊤)
    (hO2 : ∀ N : Subgroup K, N.Normal → IsPGroup 2 N → N = ⊥) (h4 : 4 ≤ Nat.card T) :
    IsSimpleGroup (K ⧸ Subgroup.center K) ∧ ListGroup (K ⧸ Subgroup.center K) ∧
      StdPair (K ⧸ Subgroup.center K) (T.map (QuotientGroup.mk' (Subgroup.center K))) ∧
      commutator K = ⊤ ∧ Odd (Nat.card (Subgroup.center K)) := by
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
  have hlist := hS (K ⧸ Z) hnab _ hWCb h4b
  have hcomm_top : commutator K = ⊤ :=
    commutator_eq_top_of_odd_center hT.1 hK hZodd (center_sup_commutator_eq_top hsimple hnab)
  exact ⟨hsimple, hlist, hL (K ⧸ Z) hlist _ hWCb h4b, hcomm_top, hZodd⟩

end CFSG.CGT.PushingUpLit.CGT6
