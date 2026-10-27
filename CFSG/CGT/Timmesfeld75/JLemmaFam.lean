module

public import CFSG.CGT.Timmesfeld75.JLemmaSub
public import CFSG.CGT.Timmesfeld75.Lemma25
public import CFSG.CGT.Timmesfeld75.CentralQuotient

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open

section Numerics

variable {G : Type} [Group G] [Finite G] {R T : Subgroup G}

theorem four_le_card_map_pCore (hT : IsWC T) (hTR : T ≤ R) {g : G} (hg : g ∈ R)
    (hq : 2 * Nat.card (normIn T (conjSubgroup g T)) < Nat.card T) :
    4 ≤ Nat.card ((T.subgroupOf R).map (QuotientGroup.mk' (CFSG.pCore 2 ↥R))) := by
  set S := T.subgroupOf R with hS
  set O := CFSG.pCore 2 ↥R with hO
  have hcard := card_map_mk'_mul_card_inf S O
  have hSc : Nat.card S = Nat.card T := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTR).toEquiv
  have hinf : Nat.card ↥(S ⊓ O) ≤ Nat.card (normIn T (conjSubgroup g T)) := by
    refine Nat.card_le_card_of_injective
      (fun s => (⟨(s.1 : G), mem_normIn.2 ⟨Subgroup.mem_subgroupOf.1 s.2.1,
        coe_mem_normalizer_conjSubgroup_of_mem_pCore hT hTR hg s.2.2⟩⟩ :
          normIn T (conjSubgroup g T))) ?_
    intro a b hab
    have h1 : ((a.1 : ↥R) : G) = ((b.1 : ↥R) : G) :=
      congrArg (fun z : normIn T (conjSubgroup g T) => (z : G)) hab
    exact Subtype.ext (Subtype.ext h1)
  have hpos : 0 < Nat.card ↥(S ⊓ O) := Nat.card_pos
  have hlt : 2 < Nat.card (S.map (QuotientGroup.mk' O)) := by
    by_contra hle
    rw [not_lt] at hle
    have h5 : Nat.card (S.map (QuotientGroup.mk' O)) * Nat.card ↥(S ⊓ O) ≤
        2 * Nat.card ↥(S ⊓ O) := Nat.mul_le_mul_right _ hle
    rw [hcard] at h5
    omega
  have habel := isElemAbelian_map_of_hom (isWC_subgroupOf hT R hTR).1 (QuotientGroup.mk' O)
  refine four_le_card_of_isElemAbelian habel ?_ (ne_of_gt hlt)
  intro hbot
  rw [hbot, Subgroup.card_bot] at hlt
  omega

omit [Finite G] in
theorem pCore_ne_bot_of_normalizes {Q : Subgroup G} (hQR : Q ≤ R) (hQ2 : IsPGroup 2 Q)
    (hQn : ∀ x ∈ R, conjSubgroup x Q = Q) (hQ : Q ≠ ⊥) : CFSG.pCore 2 ↥R ≠ ⊥ := by
  intro hO
  have hRQ : R ≤ Subgroup.normalizer (Q : Set G) := fun x hx =>
    mem_normalizer_of_conjSubgroup_eq (hQn x hx)
  have hle : Q ≤ pCoreOf 2 R := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hQR hRQ hQ2
  have hbot : pCoreOf 2 R = ⊥ := by
    show (CFSG.Open.pCore 2 ↥R).map R.subtype = ⊥
    rw [hO, Subgroup.map_bot]
  exact hQ (le_bot_iff.1 (hle.trans hbot.le))

theorem card_quot_pCore_lt (hO : CFSG.pCore 2 ↥R ≠ ⊥) :
    Nat.card (↥R ⧸ CFSG.pCore 2 ↥R) < Nat.card G := by
  have h1 := Subgroup.card_mul_index (CFSG.pCore 2 ↥R)
  rw [Subgroup.index_eq_card] at h1
  have h2 : 1 < Nat.card ↥(CFSG.pCore 2 ↥R) := (Subgroup.one_lt_card_iff_ne_bot _).2 hO
  have h3 : Nat.card ↥R ≤ Nat.card G := Subgroup.card_le_card_group R
  have h4 : 0 < Nat.card (↥R ⧸ CFSG.pCore 2 ↥R) := Nat.card_pos
  nlinarith

end Numerics

end CFSG.CGT.Timmesfeld75
