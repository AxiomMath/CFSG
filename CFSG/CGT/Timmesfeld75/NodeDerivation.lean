module

public import CFSG.CGT.Timmesfeld75.Statements
public import CFSG.CGT.Timmesfeld75.NodeAux

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open

theorem corBHyp_of_ti_of_weaklyClosed {G : Type} [Group G] {B : Subgroup G}
    (hel : IsElemAbelian 2 B)
    (hTI : ∀ g : G, B ⊓ conjSubgroup g⁻¹ B = ⊥ ∨ B ⊓ conjSubgroup g⁻¹ B = B)
    (hWC : ∀ g : G, conjSubgroup g⁻¹ B ≤ Subgroup.normalizer (B : Set G) →
      conjSubgroup g⁻¹ B = B) :
    CorBHyp B := by
  refine ⟨hel, fun g => ?_, fun g => ⟨fun hcomm => ?_, fun hgB x hx y hy => ?_⟩⟩
  · simpa using hTI g⁻¹
  · have hle : conjSubgroup g B ≤ Subgroup.normalizer (B : Set G) := fun y hy =>
      Subgroup.centralizer_le_normalizer _
        (Subgroup.mem_centralizer_iff.2 fun n hn => (hcomm n hn y hy).eq)
    have h := hWC g⁻¹
    rw [inv_inv] at h
    exact h hle
  · rw [hgB] at hy
    exact commute_of_isElemAbelian hel hx hy

theorem normalClosure_eq_top_of_simple {G : Type} [Group G] [IsSimpleGroup G] {B : Subgroup G}
    (hB : B ≠ ⊥) : Subgroup.normalClosure (B : Set G) = ⊤ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.normalClosure (B : Set G))
    with h | h
  · refine absurd (le_bot_iff.1 fun y hy => ?_) hB
    have hyN : y ∈ Subgroup.normalClosure (B : Set G) := Subgroup.subset_normalClosure hy
    rwa [h] at hyN
  · exact h

theorem listGroup_of_thmAConclusion_simple {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (heven : Even (Nat.card G)) {B : Subgroup G}
    (hnc : Subgroup.normalClosure (B : Set G) = ⊤) (h : ThmAConclusion B) : ListGroup G := by
  obtain ⟨N, hN, hNel, hcase⟩ := h
  have e₁ : ↥(Subgroup.normalClosure (B : Set G)) ≃* G :=
    (MulEquiv.subgroupCongr hnc).trans Subgroup.topEquiv
  have : IsSimpleGroup ↥(Subgroup.normalClosure (B : Set G)) := e₁.isSimpleGroup
  have hN0 : N = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with hbot | htop
    · exact hbot
    · obtain ⟨a, b, hab⟩ := hnonab
      have ha : e₁.symm a ∈ N := htop ▸ Subgroup.mem_top _
      have hb : e₁.symm b ∈ N := htop ▸ Subgroup.mem_top _
      have hc := (commute_of_isElemAbelian hNel ha hb).eq
      exact absurd (by simpa using congrArg e₁ hc) hab
  have eQ : ↥(Subgroup.normalClosure (B : Set G)) ⧸ N ≃* G :=
    ((QuotientGroup.quotientMulEquivOfEq hN0).trans QuotientGroup.quotientBot).trans e₁
  have : IsSimpleGroup (↥(Subgroup.normalClosure (B : Set G)) ⧸ N) := eQ.isSimpleGroup
  have : Finite (↥(Subgroup.normalClosure (B : Set G)) ⧸ N) :=
    Finite.of_equiv G eQ.symm.toEquiv
  have hnonabQ : ∃ a b : ↥(Subgroup.normalClosure (B : Set G)) ⧸ N, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnonab
    exact ⟨eQ.symm a, eQ.symm b, fun hc => hab (by simpa using congrArg eQ hc)⟩
  have hevenQ : Even (Nat.card (↥(Subgroup.normalClosure (B : Set G)) ⧸ N)) := by
    rwa [Nat.card_congr eQ.toEquiv]
  rcases hcase with hZ | hcov
  · exact absurd hZ (not_zStarCase_of_simple _ hnonabQ hevenQ)
  · exact ListGroup.of_mulEquiv eQ (listGroup_of_isCoveringOfList_simple _ hnonabQ hcov)

theorem nodeStatement_of_corollaryB (hB : CorollaryBStmt) : NodeStatement := by
  intro G _ _ _ hnonab B hel hcard hTI hWC
  obtain ⟨x, hxB, hx1⟩ : ∃ x ∈ B, x ≠ 1 := by
    rcases B.bot_or_exists_ne_one with hbot | h
    · rw [hbot, Subgroup.card_bot] at hcard
      omega
    · exact h
  have heven : Even (Nat.card G) := by
    have hord : orderOf x = 2 := orderOf_eq_prime (hel.2 x hxB) hx1
    exact even_iff_two_dvd.2 (hord ▸ orderOf_dvd_natCard x)
  have hBne : B ≠ ⊥ := fun h => hx1 (Subgroup.mem_bot.1 (h ▸ hxB))
  exact listGroup_of_thmAConclusion_simple hnonab heven (normalClosure_eq_top_of_simple hBne)
    (hB G B (corBHyp_of_ti_of_weaklyClosed hel hTI hWC))

end CFSG.CGT.Timmesfeld75
