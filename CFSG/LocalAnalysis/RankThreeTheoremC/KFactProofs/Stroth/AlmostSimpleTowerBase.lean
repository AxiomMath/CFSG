module

public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower.Abelian

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open CFSG CFSG.Open CFSG.AGLEmbedding
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

theorem outTowerAt_of_not_dvd_card_outer {K : Type*} [Group K] {p : ℕ}
    (hp : p.Prime) (h : ¬ p ∣ Nat.card (Outer K)) : OutTowerAt K p := by
  refine CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower.outTowerAt_of_mem_inner
    fun α ⟨k, hk⟩ => ?_
  have hcop : Nat.Coprime (p ^ k) (Nat.card (Outer K)) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).mpr h)
  have h1 : (QuotientGroup.mk α : Outer K) ^ (p ^ k) = 1 := by
    rw [← QuotientGroup.mk_pow, hk, QuotientGroup.mk_one]
  have h2 := orderOf_dvd_of_pow_eq_one h1
  have h3 : orderOf (QuotientGroup.mk α : Outer K) ∣ Nat.card (Outer K) := orderOf_dvd_natCard _
  have h4 := Nat.eq_one_of_dvd_coprimes hcop h2 h3
  exact (QuotientGroup.eq_one_iff α).1 (orderOf_eq_one_iff.1 h4)

theorem outTowerAt_of_outerComm {K : Type*} [Group K] {p : ℕ}
    (h : CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower.OuterComm K) : OutTowerAt K p :=
  CFSG.HardMathSupport.Curtis.Coordinator.SeitzNonNormal.outTowerAt_of_commutator_mem_inner h

theorem sylow_normal_of_pElements_mem {X : Type} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    {L : Subgroup X} [L.Normal] (h : ∀ x : X, (∃ k : ℕ, x ^ (p ^ k) = 1) → x ∈ L) :
    ∀ P : Sylow p (X ⧸ L), (P : Subgroup (X ⧸ L)).Normal := by
  intro P
  have hq : Function.Surjective (QuotientGroup.mk' L) := QuotientGroup.mk'_surjective L
  obtain ⟨R, hR⟩ := Sylow.mapSurjective_surjective hq p P
  have hRL : (R : Subgroup X) ≤ L := fun x hx => by
    obtain ⟨k, hk⟩ := R.isPGroup' ⟨x, hx⟩
    exact h x ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hbot : (P : Subgroup (X ⧸ L)) = ⊥ := by
    rw [← hR, Sylow.coe_mapSurjective, eq_bot_iff]
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_bot, QuotientGroup.mk'_apply]
    exact (QuotientGroup.eq_one_iff x).2 (hRL hx)
  rw [hbot]
  exact Subgroup.normal_bot

theorem rankLE2_of_subgroup {X : Type*} [Group X] {p : ℕ} (L : Subgroup X)
    (h : ∀ E : Subgroup X, IsElemAbelian p E → Nat.card E ≤ p ^ 2) :
    CFSG.LieType.SeitzGeneration.RankLE2 p ↥L := by
  intro F hF
  have h1 := h (F.map L.subtype) (IsElemAbelian.map hF _)
  rwa [Subgroup.card_map_of_injective L.subtype_injective] at h1

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
