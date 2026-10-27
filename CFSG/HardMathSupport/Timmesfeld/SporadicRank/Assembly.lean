module

public import CFSG.HardMathSupport.Timmesfeld.SporadicRank.CoverLower

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicRank

open CFSG.AGLEmbedding CFSG.Open CFSG.SectionRank

theorem pRank_le_of_not_dvd {G : Type} [Group G] [Finite G] {p k : ℕ} (hp : p.Prime)
    (h : ¬ p ^ (k + 1) ∣ Nat.card G) : CFSG.Open.pRank p (⊤ : Subgroup G) ≤ k := by
  have := Fact.mk hp
  refine pRank_le hp.one_lt fun E _ hE => ?_
  have hEp : IsPGroup p E := fun g => ⟨1, by rw [pow_one]; exact Subtype.ext (hE.2 g g.2)⟩
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hEp
  rw [ha]
  refine Nat.pow_le_pow_right hp.pos (Nat.le_of_lt_succ ?_)
  by_contra hlt
  exact h ((pow_dvd_pow p (not_lt.mp hlt)).trans (ha ▸ Subgroup.card_subgroup_dvd_card E))

theorem factorization_eq_of_pow_dvd {p N s : ℕ} (hp : p.Prime) (hN0 : N ≠ 0)
    (hv : p ^ s ∣ N ∧ ¬ p ^ (s + 1) ∣ N) : N.factorization p = s := by
  have h1 := (hp.pow_dvd_iff_le_factorization hN0).1 hv.1
  have h2 : ¬ s + 1 ≤ N.factorization p :=
    fun h => hv.2 ((hp.pow_dvd_iff_le_factorization hN0).2 h)
  omega

@[expose] def BigCoverRankAt (s : TauCeti.SporadicName) : Prop :=
  ∀ (L : Type) [Group L] [Finite L], CFSG.Open.IsQuasisimple L →
    Nonempty (L ⧸ Subgroup.center L ≃* (TauCeti.CFSGIndex.sporadic s).Group) →
    Nat.card (Subgroup.center L) ∣ 6 → 3 ∣ Nat.card (Subgroup.center L) →
    CFSG.Open.pRank 3 (⊤ : Subgroup (L ⧸ Subgroup.center L)) ≤
      CFSG.Open.pRank 3 (⊤ : Subgroup L) + 1

theorem bigCoverRankAt_of_data {s : TauCeti.SporadicName} {X : Type} [Group X] [Finite X]
    (b : Nonempty (X ≃* (TauCeti.CFSGIndex.sporadic s).Group)) (D : ModuleSpec X 3)
    (hA : D.NoAlt) (hF : D.NoFun)
    (hup : CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ D.n + 2) : BigCoverRankAt s := by
  intro L _ _ hq ⟨eL⟩ hZ6 h3
  obtain ⟨b⟩ := b
  have hlow := lower_of_cover hq (eL.trans b.symm) hZ6 h3 D hA hF
  have heq := pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) (eL.trans b.symm)
  omega

end CFSG.HardMathSupport.Timmesfeld.SporadicRank
