module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSetup

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3

open CFSG.Open
open CFSG.LocalAnalysis.AGL81TheoremCD.Section12 (gammaIn gammaOver)

variable {G : Type} [Group G] [Finite G]

theorem gammaIn_le_gammaOver {k p : ℕ} (hp : 1 < p) (R T : Subgroup G) :
    gammaIn k p R T ≤ gammaOver k p R T := by
  rw [gammaIn]
  refine Subgroup.map_le_iff_le_comap.mpr ?_
  refine (CFSG.RankThreeCoreUniqueness.Helpers.gamma_le_iff k p (R.subgroupOf T)
    ((gammaOver k p R T).comap T.subtype)).mpr ?_
  intro Q hQ hQrank n hn
  rw [Subgroup.mem_comap]
  have hQR : Q.map T.subtype ≤ R := by
    rintro _ ⟨q, hq, rfl⟩
    exact Subgroup.mem_subgroupOf.mp (hQ hq)
  have hrank : k ≤ CFSG.Open.pRank p (Q.map T.subtype) := by
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := p) (Q.map T.subtype),
      ← CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp
        (Q.equivMapOfInjective T.subtype T.subtype_injective),
      ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := p) Q]
    exact hQrank
  have hN : T.subtype n ∈ Subgroup.normalizer ((Q.map T.subtype : Subgroup G) : Set G) :=
    Subgroup.le_normalizer_map T.subtype ⟨n, hn, rfl⟩
  refine (le_iSup₂_of_le (Q.map T.subtype) hQR (le_iSup_of_le hrank le_rfl) :
    Subgroup.normalizer ((Q.map T.subtype : Subgroup G) : Set G) ⊓ T ≤ gammaOver k p R T) ?_
  exact ⟨hN, n.2⟩

theorem gammaOver_mono_right {k p : ℕ} {R T T' : Subgroup G} (hT : T ≤ T') :
    gammaOver k p R T ≤ gammaOver k p R T' :=
  iSup₂_mono fun _ _ => iSup_mono fun _ => inf_le_inf_left _ hT

theorem threeNine_not_le_gammaOver {X : Type} [Group X] [Finite X]
    (K E D X₁ : Subgroup X) (p d : ℕ) (hp : p.Prime) (hdp : d.Prime)
    (hDsyl : CFSG.ABGLocalTools.IsSylowOf d D ⊤) (hDne : D ≠ ⊥) (hX1 : X₁ < K ⊔ D)
    (hΓE : gammaOver 1 p E (K ⊔ D) ≤ X₁) (hΓD : gammaIn 1 d D (K ⊔ D) ≤ X₁) :
    ¬ K ≤ gammaOver 1 p E K := by
  intro hK
  have hfact : Fact d.Prime := ⟨hdp⟩
  have hDp : IsPGroup d D := hDsyl.isPGroup
  have hDsubp : IsPGroup d (D.subgroupOf (K ⊔ D)) :=
    hDp.of_equiv (Subgroup.subgroupOfEquivOfLe (le_sup_right : D ≤ K ⊔ D)).symm
  have hDsubne : D.subgroupOf (K ⊔ D) ≠ ⊥ := by
    intro hbot
    rw [Subgroup.subgroupOf_eq_bot] at hbot
    rw [disjoint_iff, inf_eq_left.mpr (le_sup_right : D ≤ K ⊔ D)] at hbot
    exact hDne hbot
  have hDrank : 1 ≤ CFSG.Open.pRank d (D.subgroupOf (K ⊔ D)) := by
    have hdvd : d ∣ Nat.card (D.subgroupOf (K ⊔ D)) :=
      hDsubp.card_eq_or_dvd.resolve_left fun h => hDsubne (Subgroup.card_eq_one.mp h)
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := d) (D.subgroupOf (K ⊔ D))]
    exact CFSG.one_le_pRank_of_dvd_card hdp hdvd
  have hDX1 : D ≤ X₁ := (le_gammaIn_self (le_sup_right : D ≤ K ⊔ D) hDrank).trans hΓD
  have hKX1 : K ≤ X₁ :=
    hK.trans ((gammaOver_mono_right (le_sup_left : K ≤ K ⊔ D)).trans hΓE)
  exact (ne_of_lt hX1) (le_antisymm hX1.le (sup_le hKX1 hDX1))

end CFSG.LocalAnalysis.AGL81I.Section3
