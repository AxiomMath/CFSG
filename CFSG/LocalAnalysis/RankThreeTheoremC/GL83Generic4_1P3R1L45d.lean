module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Basic
import CFSG.LocalAnalysis.RankThreeTheoremC.ObstructionElements
import CFSG.LocalAnalysis.AGLEmbedding.ReducedOrbitsAux

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

theorem m11l45_normalizer_le (hS : Setting G) (hU0 : FullCoreLocal G)
    (hp : 3 ∈ rankThreeSigmaA G) {P : Sylow 3 G} {M : Subgroup G} (hM : IsCoreMaxLocal 3 P M)
    {x : G} (hxP : x ∈ (P : Subgroup G)) (hxo : orderOf x = 3) {J : Subgroup G}
    (hxJc : ∀ j ∈ J, x * j = j * x) (hxJ : x ∉ J) {R : Subgroup ↥J}
    (hRP : R.map J.subtype ≤ (P : Subgroup G)) (hR : R ≠ ⊥) {n : ↥J}
    (hn : n ∈ normalizer (R : Set ↥J)) : (n : G) ∈ M := by
  have hprime : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hprime⟩
  obtain ⟨hPM, -⟩ := sylow_le_of_isCoreMaxLocal hS hp hM
  set RG : Subgroup G := R.map J.subtype with hRG
  have hRp : IsPGroup 3 ↥R :=
    (P.isPGroup'.to_le hRP).of_equiv
      (Subgroup.equivMapOfInjective R J.subtype J.subtype_injective).symm
  have hRn : Nontrivial ↥R := (Subgroup.nontrivial_iff_ne_bot R).mpr hR
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hRp
  have hdvd : 3 ∣ Nat.card ↥R := by
    have h1 : 1 < Nat.card ↥R := Finite.one_lt_card
    rw [hk] at h1 ⊢
    have hk0 : k ≠ 0 := by
      rintro rfl
      simp at h1
    exact dvd_pow_self 3 hk0
  obtain ⟨r, hr⟩ := exists_prime_orderOf_dvd_card' (G := ↥R) 3 hdvd
  have hrJ : ((r : ↥J) : G) ∈ J := (r : ↥J).2
  have hro : orderOf ((r : ↥J) : G) = 3 := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hr]
  have hrRG : ((r : ↥J) : G) ∈ RG := ⟨(r : ↥J), r.2, rfl⟩
  have hrx : ((r : ↥J) : G) ∉ zpowers x := by
    intro hmem
    have hle : zpowers ((r : ↥J) : G) ≤ zpowers x := zpowers_le.mpr hmem
    have heq : zpowers ((r : ↥J) : G) = zpowers x := by
      refine Subgroup.eq_of_le_of_card_ge hle ?_
      rw [Nat.card_zpowers, Nat.card_zpowers, hro, hxo]
    exact hxJ (zpowers_le.mpr hrJ (heq ▸ mem_zpowers x))
  have hHP : RG ⊔ zpowers x ≤ (P : Subgroup G) := sup_le hRP (zpowers_le.mpr hxP)
  have hHp : IsPGroup 3 ↥(RG ⊔ zpowers x) := P.isPGroup'.to_le hHP
  have hH2 : 2 ≤ CFSG.Open.pRank 3 (RG ⊔ zpowers x) :=
    CFSG.AGLEmbedding.two_le_pRank_of_commute_of_not_mem_zpowers hprime hxo
      (by rw [← hro]; exact pow_orderOf_eq_one _) hrx (hxJc _ hrJ) (mem_sup_right (mem_zpowers x))
      (mem_sup_left hrRG)
  have hNH : normalizer ((RG ⊔ zpowers x : Subgroup G) : Set G) ≤ M :=
    normalizer_le_of_le_of_two_le_pRank hS hU0 hp hM hHp (hHP.trans hPM) hH2
  have hnR : (n : G) ∈ normalizer (RG : Set G) := Subgroup.le_normalizer_map J.subtype ⟨n, hn, rfl⟩
  have hnx : (n : G) ∈ normalizer ((zpowers x : Subgroup G) : Set G) := by
    refine Subgroup.centralizer_le_normalizer ((zpowers x : Subgroup G) : Set G)
      (mem_centralizer_iff.mpr fun h hh => ?_)
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp hh
    exact ((Commute.zpow_left (hxJc _ n.2 : Commute x (n : G)) m).symm).eq.symm
  exact hNH (Subgroup.inf_normalizer_le_normalizer_sup RG (zpowers x) ⟨hnR, hnx⟩)

end CFSG.LocalAnalysis.RankThreeTheoremC
