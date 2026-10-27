module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L618
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P65Basic
import CFSG.LocalAnalysis.RankFourTheoremC.Equivalence
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.RelativePairGeometry
import CFSG.RankThree.PartTwo.Sec21.Item23Tools

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding CFSG.AGLEmbeddingD2
  CFSG.LocalAnalysis.RankThreeTheoremC Subgroup

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G}

theorem stronglyEmbedded_of_zpowers (hS : Situation G p P M) {f : ℕ} (hf : f.Prime)
    (hf2 : f ≠ 2) {F₀ : Sylow f G} (hD : D1Local f F₀ M) (hdvd : f ∣ Nat.card M)
    (hkey : ∀ y ∈ (F₀ : Subgroup G), y ≠ 1 → y ^ f = 1 →
      normalizer ((zpowers y : Subgroup G) : Set G) ≤ M) :
    GLBStronglyEmbedded f M := by
  haveI : Fact f.Prime := ⟨hf⟩
  have hFC := hS.toGlobal.fullCore
  have hF₀M : (F₀ : Subgroup G) ≤ M := sylow_le_of_core hD
  have hP : ∀ X : Subgroup G, X ≤ (F₀ : Subgroup G) → IsPGroup f X → X ≠ ⊥ →
      normalizer (X : Set G) ≤ M := by
    intro X hXP hXp hX1
    by_cases h2 : 2 ≤ Open.pRank f X
    · exact normalizer_le_of_two_le_pRank hFC hD hXp (hXP.trans hF₀M) h2
    · have hcyc : IsCyclic X := by
        by_contra hnc
        exact h2 (two_le_pRank_of_not_isCyclic hf hf2 hXp hnc)
      obtain ⟨n, hn⟩ := hXp.exists_card_eq
      have hn0 : n ≠ 0 := by
        rintro rfl
        exact hX1 ((Subgroup.card_eq_one).1 (by simpa using hn))
      obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := X) f (by
        rw [hn]; exact dvd_pow_self f hn0)
      have h1 : 1 ≤ Open.pRank f X := by
        have hyf : (y : G) ^ f = 1 := by
          have := pow_orderOf_eq_one y
          rw [hy] at this
          simpa using congrArg Subtype.val this
        have hy1 : (y : G) ≠ 1 := fun h => by
          have : y = 1 := Subtype.ext h
          rw [this, orderOf_one] at hy
          exact hf.one_lt.ne hy
        refine le_pRank_of_isElemAbelian hf (Y := zpowers (y : G)) ?_ ?_ (k := 1) ?_
        · exact zpowers_le.2 y.2
        · exact (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian f _).1
            (CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one hyf)
        · rw [Nat.card_zpowers, orderOf_eq_prime hyf hy1]
          simp
      obtain ⟨x, hxX, hx1, hxf, hNX⟩ :=
        exists_pow_eq_one_normalizer_le_of_isCyclic hf hXp hcyc h1
      exact hNX.trans (hkey x (hXP hxX) hx1 hxf)
  have := hS.simple
  refine CFSG.RankThree.PartTwo.Sec21.glbStronglyEmbedded_of_normalizer_le
    (CFSG.PreuniquenessRankFour.Helpers.twoLocal_ne_top hS.nonab hD.maxLocal.1) hdvd ?_
  intro X hXM hXp hX1
  obtain ⟨m, hm⟩ := pGroup_conjugate_into_sylow_within_overgroup f hf F₀ M hF₀M X hXp hXM
  have hXm : X.map (MulAut.conj (m : G)).toMonoidHom ≠ ⊥ := fun h =>
    hX1 ((map_eq_bot_iff_of_injective (f := (MulAut.conj (m : G)).toMonoidHom) X
      (MulAut.conj (m : G)).injective).mp h)
  have hN := hP _ hm (hXp.map _) hXm
  have hmap : (normalizer (X : Set G)).map (MulAut.conj (m : G)).toMonoidHom ≤ M := by
    rw [Subgroup.map_equiv_normalizer_eq]
    exact hN
  exact (conjugate_subgroup_le_iff_of_conjugator_mem _ M (m : G) m.2).1 hmap

theorem stronglyEmbedded_of_rank (hS : Situation G p P M) {f : ℕ} (hf : f.Prime) (hf2 : f ≠ 2)
    (hfp : f ≠ p) (hnsolv : ¬ Group.IsSolvable M) (h4 : 4 ≤ Open.pRank f M)
    (hy : f < p → ∀ y ∈ M, orderOf y = f →
      3 ≤ Open.pRank f (M ⊓ centralizer ({y} : Set G))) :
    GLBStronglyEmbedded f M := by
  haveI : Fact f.Prime := ⟨hf⟩
  obtain ⟨Fh, hFh⟩ := CFSG.ABGLocalTools.exists_isSylowOf f M
  have hFhM : Fh ≤ M := hFh.le
  have hFhp : IsPGroup f Fh := hFh.isPGroup
  have h4' : 4 ≤ Open.pRank f Fh := by
    rw [pRank_eq_of_isSylowOf hf hFh]
    exact h4
  obtain ⟨F₀, hle⟩ := hFhp.exists_le_sylow
  obtain ⟨hD, -⟩ := p65_d1Local_of_le hS hf hf2 h4 hFhM hFhp (by omega) F₀ hle
  have hdvd : f ∣ Nat.card M := dvd_card_of_one_le_pRank hf (by omega)
  have hfromAS : GLBAlmostStrong M f → GLBStronglyEmbedded f M := by
    rintro ⟨-, hMtop, -, P', -, -, hcase⟩
    rcases hcase with ⟨hd, hall⟩ | ⟨-, hsolv, -, -⟩
    · exact ⟨hMtop, hd, hall⟩
    · exact absurd hsolv hnsolv
  rcases lt_or_gt_of_ne hfp with hlt | hgt
  · by_cases hPe : ∃ y : G, IsPElement f M y
    · exact hfromAS (hS.toGlobal.thmC f F₀ M hD hPe).1
    · refine stronglyEmbedded_of_zpowers hS hf hf2 hD hdvd ?_
      intro y hyF hy1 hyf
      have hyM : y ∈ M := sylow_le_of_core hD hyF
      have hyo : orderOf y = f := orderOf_eq_prime hyf hy1
      have h3 := hy hlt y hyM hyo
      have hCM : centralizer ({y} : Set G) ≤ M := by
        by_contra hnot
        exact hPe ⟨y, hyM, hyo, h3, hnot⟩
      refine normalizer_zpowers_le_of_centralizer_rank' hS.toGlobal.fullCore hD hCM ?_
      exact le_trans (by norm_num : 2 ≤ 3) (le_trans h3 (CFSG.SectionRank.pRank_mono hf.one_lt
        (inf_le_right : M ⊓ centralizer ({y} : Set G) ≤ centralizer ({y} : Set G))))
  · exact hfromAS (hS.larger f F₀ M hgt hD).1

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
