module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P622K3Basic
import CFSG.Quasithin.Background.A3FactsClassical
import CFSG.LocalAnalysis.SectionRank.AmbientRank
import CFSG.LocalAnalysis.SectionRank.GroupRankTransport
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P622K3Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P622KxEmb

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.Yardstones.Md0ec50421ce4 (catalogIs onLie)
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty (S622IsSimpleSection KFact1019 KFactSporThree
  IsDihedralTypeIndex IsReeIndex IsRankTwoOddIndex)

variable {G : Type} [Group G] [Finite G] {P : Sylow 3 G} {M : Subgroup G} {x z : G}
  {T S L : Subgroup G}

theorem isDihedralTypeIndex_split {i : TauCeti.LieTypeIndex} (h : IsDihedralTypeIndex i) :
    IsLTwoIndex i ∨ IsLThreeUThreeIndex i := by
  cases i with
  | A n q =>
    match n, h with
    | 0, h => exact False.elim h
    | 1, h => exact Or.inl h
    | 2, h => exact Or.inr h
    | n + 3, h => exact False.elim h
  | twistedA n q =>
    match n, h with
    | 0, h => exact False.elim h
    | 1, h => exact False.elim h
    | 2, h => exact Or.inr h
    | n + 3, h => exact False.elim h
  | _ => exact False.elim h

theorem two_le_pRank_three_of_alternating {n : ℕ} (hn : 6 ≤ n) {L : Subgroup G}
    (e : ↥L ≃* alternatingGroup (Fin n)) : 2 ≤ CFSG.Open.pRank 3 L := by
  have hL : CFSG.Open.pRank 3 L = CFSG.pRank 3 ↥L :=
    (CFSG.SectionRank.pRank_coe_eq_openPRank 3 L).symm
  have he : CFSG.pRank 3 ↥L = CFSG.pRank 3 ↥(alternatingGroup (Fin n)) :=
    CFSG.pRank_congr_of_mulEquiv e 3
  have hA : CFSG.pRank 3 ↥(alternatingGroup (Fin n)) =
      CFSG.Open.pRank 3 (⊤ : Subgroup (alternatingGroup (Fin n))) :=
    CFSG.SectionRank.pRank_eq_open_pRank_top 3 ↥(alternatingGroup (Fin n))
  rw [hL, he, hA]
  exact CFSG.Quasithin.A3Facts.two_le_pRank_alternating hn

namespace P622KxCfg

theorem false_of_alt_three (c : P622KxCfg 3 P M x z T S L) {n : ℕ} (hn : 7 ≤ n)
    (e : Nonempty (↥L ≃* alternatingGroup (Fin n))) : False := by
  obtain ⟨e⟩ := e
  have h2 := two_le_pRank_three_of_alternating (by omega) e
  have h1 := c.rank
  omega

theorem false_of_j1_three (hKD : KFactJ1ClosureThree) (c : P622KxCfg 3 P M x z T S L)
    (e : Nonempty (↥L ≃* (TauCeti.CFSGIndex.sporadic .J1).Group)) : False := by
  have hLJ : L ≤ M ⊓ L := by
    refine hKD G L (M ⊓ L) z e c.z_mem c.orderOf_z
      (le_inf c.normalizer_zpowers_le inf_le_right) ?_
    intro U hUJ hUL hU1 hU2 hzU
    have hUM : U ≤ M := hUJ.trans inf_le_left
    have hne : U ⊓ M ≠ ⊥ := by rwa [inf_eq_left.mpr hUM]
    exact inf_le_inf_right L (c.normalizer_le hUL hU2 hzU hne)
  exact c.not_le (hLJ.trans inf_le_left)

theorem false_of_sporadic_three (hS3 : KFactSporThree) (hKD : KFactJ1ClosureThree)
    (c : P622KxCfg 3 P M x z T S L) {s : TauCeti.SporadicName}
    (e : Nonempty (↥L ≃* (TauCeti.CFSGIndex.sporadic s).Group)) : False := by
  have hs : s = .J1 := hS3 G L s c.isSimple.toNontrivial e c.rank
  subst hs
  exact c.false_of_j1_three hKD e

theorem false_of_lieOdd_three (hL62 : P622Lemma62Three) (hexit : P622L27Exit)
    (h1019 : KFact1019) (hKA : KFact2713Three) (hKB : KFactL3U3SL2Three)
    (hKE : KFactThreeRankTwo) (hbot : rankThreePrimeCore 3 (centralizer ({x} : Set G)) = ⊥)
    (c : P622KxCfg 3 P M x z T S L) (d : TauCeti.ValidLieTypeIndex)
    (hd2 : d.1.characteristic ≠ 2)
    (e : Nonempty (↥L ≃* (TauCeti.CFSGIndex.lie d).Group)) : False := by
  have hrk := c.rank
  by_cases hrk2 : d.1.characteristic = 3 ∨ IsReeIndex d.1 ∨ IsRankTwoOddIndex d.1
  · have h2 := hKE G L d e hrk2
    omega
  · push Not at hrk2
    obtain ⟨hf3, hree, hr2⟩ := hrk2
    set f : ℕ := d.1.characteristic with hf
    have hfp : f.Prime := TauCeti.LieTypeIndex.characteristic_prime d.1
    have hrank : ∀ U : Subgroup G, U ≤ L → U ≠ ⊥ → IsPGroup 2 U →
        CFSG.Open.pRank f (normalizer (U : Set G) ⊓ L) ≤ 3 := by
      intro U hUL hU1 hU2
      by_contra hlt
      push Not at hlt
      exact c.false_of_gen hfp hd2 ⟨U, hUL, hU1, hU2, hlt⟩
    have hlist := h1019 G L d hd2 e hrank
    rcases hlist with hdih | hree' | hr2'
    · rcases isDihedralTypeIndex_split hdih with hl2 | hl3
      ·
        have hmodel : catalogIs ↥L (onLie (fun i => IsLTwoIndex i ∧ i.characteristic ≠ 3)) :=
          ⟨TauCeti.CFSGIndex.lie d, ⟨hl2, hf3⟩, e⟩
        have hRM : ⁅zpowers z, S⁆ ≤ M := c.conf.R_le_S.trans c.S_le_M
        rcases hKA G L ⁅zpowers z, S⁆ z hmodel c.z_mem c.orderOf_z c.commutator_le
          c.conf.R_isPGroup (c.conf.z_le_normalizer_R (mem_zpowers z)) c.exists_not_commute with
          h168 | hgen
        · exact c.conf.failure.fails ⟨rfl, Or.inl (hexit G P M x z T S L c hbot h168)⟩
        · have hLJ : L ≤ M ⊓ L := hgen (M ⊓ L)
            (le_inf c.normalizer_zpowers_le inf_le_right) (le_inf hRM c.commutator_le)
          exact c.not_le (hLJ.trans inf_le_left)
      ·
        have hmodel : catalogIs ↥L
            (onLie (fun i => IsLThreeUThreeIndex i ∧ i.characteristic ≠ 3)) :=
          ⟨TauCeti.CFSGIndex.lie d, ⟨hl3, hf3⟩, e⟩
        obtain ⟨K₀, N, hK₀L, hzK₀, hzN, hs, hN1, hN2, hK₀C⟩ :=
          hKB G L z hmodel c.rank c.z_mem c.orderOf_z
        have hNK₀ : N ≤ K₀ := hs.1
        have hNL : N ≤ L := hNK₀.trans hK₀L
        have hzC : z ∈ centralizer (N : Set G) := hK₀C hzK₀
        have hzN' : z ∈ normalizer (N : Set G) := Subgroup.centralizer_le_normalizer _ hzC
        have hNC : N ≤ centralizer ({z} : Set G) := fun n hn =>
          mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hzC n hn)
        have hNM : N ≤ M := hNC.trans c.centralizer_z_le
        have hnorm : normalizer (N : Set G) ≤ M :=
          c.normalizer_le hNL hN2 hzN' (by rwa [inf_eq_left.mpr hNM])
        have hK₀M : K₀ ≤ M := fun k hk =>
          hnorm (Subgroup.centralizer_le_normalizer _ (hK₀C hk))
        exact c.false_of_section_three hL62 hK₀M hs hzK₀ hzN
    · exact hree hree'
    · exact hr2 hr2'

end P622KxCfg

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
