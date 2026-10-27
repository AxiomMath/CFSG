module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointRankFour
import CFSG.LocalAnalysis.RankFourTheoremC.Equivalence
import CFSG.LocalAnalysis.RankThreeTheoremC.ObstructionElements
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.RelativePairGeometry
import CFSG.RankThree.PartTwo.Sec21.Item23Tools
public import CFSG.LocalAnalysis.RankFourTheoremC.Refined

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.RankThreeCoreUniqueness.Helpers
  CFSG.LocalAnalysis.RankThreeTheoremC Subgroup

variable {G : Type} [Group G] [Finite G]

@[expose] def IsPElement (p : ℕ) (M : Subgroup G) (x : G) : Prop :=
  x ∈ M ∧ orderOf x = p ∧ 3 ≤ Open.pRank p (M ⊓ centralizer ({x} : Set G)) ∧
    ¬ centralizer ({x} : Set G) ≤ M

@[expose] def PElementPrimeFive (G : Type) [Group G] [Finite G] : Prop :=
  D1Global G → D1For G → FullCoreLocality G → ∀ (p : ℕ) (P : Sylow p G) (M : Subgroup G),
    D1Local p P M → ∀ x : G, IsPElement p M x → 5 ≤ p

theorem normalizer_le_of_two_le_pRank (hFC : FullCoreLocality G) {p : ℕ} {P : Sylow p G}
    {M : Subgroup G} (hloc : D1Local p P M) {S : Subgroup G} (hSp : IsPGroup p S) (hSM : S ≤ M)
    (hS2 : 2 ≤ Open.pRank p S) : normalizer (S : Set G) ≤ M := by
  have hprime := hloc.beta.1
  obtain ⟨m, hm⟩ := pGroup_conjugate_into_sylow_within_overgroup p hprime P M
    (sylow_le_of_core hloc) S hSp hSM
  have hN : normalizer ((S.map (MulAut.conj (m : G)).toMonoidHom : Subgroup G) : Set G) ≤ M :=
    (gamma_normalizer_le 2 p (P : Subgroup G) _ hm
      (by rwa [pRank_map_automorphism p hprime.one_lt])).trans (hFC p P M hloc)
  have hmap : (normalizer (S : Set G)).map (MulAut.conj (m : G)).toMonoidHom ≤ M := by
    rw [Subgroup.map_equiv_normalizer_eq]
    exact hN
  exact (conjugate_subgroup_le_iff_of_conjugator_mem _ M (m : G) m.2).1 hmap

theorem normalizer_zpowers_le_of_centralizer_le (hFC : FullCoreLocality G) {p : ℕ}
    {P : Sylow p G} {M : Subgroup G} (hloc : D1Local p P M) {x : G}
    (hCM : centralizer ({x} : Set G) ≤ M)
    (hC2 : 2 ≤ Open.pRank p ((P : Subgroup G) ⊓ centralizer ({x} : Set G))) :
    normalizer ((zpowers x : Subgroup G) : Set G) ≤ M := by
  have hprime := hloc.beta.1
  have : Fact p.Prime := ⟨hprime⟩
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  have hPCp : IsPGroup p ((P ⊓ C : Subgroup G).subgroupOf C) :=
    (P.isPGroup'.to_le (inf_le_left : (P : Subgroup G) ⊓ C ≤ P)).comap_subtype
  obtain ⟨Q, hQ⟩ := hPCp.exists_le_sylow
  set S : Subgroup G := (Q : Subgroup C).map C.subtype with hS
  have hSyl : CFSG.ABGLocalTools.IsSylowOf p S C := ⟨Q, rfl⟩
  have hPCS : (P : Subgroup G) ⊓ C ≤ S := by
    intro g hg
    exact ⟨⟨g, hg.2⟩, hQ (mem_subgroupOf.2 hg), rfl⟩
  have hSM : S ≤ M := hSyl.le.trans hCM
  have hS2 : 2 ≤ Open.pRank p S :=
    hC2.trans (CFSG.PreuniquenessRankFour.Helpers.pRank_mono p hprime hPCS)
  have hNS : normalizer (S : Set G) ≤ M :=
    normalizer_le_of_two_le_pRank hFC hloc hSyl.isPGroup hSM hS2
  have hCeq : centralizer ((zpowers x : Subgroup G) : Set G) = C := by
    rw [zpowers_eq_closure, centralizer_closure]
  have hnC : normalizer ((zpowers x : Subgroup G) : Set G) ≤ normalizer (C : Set G) := by
    have := normalizer_le_normalizer_centralizer (zpowers x : Subgroup G)
    rwa [hCeq] at this
  exact (le_sup_normalizer_of_isSylowOf hnC hSyl).trans (sup_le hCM hNS)

theorem stronglyEmbedded_three_of_pElement (hS : D1Global G) (hD1 : D1For G)
    (hFC : FullCoreLocality G) (hP5 : PElementPrimeFive G) (h313 : GL83NormalElementaryRankFour)
    {P : Sylow 3 G}
    {M : Subgroup G} (hloc : D1Local 3 P M) : GLBStronglyEmbedded 3 M := by
  have hprime : (3 : ℕ).Prime := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hprime⟩
  have hPM : (P : Subgroup G) ≤ M := sylow_le_of_core hloc
  have hP4 := four_le_pRank_sylow hloc.beta P
  have hkey : ∀ x ∈ (P : Subgroup G), x ≠ 1 → x ^ 3 = 1 →
      normalizer ((zpowers x : Subgroup G) : Set G) ≤ M := by
    intro x hxP hx1 hx3
    have hC3 := three_le_pRank_inf_centralizer h313 P.isPGroup' hP4 hxP hx3
    have hCM : centralizer ({x} : Set G) ≤ M := by
      by_contra hCM
      have h5 := hP5 hS hD1 hFC 3 P M hloc x ⟨hPM hxP, orderOf_eq_prime hx3 hx1,
        hC3.trans (CFSG.PreuniquenessRankFour.Helpers.pRank_mono 3 hprime
          (inf_le_inf_right _ hPM)), hCM⟩
      omega
    exact normalizer_zpowers_le_of_centralizer_le hFC hloc hCM (by omega)
  have hP : ∀ X : Subgroup G, X ≤ P → IsPGroup 3 X → X ≠ ⊥ →
      normalizer (X : Set G) ≤ M := by
    intro X hXP hXp hX1
    by_cases h2 : 2 ≤ Open.pRank 3 X
    · exact normalizer_le_of_two_le_pRank hFC hloc hXp (hXP.trans hPM) h2
    · have hcyc : IsCyclic X := by
        by_contra hnc
        exact h2 (two_le_pRank_of_not_isCyclic hprime (by norm_num) hXp hnc)
      obtain ⟨n, hn⟩ := hXp.exists_card_eq
      have hn0 : n ≠ 0 := by
        rintro rfl
        exact hX1 ((Subgroup.card_eq_one).1 (by simpa using hn))
      obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := X) 3 (by
        rw [hn]; exact dvd_pow_self 3 hn0)
      have h1 : 1 ≤ Open.pRank 3 X := by
        have hy3 : (y : G) ^ 3 = 1 := by
          have := pow_orderOf_eq_one y
          rw [hy] at this
          simpa using congrArg Subtype.val this
        have hy1 : (y : G) ≠ 1 := fun h => by
          have : y = 1 := Subtype.ext h
          rw [this, orderOf_one] at hy
          omega
        refine le_pRank_of_isElemAbelian hprime (Y := zpowers (y : G)) ?_ ?_ (k := 1) ?_
        · exact zpowers_le.2 y.2
        · exact (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 _).1
            (CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one hy3)
        · rw [Nat.card_zpowers, orderOf_eq_prime hy3 hy1]
          simp
      obtain ⟨x, hxX, hx1, hx3, hNX⟩ :=
        exists_pow_eq_one_normalizer_le_of_isCyclic hprime hXp hcyc h1
      exact hNX.trans (hkey x (hXP hxX) hx1 hx3)
  have hcard : 3 ∣ Nat.card M :=
    (dvd_card_of_one_le_pRank hprime (by omega : 1 ≤ Open.pRank 3 (P : Subgroup G))).trans
      (Subgroup.card_dvd_of_le hPM)
  have := hS.simple
  refine CFSG.RankThree.PartTwo.Sec21.glbStronglyEmbedded_of_normalizer_le
    (CFSG.PreuniquenessRankFour.Helpers.twoLocal_ne_top hS.nonab hloc.maxLocal.1) hcard ?_
  intro X hXM hXp hX1
  obtain ⟨m, hm⟩ := pGroup_conjugate_into_sylow_within_overgroup 3 hprime P M hPM X hXp hXM
  have hXm : X.map (MulAut.conj (m : G)).toMonoidHom ≠ ⊥ := fun h =>
    hX1 ((map_eq_bot_iff_of_injective (f := (MulAut.conj (m : G)).toMonoidHom) X
      (MulAut.conj (m : G)).injective).mp h)
  have hN := hP _ hm (hXp.map _) hXm
  have hmap : (normalizer (X : Set G)).map (MulAut.conj (m : G)).toMonoidHom ≤ M := by
    rw [Subgroup.map_equiv_normalizer_eq]
    exact hN
  exact (conjugate_subgroup_le_iff_of_conjugator_mem _ M (m : G) m.2).1 hmap

theorem deltaTwo_of_pElement (hS : D1Global G) (hD1 : D1For G) (hFC : FullCoreLocality G)
    (hP5 : PElementPrimeFive G) (h313 : GL83NormalElementaryRankFour) : GLBDeltaTwo G := by
  intro h3 P M hM hPM
  have hP4 := four_le_pRank_sylow h3 P
  have hW : GLBWeakCore 3 (P : Subgroup G) ≤ M :=
    weakCore_le_of_large_subgroup hS.pre hD1 h3 P (by omega) hM le_rfl hPM (by omega)
  exact Or.inl (stronglyEmbedded_three_of_pElement hS hD1 hFC hP5 h313 ⟨h3, hM, hW⟩)

theorem deltaTwoRank4_of_pElement (hD1 : D1Rank4) (hFC : FullCoreRank4)
    (hP5 : ∀ (G : Type) [Group G] [Finite G], PElementPrimeFive G)
    (h313 : GL83NormalElementaryRankFour) : DeltaTwoRank4 := by
  intro G _ _ _ hnonab hK hchar he hpre
  exact deltaTwo_of_pElement ⟨inferInstance, hnonab, hK, hchar, he, hpre⟩
    (hD1 G hnonab hK hchar he hpre) (hFC G hnonab hK hchar he hpre) (hP5 G) h313

end CFSG.LocalAnalysis.RankFourTheoremC
