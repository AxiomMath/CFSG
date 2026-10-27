module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.FourteenFiveThreeKFacts
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.KFTwoLinTwo
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.KFTwoUnitary
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.KFTwoSz32
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.KFTwoLocal
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.KFTwoAltTen
import CFSG.GroupTheory.Fitting.PPrimeCoreGeneralizedFitting
import CFSG.Adapters.WholeGroupLayer
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.McLFiveLocal
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.TitsFiveLocal
import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.J4Eleven
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.JStarElimOrders
import CFSG.LargeExtraspecial.OutSixBasic

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.Open
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open scoped commutatorElement

private theorem false_of_solvable_and_pRank_three_le_one {X : Type} [Group X] [Finite X]
    {N : Subgroup X}
    (hsolv : Group.IsSolvable ↥N) (hr : CFSG.Open.pRank 3 ⁅N, N⁆ ≤ 1)
    (hdisj : ¬ Group.IsSolvable ↥N ∨ 2 ≤ CFSG.Open.pRank 3 ⁅N, N⁆) : False := by
  rcases hdisj with h | h
  · exact h hsolv
  · omega

private theorem false_of_abelian_generalizedFitting {X : Type} [Group X] [Finite X]
    {N : Subgroup X} (hF : IsSimpleGroup ↥(CFSG.generalizedFitting X))
    (hcomm : ∀ a b : ↥(CFSG.generalizedFitting X), a * b = b * a)
    (hdisj : ¬ Group.IsSolvable ↥N ∨ 2 ≤ CFSG.Open.pRank 3 ⁅N, N⁆) : False := by
  classical
  haveI hKn : (CFSG.generalizedFitting X).Normal :=
    (CFSG.LocalCores.generalized_fitting_characteristic (G := X)).2
  letI : CommGroup ↥(CFSG.generalizedFitting X) :=
    { (inferInstance : Group ↥(CFSG.generalizedFitting X)) with mul_comm := hcomm }
  have hpK : Nat.Prime (Nat.card ↥(CFSG.generalizedFitting X)) := IsSimpleGroup.prime_card
  letI : Fact (Nat.Prime (Nat.card ↥(CFSG.generalizedFitting X))) := ⟨hpK⟩
  haveI hKcyc : IsCyclic ↥(CFSG.generalizedFitting X) := isCyclic_of_prime_card rfl
  have hC : Subgroup.centralizer ((CFSG.generalizedFitting X : Subgroup X) : Set X) =
      CFSG.generalizedFitting X := by
    refine le_antisymm (CFSG.centralizer_generalizedFitting_le X) ?_
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (hcomm ⟨y, hy⟩ ⟨k, hk⟩)
  have hcommAut : IsMulCommutative (MulAut ↥(CFSG.generalizedFitting X)) := ⟨⟨fun α β =>
    (IsCyclic.mulAutMulEquiv ↥(CFSG.generalizedFitting X)).injective
      (by rw [map_mul, map_mul, mul_comm])⟩⟩
  have hXX : commutator X ≤ CFSG.generalizedFitting X := by
    refine (Abelianization.commutator_subset_ker
      (MulAut.conjNormal (H := CFSG.generalizedFitting X))).trans ?_
    intro g hg
    rw [← hC]
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h := congrArg
      (fun φ : MulAut ↥(CFSG.generalizedFitting X) =>
        ((φ ⟨x, hx⟩ : ↥(CFSG.generalizedFitting X)) : X))
      (MonoidHom.mem_ker.mp hg)
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h
    calc x * g = g * x * g⁻¹ * g := by rw [h]
      _ = g * x := by group
  haveI : IsMulCommutative (X ⧸ CFSG.generalizedFitting X) :=
    (Subgroup.Normal.quotient_commutative_iff_commutator_le).mpr hXX
  have hXsolv : Group.IsSolvable X :=
    Group.isSolvable_of_subgroup_quotient (CFSG.generalizedFitting X)
  haveI : Group.IsSolvable X := hXsolv
  have hNsolv : Group.IsSolvable ↥N := inferInstance
  have hNN : ⁅N, N⁆ ≤ CFSG.generalizedFitting X :=
    (Subgroup.commutator_mono le_top le_top).trans hXX
  have hr : CFSG.Open.pRank 3 ⁅N, N⁆ ≤ 1 :=
    (CFSG.SectionRank.pRank_mono (by norm_num : 1 < 3) hNN).trans
      (CFSG.SectionRank.pRank_le_one_of_isCyclic Nat.prime_three hKcyc)
  exact false_of_solvable_and_pRank_three_le_one hNsolv hr hdisj

private theorem pPrimeCore_eq_bot_of_psl2GF {p n : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) (hn : 1 ≤ n)
    {X : Type} [Group X] [Finite X] {N : Subgroup X}
    (hF : IsSimpleGroup ↥(CFSG.generalizedFitting X))
    (hN : CFSG.RankThree.PartOne.IsStronglyPEmbedded p N)
    (hdisj : ¬ Group.IsSolvable ↥N ∨ 2 ≤ CFSG.Open.pRank 3 ⁅N, N⁆)
    (e : ↥(CFSG.generalizedFitting X) ≃* CFSG.AGLEmbedding.PSL2GF p n) :
    CFSG.pPrimeCore 3 ↥N = ⊥ := by
  have hpK : p ∣ Nat.card ↥(CFSG.generalizedFitting X) := by
    obtain ⟨T⟩ := Sylow.nonempty (p := p) (G := CFSG.AGLEmbedding.PSL2GF p n)
    have hT := Subgroup.card_subgroup_dvd_card (T : Subgroup (CFSG.AGLEmbedding.PSL2GF p n))
    rw [(CFSG.AGLEmbedding.psl2GF_sylow p n hn T).2] at hT
    rw [Nat.card_congr e.toEquiv]
    exact (dvd_pow_self p (by omega)).trans hT
  obtain ⟨hsolv, hr⟩ := KFTwo.isSolvable_and_pRank_three_le_one_of_psl2GF hp5 hn
    (CFSG.pPrimeCore_eq_bot_of_isSimpleGroup_generalizedFitting hF hpK) hN e
  exact (false_of_solvable_and_pRank_three_le_one hsolv hr hdisj).elim

private theorem pPrimeCore_eq_bot_of_unitary {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    {d : TauCeti.ValidLieTypeIndex} (hd : CFSG.AGLEmbedding.IsUnitaryIndex p d)
    {X : Type} [Group X] [Finite X] {N : Subgroup X}
    (hF : IsSimpleGroup ↥(CFSG.generalizedFitting X))
    (hN : CFSG.RankThree.PartOne.IsStronglyPEmbedded p N)
    (hdisj : ¬ Group.IsSolvable ↥N ∨ 2 ≤ CFSG.Open.pRank 3 ⁅N, N⁆)
    (e : ↥(CFSG.generalizedFitting X) ≃* CFSG.AGLEmbedding.CatGroup d) :
    CFSG.pPrimeCore 3 ↥N = ⊥ := by
  have hpK : p ∣ Nat.card ↥(CFSG.generalizedFitting X) := by
    have hfe : 0 < d.1.fieldExponent := TauCeti.ValidLieTypeIndex.fieldExponent_pos d
    rw [Nat.card_congr e.toEquiv]
    exact (dvd_pow_self p (by omega : 3 * d.1.fieldExponent ≠ 0)).trans
      (CFSG.AGLEmbedding.pow_dvd_card_catGroup_unitary hd)
  obtain ⟨hsolv, hr⟩ := KFTwo.isSolvable_and_pRank_three_le_one_of_unitary hp5 hd
    (CFSG.pPrimeCore_eq_bot_of_isSimpleGroup_generalizedFitting hF hpK) hN e
  exact (false_of_solvable_and_pRank_three_le_one hsolv hr hdisj).elim

private theorem pPrimeCore_eq_bot_of_sz32
    {d : TauCeti.ValidLieTypeIndex} (hd : d.1 = .suzuki 2)
    {X : Type} [Group X] [Finite X] {N : Subgroup X}
    (hF : IsSimpleGroup ↥(CFSG.generalizedFitting X))
    (hN : CFSG.RankThree.PartOne.IsStronglyPEmbedded 5 N)
    (hdisj : ¬ Group.IsSolvable ↥N ∨ 2 ≤ CFSG.Open.pRank 3 ⁅N, N⁆)
    (e : ↥(CFSG.generalizedFitting X) ≃* CFSG.AGLEmbedding.CatGroup d) :
    CFSG.pPrimeCore 3 ↥N = ⊥ := by
  have hpK : 5 ∣ Nat.card ↥(CFSG.generalizedFitting X) := by
    have hcard : Nat.card ↥(CFSG.generalizedFitting X) = 32537600 := by
      obtain ⟨d₀, hv⟩ := d
      obtain rfl : d₀ = .suzuki 2 := hd
      exact (CFSG.RankThree.PartOne.K159.SzAbs.szSylow_of_isoLie
        (S := ↥(CFSG.generalizedFitting X)) ⟨hv, ⟨e⟩⟩).card
    rw [hcard]
    norm_num
  obtain ⟨hsolv, hr⟩ := KFTwo.isSolvable_and_pRank_three_le_one_of_sz32 hd
    (CFSG.pPrimeCore_eq_bot_of_isSimpleGroup_generalizedFitting hF hpK) hN e
  exact (false_of_solvable_and_pRank_three_le_one hsolv hr hdisj).elim

private theorem pPrimeCore_eq_bot_of_altTen {X : Type} [Group X] [Finite X] {N : Subgroup X}
    (hF : IsSimpleGroup ↥(CFSG.generalizedFitting X))
    (hN : CFSG.RankThree.PartOne.IsStronglyPEmbedded 5 N)
    (e : ↥(CFSG.generalizedFitting X) ≃* ↥(alternatingGroup (Fin 10))) :
    CFSG.pPrimeCore 3 ↥N = ⊥ := by
  have hpK : 5 ∣ Nat.card ↥(CFSG.generalizedFitting X) := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
    norm_num
  exact KFTwo.pPrimeCore_three_eq_bot_of_altTen
    (CFSG.pPrimeCore_eq_bot_of_isSimpleGroup_generalizedFitting hF hpK) hN e

private theorem pPrimeCore_eq_bot_of_d2HeisLocalAt
    {i : TauCeti.CFSGIndex} {p : ℕ} [Fact p.Prime] (hp : p = 5 ∨ p = 11)
    (H : CFSG.AGLEmbeddingD2.D2HeisLocalAt i fun q => q = p)
    {X : Type} [Group X] [Finite X] {N : Subgroup X}
    (hF : IsSimpleGroup ↥(CFSG.generalizedFitting X))
    (hN : CFSG.RankThree.PartOne.IsStronglyPEmbedded p N)
    (hdisj : ¬ Group.IsSolvable ↥N ∨ 2 ≤ CFSG.Open.pRank 3 ⁅N, N⁆)
    (e : ↥(CFSG.generalizedFitting X) ≃* i.Group) :
    CFSG.pPrimeCore 3 ↥N = ⊥ := by
  classical
  haveI hKn : (CFSG.generalizedFitting X).Normal :=
    (CFSG.LocalCores.generalized_fitting_characteristic (G := X)).2
  by_cases hnab : ∃ a b : ↥(CFSG.generalizedFitting X), a * b ≠ b * a
  · have hKC : Subgroup.centralizer ((CFSG.generalizedFitting X : Subgroup X) : Set X) = ⊥ :=
      CFSG.Adapters.centralizer_generalizedFitting_eq_bot_of_isSimpleGroup X hF hnab
    obtain ⟨R⟩ := Sylow.nonempty (p := p) (G := X)
    obtain ⟨hout, hcard, -⟩ := H X (CFSG.generalizedFitting X) hKn hKC ⟨e⟩ p rfl R
    have hdvdIdx : (CFSG.generalizedFitting X).index ∣
        Nat.card (Outer ↥(CFSG.generalizedFitting X)) :=
      CFSG.LargeExtraspecial.S14.index_dvd_card_outer (CFSG.generalizedFitting X)
        (by rw [hKC]; exact bot_le)
    have hnotIdx : ¬ p ∣ (CFSG.generalizedFitting X).index :=
      fun h => hout (h.trans hdvdIdx)
    have hpX : p ∣ Nat.card X := by
      have hR : p ∣ Nat.card (R : Subgroup X) := by
        rw [hcard]
        exact dvd_pow_self p (by norm_num)
      exact hR.trans (Subgroup.card_subgroup_dvd_card (R : Subgroup X))
    have hpK : p ∣ Nat.card ↥(CFSG.generalizedFitting X) := by
      have hpdvd : p ∣ Nat.card ↥(CFSG.generalizedFitting X) *
          (CFSG.generalizedFitting X).index := by
        rw [Subgroup.card_mul_index]
        exact hpX
      exact Nat.Coprime.dvd_of_dvd_mul_right
        ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr hnotIdx) hpdvd
    have hO := CFSG.pPrimeCore_eq_bot_of_isSimpleGroup_generalizedFitting hF hpK
    obtain ⟨hsolv, hr⟩ :=
      KFTwo.isSolvable_and_pRank_three_le_one_of_d2HeisLocalAt hp H hO hN e
    exact (false_of_solvable_and_pRank_three_le_one hsolv hr hdisj).elim
  · have hcomm : ∀ a b : ↥(CFSG.generalizedFitting X), a * b = b * a := by
      intro a b
      by_contra h
      exact hnab ⟨a, b, h⟩
    exact (false_of_abelian_generalizedFitting hF hcomm hdisj).elim

private theorem pPrimeCore_eq_bot_of_d2TorusLocalAt {i : TauCeti.CFSGIndex}
    (H : CFSG.AGLEmbeddingD2.D2TorusLocalAt i fun q => q = 5)
    {X : Type} [Group X] [Finite X] {N : Subgroup X}
    (hF : IsSimpleGroup ↥(CFSG.generalizedFitting X))
    (hN : CFSG.RankThree.PartOne.IsStronglyPEmbedded 5 N)
    (hdisj : ¬ Group.IsSolvable ↥N ∨ 2 ≤ CFSG.Open.pRank 3 ⁅N, N⁆)
    (e : ↥(CFSG.generalizedFitting X) ≃* i.Group) :
    CFSG.pPrimeCore 3 ↥N = ⊥ := by
  classical
  haveI hKn : (CFSG.generalizedFitting X).Normal :=
    (CFSG.LocalCores.generalized_fitting_characteristic (G := X)).2
  by_cases hnab : ∃ a b : ↥(CFSG.generalizedFitting X), a * b ≠ b * a
  · have hKC : Subgroup.centralizer ((CFSG.generalizedFitting X : Subgroup X) : Set X) = ⊥ :=
      CFSG.Adapters.centralizer_generalizedFitting_eq_bot_of_isSimpleGroup X hF hnab
    obtain ⟨R⟩ := Sylow.nonempty (p := 5) (G := X)
    obtain ⟨hout, hcard, -⟩ := H X (CFSG.generalizedFitting X) hKn hKC ⟨e⟩ 5 rfl R
    have hdvdIdx : (CFSG.generalizedFitting X).index ∣
        Nat.card (Outer ↥(CFSG.generalizedFitting X)) :=
      CFSG.LargeExtraspecial.S14.index_dvd_card_outer (CFSG.generalizedFitting X)
        (by rw [hKC]; exact bot_le)
    have hnotIdx : ¬ 5 ∣ (CFSG.generalizedFitting X).index :=
      fun h => hout (h.trans hdvdIdx)
    have hpX : 5 ∣ Nat.card X := by
      have hR : 5 ∣ Nat.card (R : Subgroup X) := by
        rw [hcard]
        exact dvd_pow_self 5 (by norm_num)
      exact hR.trans (Subgroup.card_subgroup_dvd_card (R : Subgroup X))
    have hpK : 5 ∣ Nat.card ↥(CFSG.generalizedFitting X) := by
      have hpdvd : 5 ∣ Nat.card ↥(CFSG.generalizedFitting X) *
          (CFSG.generalizedFitting X).index := by
        rw [Subgroup.card_mul_index]
        exact hpX
      exact Nat.Coprime.dvd_of_dvd_mul_right
        ((Fact.out : Nat.Prime 5).coprime_iff_not_dvd.mpr hnotIdx) hpdvd
    have hO := CFSG.pPrimeCore_eq_bot_of_isSimpleGroup_generalizedFitting hF hpK
    obtain ⟨hsolv, hr⟩ :=
      KFTwo.isSolvable_and_pRank_three_le_one_of_d2TorusLocalAt H hO hN e
    exact (false_of_solvable_and_pRank_three_le_one hsolv hr hdisj).elim
  · have hcomm : ∀ a b : ↥(CFSG.generalizedFitting X), a * b = b * a := by
      intro a b
      by_contra h
      exact hnab ⟨a, b, h⟩
    exact (false_of_abelian_generalizedFitting hF hcomm hdisj).elim

theorem kFactNineFourStronglyEmbedded_holds :
    KFactNineFourStronglyEmbedded := by
  intro p hp h5 X _ _ hlist N hN hdisj
  obtain ⟨hF, i, hi, ⟨e⟩⟩ := hlist
  haveI : Fact p.Prime := ⟨hp⟩
  cases i with
  | cyclic _ _ => exact hi.elim
  | alternating n _ =>
    rcases hi with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · omega
    · haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
      exact pPrimeCore_eq_bot_of_altTen hF hN e
  | sporadic s =>
    rcases hi with ⟨rfl, -⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · omega
    · haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
      exact pPrimeCore_eq_bot_of_d2HeisLocalAt (i := .sporadic .McL) (p := 5) (Or.inl rfl)
        CFSG.AGLEmbeddingD2.d2HeisLocalAt_mcl hF hN hdisj e
    · haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
      exact pPrimeCore_eq_bot_of_d2HeisLocalAt (i := .sporadic .J4) (p := 11) (Or.inr rfl)
        CFSG.AGLEmbeddingD2.Wilson.Coordinator.d2HeisLocalAt_J4 hF hN hdisj e
  | lie d =>
    rcases hi with ⟨q, hqp, h2, hd⟩ | ⟨q, hqp, hd⟩ | ⟨rfl, m, hm⟩ |
      ⟨rfl, ⟨q, hq2, hq3, hd⟩ | ⟨q, hq2, hq2', hd⟩⟩ | ⟨rfl, hd | hd⟩
    · obtain ⟨e2⟩ := CFSG.AGLEmbedding.nonempty_mulEquiv_psl2GF_of_isLinTwoIndex
        (p := p) (n := q.exponent) (d := d) ⟨q, hd, hqp, rfl⟩
      exact pPrimeCore_eq_bot_of_psl2GF h5 (by omega) hF hN hdisj (e.trans e2)
    · exact pPrimeCore_eq_bot_of_unitary h5 ⟨q, hqp, hd⟩ hF hN hdisj e
    · omega
    · omega
    · omega
    · obtain ⟨d1, hv⟩ := d
      change d1 = .suzuki 2 at hd
      subst d1
      haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
      exact pPrimeCore_eq_bot_of_sz32 rfl hF hN hdisj e
    · obtain ⟨d1, hv⟩ := d
      change d1 = .tits at hd
      subst d1
      haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
      exact pPrimeCore_eq_bot_of_d2TorusLocalAt
        (CFSG.AGLEmbeddingD2.d2TorusLocalAt_tits ⟨.tits, hv⟩ rfl) hF hN hdisj e

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
