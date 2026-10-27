module

public import CFSG.FeitThompson.Local.MixedFittingCentralizerPrimeSupport
public import CFSG.FeitThompson.Definitions.UniqueMaximalOvergroup
import CFSG.FeitThompson.Local.MixedFittingLargeAbelianUniqueness
import CFSG.FeitThompson.Local.HighRankFittingControlsSylow
import CFSG.FeitThompson.Local.UniquenessTransferCentralizerRankTwo
import CFSG.FeitThompson.Local.HighRankAbelianUniquenessCentralizers
import CFSG.FeitThompson.Local.RankThreeNormalAbelianSelfCentralizing
import CFSG.FeitThompson.Local.PrimeFittingNormalSelfCentralizingAbelian
import CFSG.FeitThompson.Local.HighFittingRankUniqueOvergroupWitness
import CFSG.FeitThompson.Local.SecondCenterPlaneCharacteristicCentralizer
import CFSG.FeitThompson.OddOrder.RankTwoKernelSmallerComplementPrimes
import CFSG.FeitThompson.Definitions.AlphaPrimesOfAFiniteGroup

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Pointwise Subgroup

variable {G : Type*} [Group G] [Finite G] {p : ℕ} {M A : Subgroup G}

theorem exists_abelian_isUniqueMaximalOvergroup_of_three_le_elementaryAbelianPRank_mixedFitting
    [IsSimpleGroup G] (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ X : Subgroup G, X ≠ ⊤ → Group.IsSolvable ↥X)
    (hM : IsCoatom M) (hp : p.Prime)
    (hFrank : 3 ≤ elementaryAbelianPRank p ↥(mixedFitting M)) :
    ∃ E : Subgroup G, IsMulCommutative ↥E ∧ IsPGroup p ↥E ∧
      3 ≤ elementaryAbelianPRank p ↥E ∧ IsUniqueMaximalOvergroup E M := by
  have hMsolv : Group.IsSolvable ↥M := hsolv M hM.1
  have hfp := Fact.mk hp
  have hpodd : Odd p := hodd.of_dvd_nat
    (((one_le_elementaryAbelianPRank_iff hp).1 (le_trans (by norm_num) hFrank)).trans
      (Subgroup.card_subgroup_dvd_card _))
  by_cases hFp : IsPGroup p ↥(mixedFitting M)
  ·
    obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow p ↥M))
    set P : Subgroup G := (S : Subgroup ↥M).map M.subtype with hPdef
    have hPM : P ≤ M := Subgroup.map_subtype_le _
    have hPcard : Nat.card ↥P = p ^ (Nat.card ↥M).factorization p := by
      rw [hPdef, ← Nat.card_congr
        ((S : Subgroup ↥M).equivMapOfInjective M.subtype M.subtype_injective).toEquiv]
      exact S.card_eq_multiplicity
    have hFP : mixedFitting M ≤ P := mixedFitting_le_map_sylow hp hFp S
    have hPrank : 3 ≤ elementaryAbelianPRank p ↥P :=
      hFrank.trans (elementaryAbelianPRank_le_of_le hp.one_lt hFP)
    have hPpg : IsPGroup p ↥P := IsPGroup.of_card hPcard
    obtain ⟨A₀, hA₀n, hA₀c, hA₀rank, hA₀cent⟩ :=
      exists_abelian_normal_centralizer_eq_of_three_le_elementaryAbelianPRank_of_isPGroup
        hp hpodd hPpg hPrank
    set E : Subgroup G := A₀.map P.subtype with hEdef
    have hEP : E ≤ P := Subgroup.map_subtype_le _
    have hEsub : E.subgroupOf P = A₀ :=
      Subgroup.comap_map_eq_self_of_injective P.subtype_injective A₀
    have hEcomm : IsMulCommutative ↥E := by
      have := hA₀c
      rw [hEdef]
      infer_instance
    have hErank : 3 ≤ elementaryAbelianPRank p ↥E := by
      rw [hEdef, ← elementaryAbelianPRank_eq_of_mulEquiv hp.one_lt
        (A₀.equivMapOfInjective P.subtype P.subtype_injective)]
      exact hA₀rank
    have hECP : P ⊓ centralizer (E : Set G) = E :=
      (centralizer_subgroupOf_eq_iff hEP).1 (by rw [hEsub]; exact hA₀cent)
    exact ⟨E, hEcomm, hPpg.to_le hEP, hErank,
      isUniqueMaximalOvergroup_of_isPGroup_mixedFitting_of_rank_three hna hodd hsolv hM hp hFp
        hFrank hPM hPcard hEP (hEsub ▸ hA₀n) hEcomm hECP hErank⟩
  ·
    obtain ⟨E, hEF, hcomm, hexp, hEcard⟩ :=
      (mem_elementaryAbelianRanks_subgroup_iff (H := mixedFitting M) (d := 3) hp).1
        ((le_elementaryAbelianPRank_iff hp.one_lt).1 hFrank)
    have hEea : IsElementaryAbelian p E := isElementaryAbelian_iff.2
      ⟨IsMulCommutative.of_comm fun a b => Subtype.ext (hcomm a a.2 b b.2), hexp⟩
    have hEcomm : IsMulCommutative ↥E := hEea.isMulCommutative
    have hErank : 3 ≤ elementaryAbelianPRank p ↥E :=
      hEea.le_elementaryAbelianPRank hp hEcard le_rfl
    have hTM : IsUniqueMaximalOvergroup (mixedFittingCentralizer M E) M :=
      isUniqueMaximalOvergroup_mixedFittingCentralizer hna hodd hsolv hM hp hEea hEF hErank hFp
    have hET : E ≤ mixedFittingCentralizer M E := by
      rw [mixedFittingCentralizer_eq]
      exact le_inf hEF (Subgroup.le_centralizer E)
    have hEne : E ≠ ⊥ := by
      intro h
      rw [h, Subgroup.card_bot] at hEcard
      exact absurd hEcard.symm (Nat.one_lt_pow three_ne_zero hp.one_lt).ne'
    exact ⟨E, hEcomm, hEea.isPGroup, hErank,
      isUniqueMaximalOvergroup_of_le_centralizer hp hna hodd hsolv
        (lt_of_lt_of_le (bot_lt_iff_ne_bot.2 hEne) hET) hTM
        (Subgroup.le_centralizer_iff.1 (mixedFittingCentralizer_le_centralizer M E))
        (le_trans (by norm_num) hErank)⟩

theorem isUniqueMaximalOvergroup_conj_smul_of_three_le_elementaryAbelianPRank_mixedFitting
    [IsSimpleGroup G] (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ X : Subgroup G, X ≠ ⊤ → Group.IsSolvable ↥X)
    (hM : IsCoatom M) (hp : p.Prime)
    (hFrank : 3 ≤ elementaryAbelianPRank p ↥(mixedFitting M))
    (hAcomm : IsMulCommutative ↥A) (hApg : IsPGroup p ↥A)
    (hArank : 3 ≤ elementaryAbelianPRank p ↥A) :
    ∃ g : G, IsUniqueMaximalOvergroup A (MulAut.conj g • M) := by
  obtain ⟨E, hEcomm, hEpg, hErank, hEM⟩ :=
    exists_abelian_isUniqueMaximalOvergroup_of_three_le_elementaryAbelianPRank_mixedFitting
      hna hodd hsolv hM hp hFrank
  have hAnc : ¬ IsCyclic ↥A := not_isCyclic_of_three_le_elementaryAbelianPRank hp hArank
  have hAcent : 3 ≤ elementaryAbelianPRank p ↥(centralizer (A : Set G)) :=
    hArank.trans (elementaryAbelianPRank_le_of_le hp.one_lt (Subgroup.le_centralizer A))
  exact isUniqueMaximalOvergroup_conj_smul_of_three_le_elementaryAbelianPRank_centralizer hp hna
    hodd hsolv hEpg hErank hEM hApg hAnc hAcent

theorem exists_isUniqueMaximalOvergroup_of_three_le_elementaryAbelianPRank_mixedFitting
    [IsSimpleGroup G] (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ X : Subgroup G, X ≠ ⊤ → Group.IsSolvable ↥X)
    (hM : IsCoatom M) (hp : p.Prime)
    (hFrank : 3 ≤ elementaryAbelianPRank p ↥(mixedFitting M))
    (hAcomm : IsMulCommutative ↥A) (hApg : IsPGroup p ↥A)
    (hArank : 3 ≤ elementaryAbelianPRank p ↥A) :
    ∃ N : Subgroup G, IsUniqueMaximalOvergroup A N :=
  let ⟨_, hg⟩ := isUniqueMaximalOvergroup_conj_smul_of_three_le_elementaryAbelianPRank_mixedFitting
    hna hodd hsolv hM hp hFrank hAcomm hApg hArank
  ⟨_, hg⟩

end

end CFSG.FeitThompson
