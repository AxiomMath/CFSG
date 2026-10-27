module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62wDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank65Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62yCommon
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank627WMain
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank65Main
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62zGlue
import CFSG.LocalAnalysis.RankThreeUC.TheoremDClauseCCore
public import CFSG.LieType.BorelTits.Basic
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62yDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

theorem sr62w_pCoreOf_le_fitting {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hq2 : q ≠ 2) (x : G) :
    pCoreOf q (smallRankD p x) ≤
      CFSG.fittingSubgroupOf (rankThreePrimeCore 2 (smallRankD p x)) := by
  have : Fact q.Prime := ⟨hq⟩
  have : Fact p.Prime := ⟨hp⟩
  have hAD : pCoreOf q (smallRankD p x) ≤ smallRankD p x :=
    CFSG.LieType.BorelTits.pCoreOf_le q (smallRankD p x)
  have hAOD : pCoreOf q (smallRankD p x) ≤ rankThreePrimeCore 2 (smallRankD p x) := by
    refine le_sSup ⟨hAD, ?_, ?_⟩
    · exact CFSG.RankThreeEvenClassification.Helpers.pCoreOf_normal_subgroupOf q
        (smallRankD p x) (smallRankD p x) le_rfl
        (by rw [Subgroup.subgroupOf_self]; infer_instance)
    · obtain ⟨n, hn⟩ :=
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup q (smallRankD p x)).exists_card_eq
      rw [hn]
      exact Nat.Coprime.pow_right n ((Nat.coprime_primes Nat.prime_two hq).mpr (Ne.symm hq2))
  have hDC : smallRankD p x ≤ centralizer ({x} : Set G) :=
    (CFSG.LocalAnalysis.RankThreeUC.rankThreePrimeCore_spec p (centralizer ({x} : Set G))).1
  have hODD : rankThreePrimeCore 2 (smallRankD p x) ≤ smallRankD p x :=
    (CFSG.LocalAnalysis.RankThreeUC.rankThreePrimeCore_spec 2 (smallRankD p x)).1
  have hCN : centralizer ({x} : Set G) ≤ normalizer (pCoreOf q (smallRankD p x) : Set G) :=
    (CFSG.LocalAnalysis.RankThreeUC.rankThreePrimeCore_spec p
      (centralizer ({x} : Set G))).2.1.trans
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf q (smallRankD p x))
  have hODN : rankThreePrimeCore 2 (smallRankD p x) ≤
      normalizer (pCoreOf q (smallRankD p x) : Set G) := (hODD.trans hDC).trans hCN
  have hnorm : ((pCoreOf q (smallRankD p x)).subgroupOf
      (rankThreePrimeCore 2 (smallRankD p x))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAOD).mpr hODN
  have : Group.IsNilpotent (pCoreOf q (smallRankD p x)) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup q (smallRankD p x)).isNilpotent
  have hnil : Group.IsNilpotent ((pCoreOf q (smallRankD p x)).subgroupOf
      (rankThreePrimeCore 2 (smallRankD p x))) :=
    Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hAOD).symm
  have hle : (pCoreOf q (smallRankD p x)).subgroupOf (rankThreePrimeCore 2 (smallRankD p x)) ≤
      CFSG.fittingSubgroup ↥(rankThreePrimeCore 2 (smallRankD p x)) :=
    le_sSup ⟨hnorm, hnil⟩
  have hmap := Subgroup.map_mono (f := (rankThreePrimeCore 2 (smallRankD p x)).subtype) hle
  rw [Subgroup.map_subgroupOf_eq_of_le hAOD] at hmap
  exact hmap

theorem sr62w_fitting_inf_eq_bot (hS : Setting G) (hU0 : FullCoreLocal G)
    (hK1 : KFactRankTwoUniqueness) (hK2 : KFactRankThreeStructure)
    {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x z : G} {T : Subgroup G}
    (hf : Prop627Failure G p P M x z T)
    (hfit : ¬ SmallRankNice p P M →
      CFSG.fittingSubgroupOf (rankThreePrimeCore 2 (smallRankD p x)) ⊓ M = ⊥) :
    CFSG.fittingSubgroupOf (rankThreePrimeCore 2 (smallRankD p x)) ⊓ M = ⊥ := by
  by_cases hn : SmallRankNice p P M
  · obtain ⟨rfl, hsolv, he⟩ := hn
    exact fitting_inf_eq_bot_of_prop65 ⟨hS, hU0, hf.situation, hsolv, he, hf.point, hf.central⟩
      (prop65_of_kfacts hS hU0 hK1 hK2)
  · exact hfit hn

theorem GL83SmallRankInterfaceW.toInterface (hS : Setting G) (hU0 : FullCoreLocal G)
    (hK1 : KFactRankTwoUniqueness) (hK2 : KFactRankThreeStructure)
    (h : GL83SmallRankInterfaceW G) : GL83SmallRankInterface G where
  prop614 := h.prop614
  prop65 := by
    intro p P M x z T hf hcov h1 h3 h5 q hq hq2 hqp hne
    exfalso
    have hiv := sr62w_fitting_inf_eq_bot hS hU0 hK1 hK2 hf
      (h.fitting628 p P M x z T hf hcov h1 h3 h5)
    refine hne (eq_bot_iff.mpr ?_)
    calc pCoreOf q (smallRankD p x) ⊓ M ≤
          CFSG.fittingSubgroupOf (rankThreePrimeCore 2 (smallRankD p x)) ⊓ M :=
        inf_le_inf_right M (sr62w_pCoreOf_le_fitting hf.prime hq hq2 x)
      _ = ⊥ := hiv
      _ ≤ ⊥ := le_rfl

theorem sr62w_evasion_of_nice (hS : Setting G) (hU0 : FullCoreLocal G)
    (hK1 : KFactRankTwoUniqueness) (hK2 : KFactRankThreeStructure)
    {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x z : G} {T : Subgroup G} {f : ℕ}
    (hyp : Lemma630Hyp G p P M x z T f) (hn : SmallRankNice p P M) {E : Subgroup G}
    (hE : SmallRankSBSylow p f x z T E) : E ⊓ M = ⊥ := by
  obtain ⟨rfl, hsolv, he⟩ := hn
  obtain ⟨hf, hcov, h28, hfp, hf2, hfD, h29⟩ := hyp
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have : Fact f.Prime := ⟨hfp⟩
  have hf3 : f ≠ 3 := sr629_ne_prime hp hfp x hfD
  obtain ⟨-, -, -, hFe, hF4, -⟩ := h29
  have hFM : smallRankF 3 f x ⊓ M = ⊥ := by
    rw [eq_bot_iff, ← h28.2.2.2]
    exact inf_le_inf_right M (sr629_F_le_fitting hp hfp hf2 x)
  have hFne : smallRankF 3 f x ≠ ⊥ := by
    intro hF
    have h1 : Nat.card (smallRankF 3 f x) = 1 := by rw [hF]; exact Subgroup.card_bot
    rw [hF4] at h1
    exact (Nat.one_lt_pow (by norm_num) hfp.one_lt).ne' h1
  have hFE : smallRankF 3 f x ≤ E :=
    k631_le_of_sylow_centralizer hfp (sr629_F_isPGroup hfp x) hFe.1 hE.1 hE.2.1 hE.2.2.1
  have hBE : zpowers x ⊔ zpowers z ≤ normalizer (E : Set G) := le_sup_right.trans hE.2.2.2
  have hBM : zpowers x ⊔ zpowers z ≤ M := hf.B_le_M hS
  have hBX : zpowers x ⊔ zpowers z ≤ normalizer ((E ⊓ M : Subgroup G) : Set G) :=
    (le_inf hBE (hBM.trans le_normalizer)).trans inf_normalizer_le_normalizer_inf
  by_contra hne
  have hXp : IsPGroup f ↥(E ⊓ M) := hE.2.1.to_le inf_le_left
  have hcop : Nat.Coprime (Nat.card ↥(E ⊓ M)) 6 := by
    obtain ⟨k, hk⟩ := hXp.exists_card_eq
    rw [hk]
    refine Nat.Coprime.pow_left k ?_
    have h2 : Nat.Coprime f 2 := (Nat.coprime_primes hfp Nat.prime_two).mpr hf2
    have h3 : Nat.Coprime f 3 := (Nat.coprime_primes hfp Nat.prime_three).mpr hf3
    exact (show (6 : ℕ) = 2 * 3 by norm_num) ▸ Nat.Coprime.mul_right h2 h3
  have hN : normalizer ((E ⊓ M : Subgroup G) : Set G) ≤ M :=
    prop65_of_kfacts hS hU0 hK1 hK2 P M hf.situation hsolv he x z hf.point hf.central
      (E ⊓ M) inf_le_right hne hcop hBX
  have hEM : E ≤ M := by
    by_contra hEM
    have hlt : E ⊓ M < E :=
      lt_of_le_of_ne inf_le_left fun heq => hEM (heq.symm.le.trans inf_le_right)
    obtain ⟨y, hyE, hyN, hyX⟩ := sr628_exists_mem_normalizer_not_mem hE.2.1 hlt
    exact hyX ⟨hyE, hN hyN⟩
  refine hFne (eq_bot_iff.mpr ?_)
  calc smallRankF 3 f x ≤ smallRankF 3 f x ⊓ M := le_inf le_rfl (hFE.trans hEM)
    _ = ⊥ := hFM
    _ ≤ ⊥ := le_rfl

end CFSG.LocalAnalysis.RankThreeTheoremC
