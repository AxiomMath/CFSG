module

import CFSG.LocalAnalysis.RankThreeCoreUniqueness.RelativePairTwoCore
public import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2_Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.RelativePairInputs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

theorem IsOptimalRelPair.normalizer_pCoreOf_eq {p : ℕ} {M D R T H V : Subgroup G}
    (hopt : IsOptimalRelPair p M D R T H V) : normalizer (pCoreOf 2 H : Set G) = H := by
  set H' := normalizer (pCoreOf 2 H : Set G) with hH'
  have hHH' : H ≤ H' := localGroup_le_normalizer_pCoreOf 2 H
  have hV := hopt.pair
  have hcand : IsRelPairCandidate p D R T H' :=
    ⟨normalizer_pCoreOf_isTwoLocal H hV.cand.twoLocal, hV.cand.base_le.trans hHH',
      hV.cand.not_coprime.trans (Subgroup.card_dvd_of_le (invariantTwoJoinIn_mono hHH'))⟩
  have hVle : V ≤ H' ⊓ M := le_inf ((hV.maximal.1.trans inf_le_left).trans hHH')
    (hV.maximal.1.trans inf_le_right)
  obtain ⟨V', hVV', hmax⟩ := exists_invariantTwoMaximalWithin_containing D (H' ⊓ M) V hVle
    hV.maximal.2.1 hV.maximal.2.2.1
  have hpair : IsRelPairCandidatePair p M D R T H' V' :=
    ⟨hcand, hmax, hV.base_le.trans hVV'⟩
  have hcardV : Nat.card V' = Nat.card V :=
    le_antisymm (hopt.card_le H' V' hpair) (Subgroup.card_le_of_le hVV')
  have hO₂ : pCoreOf 2 H ≤ pCoreOf 2 H' := by
    refine normal_pGroup_le_pCoreOf 2 (pCoreOf 2 H) H' ((pCoreOf_le 2 H).trans hHH') ?_
      (pCoreOf_isPGroup 2 H)
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer ((pCoreOf_le 2 H).trans hHH')).mpr le_rfl
  have hcardO₂ : Nat.card (pCoreOf 2 H') = Nat.card (pCoreOf 2 H) :=
    le_antisymm (hopt.core_le H' V' hpair hcardV) (Subgroup.card_le_of_le hO₂)
  exact (Subgroup.eq_of_le_of_card_ge hHH' (hopt.order_le H' V' hpair hcardV hcardO₂)).symm

theorem IsOptimalRelPair.invariantTwoMaximalWithin_H {p : ℕ} {P : Sylow p G}
    {M D R T H V : Subgroup G} (hd : MaximalRelativePair p P M D R T)
    (hopt : IsOptimalRelPair p M D R T H V) :
    V ≤ M ∧ invariantTwoMaximalWithin D H V := by
  have hV := hopt.pair
  refine ⟨hV.maximal.1.trans inf_le_right, hV.maximal.1.trans inf_le_left, hV.maximal.2.1,
    hV.maximal.2.2.1, fun A hAH hA hDA hVA => ?_⟩
  have hAM : A ≤ M := le_of_normalizer_inf_le_of_relativePair hd.maxR hd.maxT hd.not_le_R
    hd.le_T hd.maximal hA hDA (hV.base_le.trans hVA)
  exact hV.maximal.2.2.2 A (le_inf hAH hAM) hA hDA hVA

theorem IsOptimalRelPair.pCoreOf_le_V {p : ℕ} {P : Sylow p G} {M D R T H V : Subgroup G}
    (hd : MaximalRelativePair p P M D R T) (hopt : IsOptimalRelPair p M D R T H V) :
    pCoreOf 2 H ≤ V :=
  invariantTwoMaximalWithin_contains_normal_two_subgroup D H V (pCoreOf 2 H)
    ((le_sup_right : D ≤ relPairBase R T ⊔ D).trans hopt.pair.cand.base_le)
    (hopt.invariantTwoMaximalWithin_H hd).2 (pCoreOf_le 2 H) (pCoreOf_normal 2 H)
    (pCoreOf_isPGroup 2 H)

theorem IsRelPairCandidate.pRank_eq_two (hS : Setting G) (hD1 : TheoremD1 G) {p : ℕ}
    (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G} {M D R T H : Subgroup G}
    (hext : ExtremalObstruction p P M D) (hPD : ¬ (P : Subgroup G) ≤ normalizer (D : Set G))
    (hR : TransitivityReduction G) (h13 : GL83InvariantTwoSylow G)
    (hH : IsRelPairCandidate p D R T H) : CFSG.Open.pRank p H = 2 := by
  classical
  have hprime := sigmaA_prime p hp
  have hfact : Fact p.Prime := ⟨hprime⟩
  obtain ⟨hDab, z, hzD, hz1, hzc, hzp, hN₀M, hCD, hglob⟩ :=
    hext.transitivity_data hS hD1 hp hPD hR h13
  obtain ⟨hDe, hDc⟩ := hext.isElemAbelian_of_isMulCommutative hprime hDab
  obtain ⟨hM, hDP, -, -⟩ := hext.obstruction
  obtain ⟨hPM, hP3⟩ := sylow_le_of_isCoreMaxLocal hS hp hM
  have hDH : D ≤ H := (le_sup_right : D ≤ relPairBase R T ⊔ D).trans hH.base_le
  have hHlocal := hH.twoLocal
  refine le_antisymm ?_ (hext.rank_eq ▸ pRank_mono p hprime.one_lt hDH)
  by_contra h3
  push Not at h3
  obtain ⟨E, hEH, hE, hEc⟩ := pRank_attained p H (by omega)
  obtain ⟨P', hEP'⟩ := (elementary_isPGroup p E hE).exists_le_sylow
  obtain ⟨M', hM', hP'M', -, -, -⟩ := exists_isCoreMaxLocal hS hp P'
  have hHM' : H ≤ M' := by
    refine le_of_three_le_pRank_inf hD1 hp hM' hHlocal
      (le_trans (show 3 ≤ CFSG.Open.pRank p H by omega) ?_)
    unfold CFSG.Open.pRank
    exact le_csSup (pRank_set_bddAbove p hprime.one_lt _)
      ⟨E, le_inf hEH (hEP'.trans hP'M'), hE, hEc⟩
  obtain ⟨m, hm⟩ := pGroup_conjugate_into_sylow_within_overgroup p hprime P' M' hP'M' D
    (P.isPGroup'.to_le hDP) (hDH.trans hHM')
  set P'' : Sylow p G := ((m : G)⁻¹) • P' with hP''
  have hDP'' : D ≤ (P'' : Subgroup G) := by
    rw [hP'', sylow_coe_smul_eq_map]
    intro d hd
    refine ⟨(m : G) * d * (m : G)⁻¹, hm ⟨d, hd, rfl⟩, ?_⟩
    simp [mul_assoc]
  have hM'' : IsCoreMaxLocal p P'' M' := by
    have := hM'.smul hprime.one_lt ((m : G)⁻¹)
    have hM'm : M'.map (MulAut.conj ((m : G)⁻¹)).toMonoidHom = M' :=
      mem_normalizer_iff_map_conj_eq.mp (le_normalizer (inv_mem m.2))
    rwa [hM'm] at this
  obtain ⟨hP''M', hP''3⟩ := sylow_le_of_isCoreMaxLocal hS hp hM''
  have hiso : IsIsolatedPlane p (P'' : Subgroup G) D := by
    refine ⟨hDP'', (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p D).2 hDe, hDc,
      fun E' _ hE' hDE' => ?_⟩
    have hE'' : IsElemAbelian p E' :=
      (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p E').1 hE'
    have hE'D : E' ≤ D := fun e he =>
      hext.mem_of_mem_centralizer_of_isMulCommutative hS hD1 hp hDab hCD
        (mem_centralizer_iff.mpr fun d hd => congrArg Subtype.val
          (hE''.1.is_comm.comm ⟨d, hDE' hd⟩ ⟨e, he⟩)) (hE''.2 e he)
    rw [← hDc]
    exact card_le_of_le hE'D
  obtain ⟨A, hAP'', hA, hAc⟩ := pRank_attained p (P'' : Subgroup G) (by rw [hP''3]; norm_num)
  rw [hP''3] at hAc
  obtain ⟨-, z'', hz''D, hz''1, hz''c, -, -⟩ := isolatedPlane_structure hprime P''.isPGroup' hiso
    hAP'' ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p A).2 hA) hAc
  obtain ⟨g, hgN, hgz⟩ := hext.exists_mem_normalizer_zpowers_eq hS hD1 hp hPD hDab hCD hzD hz1
    hzc hN₀M hz''D hz''1
  have hP''Mg : (P'' : Subgroup G) ≤ M.map (MulAut.conj g).toMonoidHom := by
    refine (le_normalizer_zpowers_of_le_centralizer hz''c).trans ?_
    rw [hgz, ← Subgroup.map_equiv_normalizer_eq]
    exact map_mono hN₀M
  have hMg := hM.smul hprime.one_lt g
  have hM'Mg : M' ≤ M.map (MulAut.conj g).toMonoidHom := by
    refine le_of_three_le_pRank_inf hD1 hp hMg hM'.1.1 ?_
    rw [← hP''3]
    exact pRank_mono p hprime.one_lt (le_inf hP''M' hP''Mg)
  have hHMg : H ≤ M.map (MulAut.conj g).toMonoidHom := by
    have hMgeq : M.map (MulAut.conj g).toMonoidHom = M' := hM'.1.2 _ hMg.1.1 hM'Mg
    rw [hMgeq]
    exact hHM'
  set X := CFSG.ABGTheoremB.pPrimeCoreIn p M ⊔ CFSG.ABGTheoremB.pPrimeCoreIn p
    (normalizer ((zpowers z : Subgroup G) : Set G)) with hX
  have hXall : ∀ A : Subgroup G, A ≤ M → IsPGroup 2 A → D ≤ normalizer (A : Set G) → A ≤ X := by
    intro A hAM hA2 hDA
    obtain ⟨T₁, hAT₁, hT₁⟩ := exists_invariantTwoMaximalWithin_containing D M A hAM hA2 hDA
    exact hAT₁.trans (h13 p hp P M D hext hPD hDab z hzD hz1 hzc hzp T₁ hT₁).le
  have hjoin : invariantTwoJoinIn D H ≤ X.map (MulAut.conj g).toMonoidHom :=
    (invariantTwoJoinIn_mono hHMg).trans ((invariantTwoJoinIn_map_le hgN).trans
      (Subgroup.map_mono (invariantTwoJoinIn_le_of_forall hXall)))
  have hdvd : p ∣ Nat.card (X.map (MulAut.conj g).toMonoidHom) :=
    hH.not_coprime.trans (Subgroup.card_dvd_of_le hjoin)
  rw [Subgroup.card_map_of_injective (MulAut.conj g).injective] at hdvd
  exact (hprime.coprime_iff_not_dvd.mp (coprime_card_pPrimeCoreIn_sup hN₀M)) hdvd

end CFSG.LocalAnalysis.RankThreeTheoremC
