module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixKbarInputs
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixKbarSingleFacts
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenInputs
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixKbarPair
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixNineTenOne
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.NineTenBridge
import CFSG.LocalAnalysis.AGL81TheoremCD.RankThree.NineSettingOfHypC
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.PCompNonempty
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineSixTwoComp
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenKStar
import CFSG.LocalAnalysis.RankThreeUC.AGL81CStarImgEquiv
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTwelveOneComp
import CFSG.HardMathSupport.Solomon.Coordinator.I11_2FullTypes
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBPrimeJoinTransport
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineEightBridge

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open Subgroup CFSG.LocalAnalysis.RankThreeUC.AGL81C

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {p : ℕ} {Q H : Subgroup G} {d : ℕ}
  {L₁ L₂ L₃ : Subgroup G} {n₁ n₂ n₃ : ℕ}

private theorem isPComponentIn_self {p : ℕ} [Fact p.Prime] {L H : Subgroup G}
    (hLH : IsPComponentIn p L H) : IsPComponentIn p L L := by
  have hint := (CFSG.ComponentClassification.CatalogueBPrimeJoin.pComponent_subgroupOf_iff
    p L H hLH.1).mp hLH.2
  refine ⟨le_rfl, ?_⟩
  rw [CFSG.ComponentClassification.CatalogueBPrimeJoin.pComponent_subgroupOf_iff p L L le_rfl]
  exact ⟨by rw [Subgroup.subgroupOf_self]; exact Subgroup.IsSubnormal.top, hint.2.1, hint.2.2⟩

private theorem false_of_altSix_of_kSub_eq
    (hc : TwelveSixKCtx G M 3 Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃)
    {L : Subgroup G} (hLH : IsPComponentIn 3 L H) (hkL : kSub 3 M H = L)
    (hAlt : Nonempty (↥L ⧸ CFSG.solvableRadical ↥L ≃* alternatingGroup (Fin 6))) :
    False := by
  obtain ⟨e₁⟩ := nonempty_center_quot_equiv_altSix_of_isPComponentIn hLH hAlt
  obtain ⟨e₂⟩ := hLH.nonempty_quotEquiv_starImg Nat.prime_three
  have hstar : starImg 3 H L = kStar 3 M H := by rw [kStar_eq_starImg, hkL]
  have hqs : CFSG.IsQuasisimple (↥L ⧸ CFSG.pPrimeCore 3 ↥L) :=
    hLH.isQuasisimple_quot Nat.prime_three
  have hperfStar : _root_.commutator ↥(starImg 3 H L) = ⊤ := by
    have : Group.IsPerfect (↥L ⧸ CFSG.pPrimeCore 3 ↥L) := hqs.1
    exact (Group.IsPerfect.ofSurjective (f := e₂.toMonoidHom) e₂.surjective).commutator_eq_top
  have hperf : _root_.commutator ↥(kStar 3 M H) = ⊤ := by
    rw [← hstar]
    exact hperfStar
  have hcongr : (↥L ⧸ CFSG.pPrimeCore 3 ↥L) ⧸
      Subgroup.center (↥L ⧸ CFSG.pPrimeCore 3 ↥L) ≃*
      ↥(starImg 3 H L) ⧸ Subgroup.center ↥(starImg 3 H L) :=
    QuotientGroup.congr (Subgroup.center (↥L ⧸ CFSG.pPrimeCore 3 ↥L))
      (Subgroup.center ↥(starImg 3 H L)) e₂ (Subgroup.map_center_eq e₂)
  have he : Nonempty ((↥(kStar 3 M H)) ⧸ Subgroup.center ↥(kStar 3 M H) ≃*
      alternatingGroup (Fin 6)) := by
    rw [← hstar]
    exact ⟨hcongr.symm.trans e₁⟩
  obtain ⟨e⟩ := he
  exact (hc.false_of_pRank_mulAut_kStar_le_two D
    (CFSG.HardMathSupport.Solomon.Coordinator.i112f_pRank_mulAut_hatAlt
      (K := ↥(kStar 3 M H)) (Or.inl rfl) hperf e)).elim

private theorem single_component [Fact p.Prime]
    (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃)
    {L : Subgroup G} (hLH : IsPComponentIn p L H) (hkL : kSub p M H = L)
    (hA : ¬ pLayerIn p H ≤ M) :
    IsTwoPrimeComponentIn (kSub p M H) H := by
  have hLK : IsPComponentIn p L (kSub p M H) := by
    rw [hkL]
    exact isPComponentIn_self hLH
  rcases hc.h912.1 hA L hLK with htwo | ⟨hp3, hAlt⟩
  · rwa [hkL]
  · rw [hp3] at hc hLH hkL
    exact (false_of_altSix_of_kSub_eq hc D hLH hkL hAlt).elim

theorem twelveSixKbarSingle_of (h35r : KFactThreeFiveRankOne)
    (hpair : NineSixMoreoverPairFive) (hSz : KFactSz32MulAutThreeFree) :
    TwelveSixKbarSingle := by
  intro G _ _ M p Q H d L₁ L₂ L₃ n₁ n₂ n₃ hyp
  obtain ⟨hc, ⟨D⟩, -, hA, hXM, -, -⟩ := hyp
  classical
  have : Fact p.Prime := ⟨hc.ctx.p_prime⟩
  let S : Set (Subgroup G) := {Y | IsPComponentIn p Y H ∧ ¬ Y ≤ M}
  have hkS : kSub p M H = sSup S := by
    unfold kSub
    rw [if_neg hA]
  obtain ⟨E, hEQ, hE, hEc, hΓ⟩ := hc.ctx.exists_E_sq
  have hC := hc.ctx.hypCGen hEQ hE hEc hΓ
  have h2 : S.ncard ≤ 2 :=
    nineSixTwoComp_holds G M E H E p hC.toNineSettingGen hC.mem_H2Fam hC.not_mem_sigmaM hA
  have hne : S.Nonempty := exists_pComponentIn_not_le_of_not_pLayerIn_le hA
  have hpos : 0 < S.ncard := (Set.ncard_pos (Set.toFinite S)).mpr hne
  have hcases : S.ncard = 1 ∨ S.ncard = 2 := by omega
  rcases hcases with h1 | h2'
  · obtain ⟨L, hSL⟩ := Set.ncard_eq_one.mp h1
    have hLmem : L ∈ S := by rw [hSL]; simp
    have hkL : kSub p M H = L := by rw [hkS, hSL, sSup_singleton]
    exact single_component hc D hLmem.1 hkL hA
  · obtain ⟨L, I, hLI, hSL⟩ := Set.ncard_eq_two.mp h2'
    have hLmem : L ∈ S := by rw [hSL]; simp
    have hImem : I ∈ S := by rw [hSL]; simp
    exact (hc.false_of_two_pComponents_not_le D hXM h35r hpair hSz hLmem.1 hLmem.2
      hImem.1 hImem.2 hLI).elim

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12

end
