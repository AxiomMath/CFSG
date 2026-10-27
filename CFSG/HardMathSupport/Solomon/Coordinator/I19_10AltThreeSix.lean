module

public import CFSG.HardMathSupport.Solomon.Coordinator.I19_6Red
public import CFSG.HardMathSupport.Timmesfeld.DefChar.CoreA1
public import CFSG.HardMathSupport.Timmesfeld.DefChar.LieOuterA
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.DefCharClassical
public import CFSG.LocalAnalysis.ComponentInitial.FieldNineAlternatingSix
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Assembly.QuasithinDefs
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.Foundations
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma32
public import CFSG.HardMathSupport.Solomon.LocalBalance.Prop22
public import CFSG.HardMathSupport.Timmesfeld.Proving.ExistsOrderPCentralizer
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingTransport
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHermitianIsometry
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.RankThree.Automorphisms.LinearHigherCoprime
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.IG1114
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremB
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremC
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.ZJTheorem
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.GW1965RemarkDGroup
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29Helpers
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag CFSG.GorensteinWalter
open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.DefChar
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.LocalTwo

set_option linter.unusedSectionVars false

theorem i1910a3_coreFree_psl2 {S : Type} [Group S] [Finite S] (hZ : Subgroup.center S = ⊥)
    {K : Type} [Field K] [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p] (hp2 : p ≠ 2)
    (hodd : IsOddPrimePower (Nat.card K)) (hKc : 3 < Nat.card K) (e : S ≃* PSL2 K) :
    ∀ x ∈ innerAut S, orderOf x = p → ∀ H : Subgroup (MulAut S), innerAut S ≤ H →
      GLAPPrimeCoreOf p (H ⊓ Subgroup.centralizer ({x} : Set (MulAut S))) = ⊥ := by
  intro x hx hxo H hH
  let ι : PSL2 (K) ≃* projectiveSL 2 (K) :=
    LinearCover.projectiveSpecialLinearEquivProjectiveSL 2 _
  let E : S ≃* projectiveSL 2 (K) := e.trans ι
  obtain ⟨g, rfl⟩ := hx
  have hord : orderOf g = p := by
    rw [← orderOf_injective (MulAut.conj : S →* MulAut S) (conj_injective_of_center_eq_bot hZ) g]
    exact hxo
  have hord0 : orderOf (E g) = p := by rw [MulEquiv.orderOf_eq E g]; exact hord
  obtain ⟨N, hN, hN0, hg0⟩ := exists_nilpotent_of_orderOf_eq (p := p) (E g) hord0
  refine gLAPPrimeCoreOf_eq_bot_of_framework hZ (Fact.out : p.Prime) g ∅
    {q' | E q' ∈ modelT 2 (K) N} ?_ ?_ ?_ ?_ ?_ H hH _ rfl
  · intro q' hq'
    rcases hq' with hq' | hq'
    · exact hq'.elim
    apply E.injective
    rw [map_mul, map_mul, hg0]
    exact model_h1 hN (E q') (Or.inr hq')
  · intro s q' hs hq'
    apply E.injective
    rw [map_mul, map_mul]
    refine model_hT hN (E s) (E q') ?_ hq'
    rw [← hg0, ← map_mul, ← map_mul, hs]
  · intro s q' _ hq'
    exact hq'.elim
  · intro q' hq'
    exact hq'.elim
  · intro α hα hfix
    have hcop : (orderOf (MulAut.congr e α)).Coprime p := by
      rw [MulEquiv.orderOf_eq (MulAut.congr e) α]; exact hα
    have h1 : MulAut.congr e α = 1 := by
      refine uniq_psl2 (p := p) hodd hKc hp2 hN hN0 _ hcop ?_
      intro s t hs
      have hmem : E.symm (proj 2 (K) s) ∈
          (∅ : Set S) ∪ {q' | E q' ∈ modelT 2 (K) N} :=
        Or.inr (by
          show E (E.symm _) ∈ modelT 2 (K) N
          rw [MulEquiv.apply_symm_apply]
          exact ⟨s, t, hs, rfl⟩)
      have h2 := hfix _ hmem
      have h3 : e.symm (QuotientGroup.mk s) = E.symm (proj 2 (K) s) := by
        apply E.injective
        rw [MulEquiv.apply_symm_apply]
        show ι (e (e.symm (QuotientGroup.mk s))) = _
        rw [MulEquiv.apply_symm_apply]
        rfl
      change e (α (e.symm (QuotientGroup.mk s))) = QuotientGroup.mk s
      rw [h3, h2]
      show e (E.symm (proj 2 (K) s)) = _
      rw [← h3, MulEquiv.apply_symm_apply]
    exact (MulAut.congr e).injective (by rw [h1, map_one])


theorem i1910a3_altSix : IsLocallyBalancedAbs 3 2 (alternatingGroup (Fin 6)) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hKc9 : Nat.card (GaloisField 3 2) = 9 := by
    rw [GaloisField.card 3 2 (by norm_num)]; norm_num
  have : Fintype (GaloisField 3 2) := Fintype.ofFinite _
  obtain ⟨e0⟩ := unique_field_nine_projective_linear_alternating_six_isomorphism
    (GaloisField 3 2) (by rw [← Nat.card_eq_fintype_card, hKc9])
  let e : alternatingGroup (Fin 6) ≃* PSL2 (GaloisField 3 2) := e0.symm
  have hZ : Subgroup.center (alternatingGroup (Fin 6)) = ⊥ :=
    alternatingGroup.center_eq_bot (by simp)
  have hodd : IsOddPrimePower (Nat.card (GaloisField 3 2)) :=
    ⟨3, 2, Nat.prime_three, by decide, by norm_num, by rw [hKc9]; norm_num⟩
  have hKc : 3 < Nat.card (GaloisField 3 2) := by rw [hKc9]; norm_num
  intro D hD hcard H hH hDH
  obtain ⟨x, ⟨hxD, hxI⟩, hx1⟩ := exists_inner_transport_lt e D (fun a ha => hD.2 a ha)
    (by rw [hcard]; norm_num)
    (fun D' hexp hc => exists_inner_of_elemAbelian_psl2_all Nat.prime_three (by norm_num) D' hexp hc)
  have hxp : orderOf x = 3 := orderOf_eq_prime (hD.2 x hxD) hx1
  have hle : localDeltaIn 3 H D ≤
      GLAPPrimeCoreOf 3 (H ⊓ Subgroup.centralizer ({x} : Set (MulAut (alternatingGroup (Fin 6))))) := by
    unfold localDeltaIn
    exact iInf₂_le_of_le x hxD (iInf_le_of_le hx1 le_rfl)
  rw [i1910a3_coreFree_psl2 hZ (by norm_num) hodd hKc e x hxI hxp H hH] at hle
  exact le_bot_iff.1 hle

end CFSG.HardMathSupport.Solomon.Coordinator
