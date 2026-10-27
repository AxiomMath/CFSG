module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Lemma59
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5InputsRank
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Cor217Invt
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SKu58

public section

namespace CFSG.ComponentClassification.GrSLit.GrS5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

theorem l34Lemma59_of_inputs_ku
    (hS : SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hSol : SolomonCommutingCoreInput) (hGW : GorensteinWalterConnectedInput)
    (hMax : MaximalTwoComponentInput) (hL34 : L34InvolutionCentralizerFact)
    (hStd : GSThmB.L34StandardEvenInput) (h56 : L34Lemma56) (hAut : L34AutRankOneNormalFact)
    (hF1 : L34SylowCentralizerFact) (hUCen : L34UnitaryCenterFact)
    (hUnit : L34UnbalancingUnitaryStep) (hUC : L34UnitaryCentralizerFact)
    (hUA : L34UnitaryAutFact) (hComp : L34Cor217ComponentStep)
    (h41 : L34Prop41) (hKu : GrS5S.L34Sec5KuOddStep)
    (hFour : L34UnbalancingFourFact)
    (hOrb : L34Lemma58OrbitStep) (hElem : L34ElementaryCenterSylowFact)
    (hNE : L34NonelementaryCenterCommutatorFact) (hL2 : L2UnbalancingAutFact)
    (hRank : L34AutRankFact) (hERank : L34ElementaryRankFact) : L34Lemma59 := by
  intro G _ _ L t S T hset
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hInvt := l34Sec5ComponentInvariantStep_of_comp hMax hComp
  obtain ⟨hE, hE4⟩ :=
    isElemTwo_omegaOne_of_setting_ku hS hU hheld hSol hGW hMax hL34 hKu hFour hset
  have hne := omegaOne_ne_zpowers_of_inputs hS hU hheld hSol hGW hMax hL34 hStd h56 hAut hF1
    hUCen hUnit hUC hUA hComp h41 hset
  obtain ⟨-, hLt, hLpt⟩ := eq_of_mem_inf_centralizer hS hU hheld hSol hGW hset
  have hZS := mem_center_of_setting hS hU hheld hSol hGW hset
  have hset' := hset
  obtain ⟨-, ⟨⟨-, -, -, -, -, hto, -, -⟩, htypeL, -⟩, -, hSyl, htS, -, -⟩ := hset'
  have hS2 : IsPGroup 2 S := IsSylowTwoIn.isPGroup hSyl
  have ht2 : t * t = 1 := by rw [← pow_two, ← hto, pow_orderOf_eq_one]
  have htK : t ∈ coreActionKernel L := mem_coreActionKernel_of_commute fun l hl =>
    (mem_centralizer_singleton_iff.mp (hLt hl)).symm
  have htΩ : t ∈ omegaOne (S ⊓ coreActionKernel L) := subset_closure ⟨mem_inf.mpr ⟨htS, htK⟩, ht2⟩
  have hle : zpowers t ≤ omegaOne (S ⊓ coreActionKernel L) := zpowers_le.mpr htΩ
  obtain ⟨z, hzΩ, hzt⟩ : ∃ z ∈ omegaOne (S ⊓ coreActionKernel L), z ∉ zpowers t := by
    by_contra h
    push Not at h
    exact hne (le_antisymm h hle)
  have hz2 : z * z = 1 := hE.2 z hzΩ
  have hz1 : z ≠ 1 := fun h => hzt (h ▸ one_mem _)
  have hzt' : z ≠ t := fun h => hzt (h ▸ mem_zpowers t)
  have hzo : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz2) hz1
  have hzQ : z ∈ S ⊓ coreActionKernel L := omegaOne_le _ hzΩ
  obtain ⟨-, hcard⟩ := elemTwo_zpowers_sup hz2 (isElemTwo_zpowers ht2) (fun y hy => by
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hy
    exact (Commute.zpow_right (show Commute z t from hZS z (mem_inf.mp hzQ).1) i).eq) hzt
  rw [Nat.card_zpowers, hto] at hcard
  have hΩeq : omegaOne (S ⊓ coreActionKernel L) = zpowers t ⊔ zpowers z := by
    rw [sup_comm]
    exact (Subgroup.eq_of_le_of_card_ge (sup_le (zpowers_le.mpr hzΩ) hle)
      (by rw [hcard]; exact hE4)).symm
  have hΩ4 : Nat.card ↥(omegaOne (S ⊓ coreActionKernel L)) = 4 := by
    rw [hΩeq, sup_comm, hcard]
  have hperf : ⁅L, L⁆ = L := GSThmB.commutator_eq_self_of_isPComponent hLt hLpt
  have hS64 : ∀ E : Subgroup G, E ≤ S → IsElemTwo E → Nat.card E ≤ 64 := by
    intro E hES hEl
    have h1 := hRank G L E hperf htypeL (hES.trans hSyl.1) hEl
    have h2 : E ⊓ coreActionKernel L ≤ omegaOne (S ⊓ coreActionKernel L) := fun x hx =>
      subset_closure ⟨mem_inf.mpr ⟨hES (mem_inf.mp hx).1, (mem_inf.mp hx).2⟩,
        hEl.2 x (mem_inf.mp hx).1⟩
    have h3 := card_le_of_le h2
    omega
  have hA : S ⊓ L ⊔ zpowers t ⊔ zpowers z ≤ S :=
    sup_le (sup_le inf_le_left (zpowers_le.mpr htS)) (zpowers_le.mpr (mem_inf.mp hzQ).1)
  have hup : ∀ H : Subgroup G, H ≤ S → pRank 2 ↥H ≤ 6 := fun H hH =>
    pRank_le_of_forall_isElemTwo fun E hEH hEl => (hS64 E (hEH.trans hH) hEl).trans (by norm_num)
  have hS₀ : IsSylowTwoIn (S ⊓ L) L := isSylowTwoIn_inf_of_isSubnormal hSyl le_normalizer
    (Subgroup.Normal.isSubnormal Subgroup.normal_in_normalizer)
  have hZ2 : ∀ y ∈ S ⊓ L ⊓ zStarIn L, y * y = 1 := by
    intro y hy
    obtain ⟨hy1, hyZ⟩ := mem_inf.mp hy
    have hyQL : y ∈ S ⊓ coreActionKernel L ⊓ L := mem_inf.mpr ⟨mem_inf.mpr ⟨(mem_inf.mp hy1).1,
      zStarIn_le_coreActionKernel L hyZ⟩, (mem_inf.mp hy1).2⟩
    by_cases hZ : S ⊓ coreActionKernel L ⊓ L = ⊥
    · rw [hZ, mem_bot] at hyQL
      rw [hyQL, mul_one]
    · exact (omegaOne_eq_of_inputs_ku hS hU hheld hSol hGW hMax hL34 hKu hFour hOrb
        hElem hNE hL2 hUnit hUA hInvt hset hZ).2 y hyQL
  obtain ⟨A₀, hA₀S, hA₀, hA₀c⟩ := hERank G L (S ⊓ L) hperf htypeL hS₀ hZ2
  have hcomm : ∀ a ∈ A₀, ∀ q ∈ omegaOne (S ⊓ coreActionKernel L), a * q = q * a := by
    intro a ha q hq
    have hqQ := omegaOne_le _ hq
    exact (commute_of_mem_coreActionKernel hS2 (mem_inf.mp hqQ).1 (mem_inf.mp hqQ).2
      (mem_inf.mp (hA₀S ha)).1 (mem_inf.mp (hA₀S ha)).2).symm
  have hEl : IsElemTwo (A₀ ⊔ omegaOne (S ⊓ coreActionKernel L)) := IsElemTwo.sup hA₀ hE hcomm
  obtain ⟨hprod, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute A₀
    (omegaOne (S ⊓ coreActionKernel L)) hcomm
  have hinf : A₀ ⊓ omegaOne (S ⊓ coreActionKernel L) ≤ S ⊓ L ⊓ zStarIn L := fun x hx => by
    obtain ⟨hxA, hxΩ⟩ := mem_inf.mp hx
    have hxS₀ := hA₀S hxA
    exact mem_inf.mpr ⟨hxS₀, inf_coreActionKernel_le_zStarIn L
      (mem_inf.mpr ⟨(mem_inf.mp hxS₀).2, (mem_inf.mp (omegaOne_le _ hxΩ)).2⟩)⟩
  have hinfc := card_le_of_le hinf
  have hES : A₀ ⊔ omegaOne (S ⊓ coreActionKernel L) ≤ S ⊓ L ⊔ zpowers t ⊔ zpowers z := by
    rw [sup_assoc, ← hΩeq]
    exact sup_le_sup_right hA₀S _
  have hE64 : Nat.card ↥(A₀ ⊔ omegaOne (S ⊓ coreActionKernel L)) = 2 ^ 6 := by
    have h1 := hS64 _ (hES.trans hA) hEl
    have h2 : 0 < Nat.card ↥(S ⊓ L ⊓ zStarIn L) := Nat.card_pos
    have h3 : 0 < Nat.card ↥(A₀ ⊓ omegaOne (S ⊓ coreActionKernel L)) := Nat.card_pos
    rw [hA₀c, hΩ4] at hprod
    have h4 : 64 * Nat.card ↥(A₀ ⊓ omegaOne (S ⊓ coreActionKernel L)) ≤
        Nat.card ↥(A₀ ⊔ omegaOne (S ⊓ coreActionKernel L)) *
          Nat.card ↥(A₀ ⊓ omegaOne (S ⊓ coreActionKernel L)) := by
      rw [hprod]
      nlinarith
    have h5 := Nat.le_of_mul_le_mul_right h4 h3
    norm_num
    omega
  have hlow := GrS4.le_pRank_of_isElemTwo hES hEl hE64
  have hlowS := GrS4.le_pRank_of_isElemTwo (hES.trans hA) hEl hE64
  exact ⟨z, hzo, hzt', hΩeq, le_antisymm (hup _ hA) hlow, le_antisymm (hup S le_rfl) hlowS⟩

end CFSG.ComponentClassification.GrSLit.GrS5
