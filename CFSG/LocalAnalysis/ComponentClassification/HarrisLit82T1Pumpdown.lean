module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLiftField
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitTwoComp
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aOddQuotIso
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas
public import CFSG.GroupTheory.ConjugatePairSubnormality
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma45c
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup

variable {X : Type} [Group X] [Finite X]

theorem range_barMap_centralizerResidual {K : Subgroup X} {t : X}
    (htN : t ∈ normalizer (K : Set X)) (ht2 : IsPGroup 2 (zpowers t))
    (hperf : Group.IsPerfect (Bar K)) (htriv : barAction K ⟨t, htN⟩ = 1) :
    (barMap K (centralizerResidual_le_left (g := t))).range = ⊤ := by
  have hfix : fixedPoints (barAction K ⟨t, htN⟩) = ⊤ := by
    rw [htriv]
    ext y
    simp only [mem_fixedPoints, MulAut.one_apply, mem_top]
  have hrange := range_barMap_perfectResidual htN ht2
  rw [perfectResidual_map_subtype_eq hfix] at hrange
  refine hrange.trans ?_
  have htop : Group.IsPerfect ↥(⊤ : Subgroup (Bar K)) :=
    Group.IsPerfect.ofSurjective (f := Subgroup.topEquiv.symm.toMonoidHom)
      (MulEquiv.surjective _)
  exact top_le_iff.mp (le_perfectResidual_map le_rfl htop)

theorem pumpdown {A K : Subgroup X} (hK : IsTwoComponentIn K A) {t : X}
    (htN : t ∈ normalizer (K : Set X)) (ht2 : IsPGroup 2 (zpowers t))
    (htriv : barAction K ⟨t, htN⟩ = 1) :
    IsTwoComponentIn (centralizerResidual K t) (A ⊓ centralizer {t}) ∧
      Nonempty (↥(centralizerResidual K t) ⧸ pPrimeCore 2 ↥(centralizerResidual K t) ≃*
        Bar K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq : IsQuasisimple (Bar K) := hK.2.2.2
  have hsurj : Function.Surjective (barMap K (centralizerResidual_le_left (g := t))) :=
    MonoidHom.range_eq_top.mp (range_barMap_centralizerResidual htN ht2 hq.1 htriv)
  have hker : ¬ 2 ∣ Nat.card (barMap K (centralizerResidual_le_left (g := t))).ker :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp (coprime_card_ker_barMap _)
  obtain ⟨e⟩ := GSThmB.OddQuot.nonempty_pPrimeCore_equiv_of_surjective _ hsurj hker
  let eJ : ↥(centralizerResidual K t) ⧸ pPrimeCore 2 ↥(centralizerResidual K t) ≃* Bar K :=
    e.trans ((QuotientGroup.quotientMulEquivOfEq (pPrimeCore_quotient_pPrimeCore_eq_bot 2)).trans
      QuotientGroup.quotientBot)
  refine ⟨⟨le_inf (centralizerResidual_le_left.trans hK.1)
    (centralizerResidual_le.trans inf_le_right), ?_, ?_⟩, ⟨eJ⟩⟩
  ·
    have hD : ((K ⊓ centralizer {t}).subgroupOf (A ⊓ centralizer {t})).IsSubnormal := by
      have h1 : ((K.subgroupOf A).subgroupOf ((A ⊓ centralizer {t}).subgroupOf A)).IsSubnormal :=
        hK.2.1.subgroupOf
      rw [CFSG.GroupTheory.isSubnormal_subgroupOf_subgroupOf_iff
        (inf_le_left : A ⊓ centralizer {t} ≤ A)] at h1
      convert h1 using 1
      ext x
      simp only [mem_subgroupOf, mem_inf]
      exact ⟨fun h => h.1, fun h => ⟨h, x.2.2⟩⟩
    have hJD : ((centralizerResidual K t).subgroupOf (K ⊓ centralizer {t})).IsSubnormal :=
      ((normal_subgroupOf_iff_le_normalizer centralizerResidual_le).mpr
        (le_normalizer_perfectResidual_map _)).isSubnormal
    exact CFSG.GroupTheory.isSubnormal_subgroupOf_trans centralizerResidual_le
      (inf_le_inf_right _ hK.1) hJD hD
  · exact ⟨isPerfect_perfectResidual_map _, LocalCores.isQuasisimple_of_mulEquiv eJ.symm hq⟩

omit [Finite X] in
theorem barAction_eq_one_of_mem_center {K : Subgroup X} {t : K}
    (ht : (QuotientGroup.mk t : Bar K) ∈ center (Bar K))
    (htN : (t : X) ∈ normalizer (K : Set X)) : barAction K ⟨t, htN⟩ = 1 := by
  ext y
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective y
  rw [barAction_mk, MulAut.one_apply]
  have h1 : normalizerConj K ⟨t, htN⟩ k = t * k * t⁻¹ := Subtype.ext rfl
  rw [h1, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
    ← mem_center_iff.mp ht (QuotientGroup.mk k), mul_inv_cancel_right]

end CFSG.ComponentClassification.HarrisLit.T1
