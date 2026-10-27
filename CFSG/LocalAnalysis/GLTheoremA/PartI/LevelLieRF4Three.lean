module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieRF4Field
import CFSG.RankThree.PartTwo.Sec8.Item8KFacts2ProofReeConj
import CFSG.RankThree.PartTwo.Sec8.Item87ProofGamma
import CFSG.LocalAnalysis.GLTheoremA.S4.Lemma49i
import CFSG.HardMathSupport.Timmesfeld.DefChar.LieOuterTwisted
import CFSG.SignalizerFunctorTheorem.CatalogBridge.NonLocalLargeReeMain
public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLie
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.LieType.Ree (ReeTag)

private theorem rf4_u3_stated_iso {c fe : ℕ} [Fact c.Prime] (hc : c = 2) (hfe : fe = 3)
    {G : Type} [Group G]
    (E : G ≃* StatedProj (StatedSU (2 + 1) (c ^ fe) (GaloisField c (2 * fe)))) :
    Nonempty (G ≃* StatedProj (StatedSU 3 (2 ^ 3) (GaloisField 2 (2 * 3)))) := by
  subst hc hfe
  exact ⟨E⟩

private def rf4Q8 : TauCeti.PrimePower := ⟨2, 3, Nat.prime_two, by norm_num⟩

private theorem rf4_twistedA_valid : (TauCeti.LieTypeIndex.twistedA 2 rf4Q8).Valid := by
  rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
    TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
  norm_num [rf4Q8, TauCeti.PrimePower.card_def]

theorem rf4_u3_level {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]
    (hK : Nat.card K = 2 ^ (2 * 1 + 1)) (y : ReeTag.F4.reeGamma K 1) (hy : orderOf y = 3) :
    ∀ I : Subgroup (ReeTag.F4.reeGamma K 1),
      GLAPComponent 3 (fixSubgroup (MulAut.conj y)) I → kLevel 3 (PSimple 3 I) ≤ 2 := by
  classical
  haveI : Finite (ReeTag.F4.reeGamma K 1) := Subtype.finite
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := CFSG.RankThree.PartTwo.Sec8.Item8KFacts2Proof.centralizer_mulEquiv_unitarySU 1 K hK y hy
  have hF : Nat.card (GaloisField 2 (2 * (2 * 1 + 1))) = (2 ^ (2 * 1 + 1)) ^ 2 := by
    rw [GaloisField.card 2 _ (by norm_num)]
    norm_num
  haveI : Fintype (GaloisField 2 (2 * (2 * 1 + 1))) := Fintype.ofFinite _
  have hq := CFSG.RankThree.PartTwo.Sec8.Item87Proof.isQuasisimple_statedSU_three
    (F := GaloisField 2 (2 * (2 * 1 + 1))) (f := 2 * 1 + 1) hF (by norm_num)
  let H := StatedSU 3 (2 ^ (2 * 1 + 1)) (GaloisField 2 (2 * (2 * 1 + 1)))
  have hqO : CFSG.Open.IsQuasisimple ↥H :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.open_isQuasisimple hq.1
  haveI hPerf : Group.IsPerfect ↥H := ⟨hqO.1⟩
  haveI hSimpProj : IsSimpleGroup (StatedProj H) :=
    CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU
      (GaloisField 2 (2 * (2 * 1 + 1))) 2 3 hF 3 (by norm_num) (by norm_num)
  have hZ := CFSG.LieType.Universal.Spin.center_eq_statedScalars_subgroupOf (H := H)
  let E : ↥(fixSubgroup (MulAut.conj y)) ≃* ↥H :=
    (MulEquiv.subgroupCongr (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup_conj y)).trans e
  have hXq : CFSG.Open.IsQuasisimple ↥(fixSubgroup (MulAut.conj y)) :=
    CFSG.Open.IsQuasisimple.of_mulEquiv E hqO
  let eXZ : (↥(fixSubgroup (MulAut.conj y)) ⧸ Subgroup.center ↥(fixSubgroup (MulAut.conj y))) ≃*
      (↥H ⧸ Subgroup.center ↥H) :=
    QuotientGroup.congr _ _ E (Subgroup.map_center_eq E)
  let eZ : (↥H ⧸ Subgroup.center ↥H) ≃* StatedProj H := QuotientGroup.quotientMulEquivOfEq hZ
  have hv := rf4_twistedA_valid
  haveI hfact : Fact (Nat.Prime (TauCeti.ValidLieTypeIndex.characteristic
      ⟨TauCeti.LieTypeIndex.twistedA 2 rf4Q8, hv⟩)) :=
    ⟨by simpa [TauCeti.ValidLieTypeIndex.characteristic, rf4Q8] using Nat.prime_two⟩
  obtain ⟨eU⟩ := rf4_u3_stated_iso (c := TauCeti.ValidLieTypeIndex.characteristic
      ⟨TauCeti.LieTypeIndex.twistedA 2 rf4Q8, hv⟩)
    (fe := TauCeti.ValidLieTypeIndex.fieldExponent ⟨TauCeti.LieTypeIndex.twistedA 2 rf4Q8, hv⟩)
    (by simp [TauCeti.ValidLieTypeIndex.characteristic, rf4Q8])
    (by simp [TauCeti.ValidLieTypeIndex.fieldExponent, rf4Q8])
    (CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj 2 rf4Q8 hv)
  have hk : catalogIs (↥(fixSubgroup (MulAut.conj y)) ⧸ Subgroup.center ↥(fixSubgroup (MulAut.conj y)))
      (k2 3) :=
    ⟨TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.twistedA 2 rf4Q8, hv⟩,
      by simp [k2, k2Lie, rf4Q8, Nat.odd_iff], ⟨(eXZ.trans eZ).trans eU.symm⟩⟩
  have hlev := rf4_kLevel_le_two hk
  intro I hI
  have hIeq : I = fixSubgroup (MulAut.conj y) := rf4_eq_of_glaPComponent hI hXq
  subst hIeq
  obtain ⟨f⟩ := rf4_pSimple_equiv_center Nat.prime_three hI hXq
  rw [kLevel_congr 3 f]
  exact hlev

theorem rf4_downLe_three (K : Type) [Field K] [Finite K] [CharP K ReeTag.F4.prime]
    (hK : Nat.card K = 2 ^ (2 * 1 + 1)) (hk : kLevel 3 (ReeTag.F4.reeGamma K 1) ≤ 2) :
    DownLe 3 2 (ReeTag.F4.reeGamma K 1) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hsimp : IsSimpleGroup (ReeTag.F4.reeGamma K 1) :=
    CFSG.SignalizerFunctorTheorem.CatalogBridge.isSimpleGroup_reeGamma_F4 le_rfl hK
  haveI : Finite (ReeTag.F4.reeGamma K 1) := Subtype.finite
  have hΓ := (CFSG.RankThree.LargeReeOrder.large_Ree_exact_native_order_and_prime_factor_exhaustion
    1 K hK).1
  have hdvd : 3 ∣ Nat.card (ReeTag.F4.reeGamma K 1) := by
    rw [hΓ]
    norm_num
  have hnc : ∃ a b : ReeTag.F4.reeGamma K 1, a * b ≠ b * a := by
    apply rf4_nonab_of_not_prime
    intro hp
    have h2 : 2 ∣ Nat.card (ReeTag.F4.reeGamma K 1) := by
      rw [hΓ]
      norm_num
    rcases hp.eq_one_or_self_of_dvd 2 h2 with h | h
    · norm_num at h
    · rw [hΓ] at h
      norm_num at h
  intro α hα I hI
  by_cases h1 : α = 1
  · subst h1
    exact rf4_claim_one Nat.prime_three hnc hdvd hk I hI
  · rcases CFSG.HardMathSupport.Solomon.Coordinator.LieComp.reeF4_inner_or_field (a := 1) le_rfl hK Nat.prime_three hα h1 with
      ⟨y, rfl, hy3, hy1⟩ | ⟨σ, g, hσ, rfl⟩
    · exact rf4_u3_level hK y (orderOf_eq_prime hy3 hy1) I hI
    · rw [show MulAut.conj g * ReeTag.F4.reeGammaFieldAut K 1 σ * (MulAut.conj g)⁻¹ =
          MulAut.congr (MulAut.conj g : ReeTag.F4.reeGamma K 1 ≃* ReeTag.F4.reeGamma K 1)
            (ReeTag.F4.reeGammaFieldAut K 1 σ) from (rf4_congr_self _ _).symm] at hI
      exact rf4_claim_congr Nat.prime_three
        (MulAut.conj g : ReeTag.F4.reeGamma K 1 ≃* ReeTag.F4.reeGamma K 1) _
        (rf4_claim_field hK Nat.prime_three (by norm_num) (by norm_num) (Or.inl rfl) σ hσ) I hI

theorem kdLieRowReeF4EightThree_holds :
    KDLieRowReeF4EightThree := by
  unfold KDLieRowReeF4EightThree
  intro hv
  have hR := CFSG.HardMathSupport.Timmesfeld.DefChar.lot_reeTitsModel_twistedF4_of_index 1 hv
    (MulEquiv.refl _)
  obtain ⟨-, a, ha, hfa, K, _, _, _, hK, ⟨e⟩⟩ :=
    CFSG.RankThree.PartTwo.Sec4.exists_mulEquiv_reeGamma hR
  obtain rfl : a = 1 := by omega
  have hk : kLevel 3 (ReeTag.F4.reeGamma K 1) ≤ 2 := by
    rw [← kLevel_congr 3 e]
    exact rf4_kLevel_le_two ⟨TauCeti.CFSGIndex.lie ⟨.reeF4 1, hv⟩, by simp [k2, k2Lie],
      ⟨MulEquiv.refl _⟩⟩
  exact downLe_of_mulEquiv e.symm (rf4_downLe_three K hK hk)

end CFSG.LocalAnalysis.GLTheoremA
