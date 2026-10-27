module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58bExc
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBTypeInputs
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.ClassicalGroups
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalIsogeny
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Conj
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Export
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Roots
public import CFSG.ClassicalInvolution.ModelFacts.FundPerfectMain
public import CFSG.ClassicalInvolution.Models.LinearFrames
public import CFSG.ClassicalInvolution.Models.LinearPairs
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Quadruple
public import CFSG.ClassicalInvolution.Models.UnitaryPairs
public import CFSG.ClassicalInvolution.Models.UnitaryPairs.Pairs
public import CFSG.GH74.GLS.Classes
public import CFSG.GH74.Generic.Shapes
public import CFSG.GH74.Statements
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LieType.Ree.SmallReeInvolutionComponents
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBL2Reduction
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofF4Inner
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddRee
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddTrialityInner
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofTwE6Inner
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorOddE6
public import CFSG.LocalAnalysis.ComponentClassification.GSFMMaximal
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeSteps
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitFrontier46
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitKGFieldClass
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLit39b
public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorInner
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTILinearSocle
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.Sol78Seven
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSLAllInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSUFieldOddCore
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCriticalStandard
public import CFSG.LocalAnalysis.ComponentInitial.ProjectiveEigenspaceComponent
public import CFSG.LocalAnalysis.ComponentInitial.ProjectiveOrthogonalLocalComponentSplit
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPreimages
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFourPresentation
public import CFSG.LocalAnalysis.SectionRank.BruhatLift
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd
public import CFSG.LocalAnalysis.SectionRank.EvenCover.LinearStep
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SLTwo
public import CFSG.LocalAnalysis.SectionRank.LargeReeCover
public import CFSG.LocalAnalysis.SignalizerFunctor
public import CFSG.LocalAnalysis.SteinbergCEOddResidualE6Graph
public import CFSG.Open.GorensteinHaradaSectionalRankFourMilestoneDefs
public import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl
public import CFSG.RankThree.PartOne.KC.OrthogonalAutSemilinearBridge
public import CFSG.RankThree.PartOne.KC.OrthogonalFieldDescentCore
public import CFSG.RankThree.PartOne.KC.OrthogonalFieldDescentDisplayed
public import CFSG.RankThree.PartOne.KC.OrthogonalFieldDescentTags
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeOrbits
public import CFSG.RankThree.SteinbergR3EOrthogonalCoprimeCyclic
public import CFSG.Sporadic.Schreier.TitsOther
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup Assembly.LowTwoRank Blueprint CFSG.LocalAnalysis.ComponentInitial
open scoped MatrixGroups

namespace P58b

variable {X : Type} [Group X] [Finite X]

theorem autFixed_conj {G : Type*} [Group G] (x : G) :
    TBLit.autFixed (MulAut.conj x) = centralizer {x} := by
  ext g
  rw [mem_centralizer_singleton_iff]
  change MulAut.conj x g = g ↔ g * x = x * g
  rw [MulAut.conj_apply]
  constructor
  · intro h
    calc g * x = x * g * x⁻¹ * x := by rw [h]
      _ = x * g := by group
  · intro h
    calc x * g * x⁻¹ = g * x * x⁻¹ := by rw [h]
      _ = g := by group

theorem admissible_of_lieModel {G : Type} [Group G] {τ : StatedLieTag} {n p f : ℕ}
    (h : LieModel G τ n p f) : StatedLieAdmissible τ n p f :=
  CFSG.Blueprint.LieModel.admissible h

theorem false_of_cover_center_pow (hX : IsQuasisimple X) (h2 : IsPGroup 2 (center X)) {c : X}
    (hcZ : c ∈ center X) (hc2 : orderOf c = 2) {G : Type} [Group G] [Finite G]
    (hG : IsQuasisimple G)
    (hsplit : ∀ (E : Type) [Group E] [Finite E] (π : E →* G),
      Function.Surjective π → π.ker ≤ center E → IsPGroup 2 π.ker →
        ∃ s : G →* E, ∀ x, π (s x) = x)
    (β : G →* X ⧸ center X) (hβ : Function.Surjective β) {m : ℕ} (hm : Odd m)
    (hZ : ∀ z ∈ center G, z ^ m = 1) : False := by
  have : Group.IsPerfect X := hX.1
  have hη : (QuotientGroup.mk' (center X)).ker = center X := QuotientGroup.ker_mk' _
  obtain ⟨α, -, -, hker⟩ := CFSG.LieType.Steinberg.exists_surjective_of_isPerfect hsplit hβ
    (QuotientGroup.mk'_surjective (center X)) hη.le (by rw [hη]; exact h2)
  have hnt : ∃ g, β g ≠ 1 := by
    obtain ⟨a, b, hab⟩ := hX.2.2
    by_contra hall
    have hall' : ∀ g, β g = 1 := fun g => by
      by_contra h
      exact hall ⟨g, h⟩
    apply hab
    obtain ⟨a, rfl⟩ := hβ a
    obtain ⟨b, rfl⟩ := hβ b
    rw [hall' a, hall' b]
  have hβZ := CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple hG hnt
  rw [← hη, hker] at hcZ
  obtain ⟨z, hz, rfl⟩ := hcZ
  have hcm : α z ^ m = 1 := by rw [← map_pow, hZ z (hβZ hz), map_one]
  have hdvd := orderOf_dvd_of_pow_eq_one hcm
  rw [hc2] at hdvd
  exact (Nat.not_even_iff_odd.2 hm) (even_iff_two_dvd.2 hdvd)

end P58b

open P58b

theorem noConfig_classicalS (hcl : Burgoyne.BurgoynePropBClassicalS) {τ : StatedLieTag} {n : ℕ}
    (hτ : ((τ = .PSL ∨ τ = .PSU) ∧ 6 ≤ n ∧ Even n) ∨ (τ = .PSp ∧ 3 ≤ n)) :
    Harris82Lemma58bNoConfig τ n := by
  intro X _ _ hX _ p f hp hp2 hm k c t Q hcfg
  have : Fact p.Prime := ⟨hp⟩
  have h5 : 5 ≤ p ^ k := hcfg.2.2.2.2.2.2.1
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with rfl | h
    · simp at h5
    · exact h
  have hZS := center_quotient_eq_bot hX
  obtain ⟨hxx, hx1, hRv, hRc, N, hN, hNodd, ⟨eN⟩⟩ := exists_psl2_component hX
    (QuotientGroup.mk' (center X)) (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    hp2 hcfg
  have hv2 : orderOf (MulAut.conj (QuotientGroup.mk' (center X) t)) = 2 := by
    apply orderOf_eq_prime
    · rw [pow_two, ← map_mul, hxx, map_one]
    · intro h1
      apply hx1
      have hxZ : QuotientGroup.mk' (center X) t ∈ center (X ⧸ center X) := by
        rw [mem_center_iff]
        intro g
        have h2 : QuotientGroup.mk' (center X) t * g * (QuotientGroup.mk' (center X) t)⁻¹ = g :=
          by
            have h3 := DFunLike.congr_fun h1 g
            rwa [MulAut.conj_apply, MulAut.one_apply] at h3
        calc g * QuotientGroup.mk' (center X) t =
              QuotientGroup.mk' (center X) t * g * (QuotientGroup.mk' (center X) t)⁻¹ *
                QuotientGroup.mk' (center X) t := by rw [h2]
          _ = QuotientGroup.mk' (center X) t * g := by group
      rw [hZS, mem_bot] at hxZ
      exact hxZ
  have hfix := autFixed_conj (QuotientGroup.mk' (center X) t)
  exact hcl (X ⧸ center X) τ n p f hτ hp2 hm _ hv2 (Q.map (QuotientGroup.mk' (center X)))
    (by rw [hfix]; exact hRv) (by rw [hfix]; exact hRc) p k hp2 hk N hNodd ⟨eN⟩

theorem noConfig_PSL_odd {n : ℕ} (hodd : Odd n) : Harris82Lemma58bNoConfig .PSL n := by
  intro X _ _ hX hO p f hp hp2 hm k c t Q hcfg
  obtain ⟨hc2, hcZ, -⟩ := hcfg
  obtain ⟨-, -, hn2, -⟩ := admissible_of_lieModel hm
  obtain ⟨F, _, _, hFc, ⟨θ⟩⟩ := LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hm
  have : Fintype F := Fintype.ofFinite F
  have : Fact p.Prime := ⟨hp⟩
  have : CharP F p := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
  have hF : ringChar F ≠ 2 := by rw [ringChar.eq F p]; exact hp2
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hn3 : 3 ≤ m + 1 := by obtain ⟨j, hj⟩ := hodd; omega
  have hG := CatalogueBGeneralLinear.specialLinear_quasisimple (m + 1) F (by omega)
    (Or.inl (by omega)) (Or.inl (by omega))
  refine false_of_cover_center_pow hX (Sol78.center_isPGroup_two hO) hcZ hc2 hG ?_
    (θ.symm.toMonoidHom.comp (LinearFlag.proj (m + 1) F))
    (θ.symm.surjective.comp (LinearFlag.proj_surjective (m + 1) F)) hodd ?_
  · intro E _ _ π hπ hker h2
    obtain ⟨s, hs, -⟩ := CFSG.LieType.Steinberg.sl_central_two_extension_splitting m hF hπ hker h2
    exact ⟨s, hs⟩
  · intro z hz
    obtain ⟨r, hr, hrz⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hz
    rw [Fintype.card_fin] at hr
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, ← hrz, ← map_pow, hr, map_one,
      Matrix.SpecialLinearGroup.coe_one]

theorem noConfig_PSU_odd {n : ℕ} (hodd : Odd n) : Harris82Lemma58bNoConfig .PSU n := by
  intro X _ _ hX hO p f hp hp2 hm k c t Q hcfg
  obtain ⟨hc2, hcZ, -⟩ := hcfg
  rcases hm with ⟨-, hcl⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩
  rotate_left
  · exact absurd htag (by decide)
  · exact absurd htag (by decide)
  · exact absurd htag (by decide)
  obtain ⟨⟨hp', hf, hn3, -⟩, K₀, _, _, hKc, ⟨θ⟩⟩ := hcl
  have h : UnitaryFieldData p f K₀ := ⟨hp', hf, by rw [hKc, ← pow_mul, mul_comm]⟩
  have : Fact p.Prime := ⟨hp'⟩
  have := h.charP
  have hnq : (n, p ^ f) ≠ (3, 2) := by
    intro h32
    have h2 : p ^ f = 2 := congrArg Prod.snd h32
    have hp2' : p ∣ 2 := h2 ▸ dvd_pow_self p (by omega)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp' Nat.prime_two).1 hp2')
  obtain ⟨hG, hZG⟩ := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card
    h.card_eq_sq hn3 hnq
  refine false_of_cover_center_pow hX (Sol78.center_isPGroup_two hO) hcZ hc2 hG
    (Burgoyne.B.statedSU_central_two_splitting h.card_eq_sq hp2 (by omega))
    (θ.symm.toMonoidHom.comp (Burgoyne.Proj.projH _))
    (θ.symm.surjective.comp Burgoyne.Proj.projH_surjective) hodd ?_
  intro z hz
  rw [hZG, mem_subgroupOf] at hz
  obtain ⟨r, hr⟩ := hz
  have hdet := CFSG.LieType.Universal.Unitary.det_eq_one_of_mem_statedSU z.2
  have hzr : ((z : GL (Fin n) K₀) : Matrix (Fin n) (Fin n) K₀) =
      Matrix.scalar (Fin n) (r : K₀) := by
    have h' := congrArg Units.val hr
    rw [Matrix.GeneralLinearGroup.coe_scalar] at h'
    exact h'.symm
  rw [hzr, Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin] at hdet
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hzr, ← map_pow, hdet, map_one, Subgroup.coe_one,
    Units.val_one]

theorem noConfig_PSL_two : Harris82Lemma58bNoConfig .PSL 2 := by
  intro X _ _ hX hO p f hp hp2 hm k c t Q hcfg
  obtain ⟨hc2, hcZ, ht2, htZ, -⟩ := hcfg
  have : Group.IsPerfect X := hX.1
  obtain ⟨-, hf, -, -, h23⟩ := admissible_of_lieModel hm
  obtain ⟨F, _, _, hFc, ⟨θ⟩⟩ := LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hm
  have : Fintype F := Fintype.ofFinite F
  have : Fact p.Prime := ⟨hp⟩
  have : CharP F p := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
  have hF : ringChar F ≠ 2 := by rw [ringChar.eq F p]; exact hp2
  have hF2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  have hq2 : Nat.card F ≠ 2 := by
    intro h
    rw [hFc] at h
    have hp2' : p ∣ 2 := h ▸ dvd_pow_self p (by omega)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 hp2')
  have hq3 : Nat.card F ≠ 3 := by
    intro h
    rw [hFc] at h
    exact h23 (by rw [h])
  have hG := CatalogueBGeneralLinear.specialLinear_quasisimple 2 F le_rfl (Or.inr hq2)
    (Or.inr hq3)
  have hsplit : ∀ (E : Type) [Group E] [Finite E] (π : E →* SL(2, F)),
      Function.Surjective π → π.ker ≤ center E → IsPGroup 2 π.ker →
        ∃ s : SL(2, F) →* E, ∀ x, π (s x) = x := fun E _ _ π hπ hker h2 => by
    obtain ⟨s, hs, -⟩ := CFSG.LieType.Steinberg.sl_central_two_extension_splitting 1 hF hπ hker h2
    exact ⟨s, hs⟩
  set β : SL(2, F) →* X ⧸ center X := θ.symm.toMonoidHom.comp (LinearFlag.proj 2 F)
  have hβ : Function.Surjective β := θ.symm.surjective.comp (LinearFlag.proj_surjective 2 F)
  have hη : (QuotientGroup.mk' (center X)).ker = center X := QuotientGroup.ker_mk' _
  obtain ⟨α, hαβ, hαs, hker⟩ := CFSG.LieType.Steinberg.exists_surjective_of_isPerfect hsplit hβ
    (QuotientGroup.mk'_surjective (center X)) hη.le
    (by rw [hη]; exact Sol78.center_isPGroup_two hO)
  have hnt : ∃ g, β g ≠ 1 := by
    obtain ⟨a, b, hab⟩ := hX.2.2
    by_contra hall
    have hall' : ∀ g, β g = 1 := fun g => by
      by_contra h
      exact hall ⟨g, h⟩
    apply hab
    obtain ⟨a, rfl⟩ := hβ a
    obtain ⟨b, rfl⟩ := hβ b
    rw [hall' a, hall' b]
  have hβZ := CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple hG hnt
  have hpm : ∀ z ∈ β.ker, z = 1 ∨ z = -1 := fun z hz =>
    Burgoyne.C.eq_one_or_eq_neg_one hF2 z (by
      rw [← pow_two]; exact Burgoyne.C.sq_eq_one_of_mem_center_SL (hβZ hz))
  have hc : c ∈ β.ker.map α := by rw [← hker, hη]; exact hcZ
  obtain ⟨z, hz, hzc⟩ := hc
  have hc1 : c ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hc2
    exact absurd hc2 (by norm_num)
  have hneg : α (-1) = c := by
    rcases hpm z hz with rfl | rfl
    · rw [map_one] at hzc
      exact absurd hzc.symm hc1
    · exact hzc
  obtain ⟨g, rfl⟩ := hαs t
  have hg2 : g * g = 1 := by
    have hα2 := pow_orderOf_eq_one (α g)
    rw [ht2] at hα2
    have h1 : α (g * g) = 1 := by
      rw [map_mul, ← pow_two, hα2]
    have h2 : g * g ∈ β.ker := by
      rw [MonoidHom.mem_ker, ← hαβ, h1, map_one]
    rcases hpm _ h2 with h3 | h3
    · exact h3
    · exfalso
      rw [h3, hneg] at h1
      exact hc1 h1
  rcases Burgoyne.C.eq_one_or_eq_neg_one hF2 g hg2 with rfl | rfl
  · rw [map_one] at htZ
    exact htZ (one_mem _)
  · rw [hneg] at htZ
    exact htZ hcZ

end CFSG.ComponentClassification.HarrisLit.T1
