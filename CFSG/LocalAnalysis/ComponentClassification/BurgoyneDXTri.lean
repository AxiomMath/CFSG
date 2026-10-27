module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneDXTriRoots
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneDXFamily
public import CFSG.LieType.Steinberg.PartBProof
public import CFSG.ClassicalInvolution.Asc77.Lemma310
public import CFSG.ClassicalInvolution.Asc77.ThmEStatement
public import CFSG.ClassicalInvolution.Asc77.WP1Section18
public import CFSG.ClassicalInvolution.Asc77.WP1Section6
public import CFSG.ClassicalInvolution.Balance.QNineFuzzyFree
public import CFSG.ClassicalInvolution.Balance.Theorem5Models
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalIsogeny
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Conj
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Roots
public import CFSG.ClassicalInvolution.ModelFacts.D4RigidFrame
public import CFSG.ClassicalInvolution.ModelFacts.Orth15Std
public import CFSG.LocalAnalysis.ComponentClassification.BadTwoComponentSubgroup
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPreimages
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
public import CFSG.LocalAnalysis.SignalizerFunctor
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldPrimeOrderFixedSubfield
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OrderThreeNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PSLRangeCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinInvolutionCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinUDecomposition
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationEleven
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTen
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTenStructuralIdentities
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2FieldProjectionArithmetic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2OrderPSubgroupCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphReconstruction
public import Certificates.Certificate1
public import Certificates.Certificate10
public import Certificates.Certificate11
public import Certificates.Certificate12
public import Certificates.Certificate2
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate42
public import Certificates.Certificate44
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate8
public import Certificates.Certificate9

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.DX.Tri

open CFSG.LieType.Universal.Spin CFSG.LieType.Steinberg CFSG.LieType.Steinberg.SpinPlus
open CFSG.LieType.Steinberg.SpinFrame CFSG.LieType.CurtisTits
open CFSG.ClassicalInvolution.G2D4Models.Twin
open scoped commutatorElement

theorem le34 : 3 ≤ 4 := by norm_num

variable (F : Type) [Field F]

@[expose] noncomputable def ordD : CommOrder (Φ 4 F le34) := by
  classical
  exact
  { list := fun α β => if α + β ∈ (Φ 4 F le34).roots then [(1, 1)] else []
    nodup := fun α β => by split_ifs <;> simp
    mem_iff := fun α hα β hβ hαβ p => by
      rw [Orthogonal.mem_expPairs_D (by norm_num) (Φ_roots _) hα hβ hαβ p]
      split_ifs with h <;> simp [h] }

variable {F}

@[expose] def yT (γ : Fin 4 → ℤ) (c : F) : spinGroup (quadPlus 4 F) :=
  x 4 F le34 (piT γ) ((epsT γ : F) * c)

theorem piT_mem_roots {γ : Fin 4 → ℤ} (hγ : γ ∈ (Φ 4 F le34).roots) :
    piT γ ∈ (Φ 4 F le34).roots :=
  (mem_roots_iff _).2 (piT_mem γ ((mem_roots_iff _).1 hγ))

theorem yT_add : ∀ γ ∈ (Φ 4 F le34).roots, ∀ c d : F,
    yT γ (c + d) = yT γ c * yT γ d := by
  intro γ hγ c d
  unfold yT
  rw [mul_add]
  exact ((isParametrization le34) _ (piT_mem_roots hγ)).2.1 _ _

theorem yT_comm (O : CommOrder (Φ 4 F le34)) :
    CommutatorFormula (yT (F := F)) O (commC (n := 4)) := by
  intro α hα β hβ hαβ c d
  have hα' := (mem_roots_iff (K := F) le34).1 hα
  have hβ' := (mem_roots_iff (K := F) le34).1 hβ
  have hπα := piT_mem_roots hα
  have hπβ := piT_mem_roots hβ
  have hπαβ : piT α + piT β ≠ 0 := fun h => hαβ (piT_injective (by rw [piT_add, h]; rfl))
  have key := commutatorFormula le34 O (piT α) hπα (piT β) hπβ hπαβ
    ((epsT α : F) * c) ((epsT β : F) * d)
  unfold yT
  rw [key]
  by_cases hr : α + β ∈ (Φ 4 F le34).roots
  · have hr' : piT α + piT β ∈ (Φ 4 F le34).roots := by
      rw [← piT_add]
      exact piT_mem_roots hr
    rw [(commOrder_list_eq _ O hπα hπβ hπαβ).1 hr', (commOrder_list_eq _ O hα hβ hαβ).1 hr]
    simp only [List.map_singleton, List.prod_singleton, one_smul, pow_one]
    rw [← piT_add]
    congr 1
    have h := commC_piT hα' hβ' ((mem_roots_iff (K := F) le34).1 hr) (1, 1) (1, 1)
    have h' : ((commC (piT α) (piT β) (1, 1) * epsT α * epsT β : ℤ) : F) =
        ((epsT (α + β) * commC α β (1, 1) : ℤ) : F) := by rw [h]
    push_cast at h'
    linear_combination (c * d) * h'
  · have hr' : piT α + piT β ∉ (Φ 4 F le34).roots := fun h => hr (by
      have := piT_mem_roots (F := F) (piT_mem_roots h)
      rw [← piT_add, piT_piT_piT] at this
      exact this)
    rw [(commOrder_list_eq _ O hπα hπβ hπαβ).2 hr', (commOrder_list_eq _ O hα hβ hαβ).2 hr]
    simp

variable (F) [Finite F]

theorem finite_spin : Finite (spinGroup (quadPlus 4 F)) :=
  CFSG.LieType.Steinberg.finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadPlus (n := 4))

theorem pres_spec : ∃ h : ∀ r ∈ relA (Φ 4 F le34) F ∪
      relB (Φ 4 F le34) F (ordD F) (commC (n := 4)),
      FreeGroup.lift (chevEval (x 4 F le34)) r = 1,
    Function.Bijective (PresentedGroup.toGroup h) :=
  (presentationB le34 (ordD F)).2 (commC (n := 4)) (commutatorFormula le34 (ordD F))

@[expose] def rho0 : spinGroup (quadPlus 4 F) →* spinGroup (quadPlus 4 F) :=
  (PresentedGroup.toGroup (chevEval_rels (Φ := Φ 4 F le34) yT_add (yT_comm (ordD F)))).comp
    (MulEquiv.ofBijective _ (pres_spec F).snd).symm.toMonoidHom

variable {F}

theorem rho0_x {γ : Fin 4 → ℤ} (hγ : γ ∈ (Φ 4 F le34).roots) (c : F) :
    rho0 F (x 4 F le34 γ c) = yT γ c := by
  have h : (MulEquiv.ofBijective _ (pres_spec F).snd).symm (x 4 F le34 γ c) =
      PresentedGroup.of (⟨γ, hγ⟩, c) := by
    rw [MulEquiv.symm_apply_eq, MulEquiv.ofBijective_apply, PresentedGroup.toGroup.of]
    rfl
  rw [rho0, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h, PresentedGroup.toGroup.of]
  rfl

theorem x_piT_eq {γ : Fin 4 → ℤ} (hγ : γ ∈ (Φ 4 F le34).roots) (c : F) :
    x 4 F le34 (piT γ) c = rho0 F (x 4 F le34 γ ((epsT γ : F) * c)) := by
  rw [rho0_x hγ, yT, ← mul_assoc, ← Int.cast_mul, epsT_mul_self, Int.cast_one, one_mul]

variable (F)

theorem rho0_surjective : Function.Surjective (rho0 F) := by
  rw [← MonoidHom.range_eq_top, eq_top_iff, ← plusDatum_iSup_eq_top 4 F le34]
  refine iSup₂_le fun γ hγ => ?_
  intro g hg
  have hγ₀ : piT (piT γ) ∈ (Φ 4 F le34).roots := piT_mem_roots (piT_mem_roots hγ)
  obtain ⟨c, rfl⟩ := (((isParametrization le34) γ hγ).1 g).1 hg
  have e := x_piT_eq hγ₀ c
  rw [piT_piT_piT] at e
  rw [e]
  exact ⟨_, rfl⟩

@[expose] def rhoT : Sp8 F ≃* Sp8 F :=
  have := finite_spin F
  MulEquiv.ofBijective (rho0 F) ⟨Finite.injective_iff_surjective.2 (rho0_surjective F),
    rho0_surjective F⟩

variable {F}

theorem map_rootGroup {γ : Fin 4 → ℤ} (hγ : γ ∈ (Φ 4 F le34).roots) :
    ((plusDatum 4 F le34).rootGroup γ).map (rho0 F) =
      (plusDatum 4 F le34).rootGroup (piT γ) := by
  have hπ := piT_mem_roots hγ
  ext g
  constructor
  · rintro ⟨h, hh, rfl⟩
    obtain ⟨c, rfl⟩ := (((isParametrization le34) γ hγ).1 h).1 hh
    rw [rho0_x hγ]
    exact (((isParametrization le34) (piT γ) hπ).1 _).2 ⟨_, rfl⟩
  · intro hg
    obtain ⟨c, rfl⟩ := (((isParametrization le34) (piT γ) hπ).1 g).1 hg
    exact ⟨_, (((isParametrization le34) γ hγ).1 _).2 ⟨_, rfl⟩, (x_piT_eq hγ c).symm⟩

variable (F)

theorem isTriality_rhoT : IsTriality (rhoT F) := by
  intro k
  have hs : (Pi.single k 1 : Fin 4 → ℤ) ∈ (Φ 4 F le34).roots :=
    (Φ 4 F le34).single_mem k
  have hns : (-Pi.single k 1 : Fin 4 → ℤ) ∈ (Φ 4 F le34).roots :=
    (mem_roots_iff (K := F) le34).2 (by
      have := (mem_roots_iff (K := F) le34).1 hs
      revert this
      fin_cases k <;> decide)
  change Subgroup.map (rho0 F) ((plusDatum 4 F le34).rootGroup (Pi.single k 1) ⊔
      (plusDatum 4 F le34).rootGroup (-Pi.single k 1)) =
    (plusDatum 4 F le34).rootGroup (Pi.single (triPerm k) 1) ⊔
      (plusDatum 4 F le34).rootGroup (-Pi.single (triPerm k) 1)
  rw [Subgroup.map_sup]
  have e1 := map_rootGroup (F := F) hs
  have e2 := map_rootGroup (F := F) hns
  rw [piT_single] at e1
  rw [piT_neg, piT_single] at e2
  exact congrArg₂ (· ⊔ ·) e1 e2

theorem exists_triality_spin : ∃ ρ : Sp8 F ≃* Sp8 F, IsTriality ρ :=
  ⟨rhoT F, isTriality_rhoT F⟩

theorem d4TrialityThreeInput_holds : D4TrialityThreeInput :=
  exists_triality_spin (GaloisField 3 1)

end CFSG.ComponentClassification.Burgoyne.DX.Tri
