module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.H1429SubCore
public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.ExcTriThree
public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.ExcTriClassA
public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.ExcTriClassB
public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.ExcUntwisted
import CFSG.RankThree.PartOne.KGD.D4T36Core
public import CFSG.LieType.Chevalley.EvenOddCentralizerRadicalModel
public import CFSG.LieType.Multipliers.U62Sylow
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcF4O2
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreEven
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreL34
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreRes
public import CFSG.LocalAnalysis.GLTheoremA.CatA.H1429SubRed
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporRows
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431Defs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011I1416Small
public import CFSG.LocalAnalysis.GLTheoremA.S10.Bridge
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs105
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsBeta
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsSetup
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs16
public import CFSG.LocalAnalysis.GLTheoremA.S11.InputsCE
public import CFSG.LocalAnalysis.GLTheoremA.S11.InputsElim
public import CFSG.LocalAnalysis.SeitzReduction.CrossCharInputs
public import CFSG.LocalAnalysis.SeitzReduction.RankOneBranches
public import CFSG.LocalAnalysis.SeitzReduction.RankOneHypStarDef
public import CFSG.Quasithin.Vol2.Ch5Sec1L34FiveA7
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4SpA

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1429Sub

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.Yardstones.Md0ec50421ce4
  CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3
  CFSG.HardMathSupport.Lang.Triality
  CFSG.GH74.GLS.Stage2.Bender.Thm1 CFSG.HardMathSupport.Dickson.Sec6.I923
  CFSG.HardMathSupport.Dickson.Sec6.I923.TriD4Aux
open CFSG.HardMathSupport.Dickson.DefCharOuter.Export

@[expose] def NoU42At {T : Type} [Group T] (γ : MulAut T) : Prop :=
  ∀ I : Subgroup T, GLAPComponent 3 (fixSubgroup γ) I → Nat.card (PSimple 3 I) ≠ 25920

theorem NoU42At.of_conj {T : Type} [Group T] [Finite T] (ε β : MulAut T)
    (h : NoU42At (ε * β * ε⁻¹)) : NoU42At β := by
  intro I hI hc
  obtain ⟨hI', ⟨e⟩⟩ := component_transport (ε : T ≃* T) (β := β) (a := ε * β * ε⁻¹)
    (by ext x; rfl) hI
  exact h _ hI' ((Nat.card_congr e.toEquiv).symm.trans hc)

theorem NoU42At.of_inv {T : Type} [Group T] {β : MulAut T} (h : NoU42At β⁻¹) : NoU42At β := by
  intro I hI
  exact h I (by rwa [exc_fixSubgroup_inv])

theorem NoU42At.of_noComponent {T : Type} [Group T] {γ : MulAut T}
    (h : ∀ I : Subgroup T, ¬ GLAPComponent 3 (fixSubgroup γ) I) : NoU42At γ :=
  fun I hI => (h I hI).elim


section ClassA

variable {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] [CharP K 3]
  (hK : Nat.card K = (3 ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (3 ^ f))
include hf hK hσ

theorem noU42At_classA : NoU42At (fieldActor (t := TwistTag.D4) σ σ) := by
  classical
  intro I hI hc
  haveI := finite_graphFixedRootGroup_D4 σ
  have hs := isSimpleGroup_fixSubgroup_fieldActor_D4 3 f Nat.prime_three (by norm_num) K hK σ hσ
  have hnab := nonabelian_fixSubgroup_fieldActor_D4 3 f Nat.prime_three (by norm_num) K hK σ hσ
  let e := ExcTriClassA.fixSubgroupFieldActorEquivG2 Nat.prime_three (by norm_num) hf hK σ hσ
  have hkcard : Nat.card (fixSubfield σ) = 3 ^ f :=
    CFSG.RankThree.PartOne.KGD.card_fixSubfield_cube Nat.prime_three hf hK σ hσ
  have hsix := ExcUntwisted.card_pow_six_dvd Tag.G2 (Or.inl rfl) (fixSubfield σ)
  rw [hkcard] at hsix
  have hdvd : 3 ∣ Nat.card (fixSubgroup (fieldActor (t := TwistTag.D4) σ σ)) := by
    rw [Nat.card_congr e.toEquiv]
    exact ((dvd_pow_self 3 (by omega)).trans (dvd_pow_self _ (by norm_num))).trans hsix
  haveI hnorm := normal_subgroupOf_self (fixSubgroup (fieldActor (t := TwistTag.D4) σ σ))
  obtain ⟨e'⟩ := exists_equiv_of_conj (MulEquiv.refl _) (β := fieldActor (t := TwistTag.D4) σ σ)
    (a := fieldActor (t := TwistTag.D4) σ σ) rfl (J := fixSubgroup (fieldActor (t := TwistTag.D4) σ σ))
    le_rfl (isSolvable_quotient_self _) hs hnab hdvd hI
  have hcard : Nat.card (PSimple 3 I) = Nat.card (adjointGroup Tag.G2 (fixSubfield σ)) :=
    Nat.card_congr (e'.trans e).toEquiv
  rw [hc] at hcard
  rw [← hcard] at hsix
  have h729 : 3 ^ 6 ∣ 25920 := (pow_dvd_pow_of_dvd (dvd_pow_self 3 (by omega)) 6).trans hsix
  norm_num at h729

theorem noU42At_trialityD4_three
    (β : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) (hβ3 : β ^ 3 = 1)
    (hout : β ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) : NoU42At β := by
  classical
  haveI := finite_graphFixedRootGroup_D4 σ
  exact three_of_classes_gen hf hK σ hσ (fun γ => NoU42At γ)
    (fun ε γ h => NoU42At.of_conj ε γ h) (fun γ h => NoU42At.of_inv h)
    (noU42At_classA hf hK σ hσ)
    (fun hc hc0 => NoU42At.of_noComponent (exc_noComponent_classB hf hK σ hσ hc hc0)) β hβ3 hout

end ClassA

end CFSG.LocalAnalysis.GLTheoremA.H1429Sub

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.H1429Sub
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Dickson.DefCharOuter.Export


theorem i1429SubTri_holds : I1429SubLieAt SubIsTri := by
  intro S _ _ hS hnc d hchar ⟨q, hd⟩ ⟨e⟩ β hβ hout I hI hU
  have hord : orderOf β = 3 := orderOf_three_of_not_inner hβ hout
  obtain ⟨d, hv⟩ := d
  cases hd
  have hq3 : q.p = 3 := by simpa using hchar
  exfalso
  obtain ⟨f, hf, K, _, _, σ, hK, hσ, ⟨e₁⟩⟩ := exc_exists_graphFixed_of_tauCeti q hv e hq3
  haveI : CharP K 3 := exc_charP_three_of_card K hK
  haveI : Finite (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
    Finite.of_equiv S e₁.toEquiv
  have hβ3 : MulAut.congr e₁ β ^ 3 = 1 := by
    rw [← map_pow, ← hord, pow_orderOf_eq_one, map_one]
  have hβin : MulAut.congr e₁ β ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
    rintro ⟨g, hg⟩
    apply hout
    refine ⟨e₁.symm g, ?_⟩
    apply (MulAut.congr e₁).injective
    rw [CFSG.ComponentClassification.OuterAutomorphisms.congr_conj, e₁.apply_symm_apply]
    exact hg
  have key := noU42At_trialityD4_three hf hK σ hσ _ hβ3 hβin
  obtain ⟨hI', ⟨eI⟩⟩ := component_transport e₁ rfl hI
  exact key _ hI' ((Nat.card_congr eI.toEquiv).symm.trans (I1431Z.card_eq_of_u4two hU))

end CFSG.LocalAnalysis.GLTheoremA

end
