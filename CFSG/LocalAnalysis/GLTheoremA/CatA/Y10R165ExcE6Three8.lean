module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Lang.TwE6Step3.SylowTorusSix
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SeitzGeneration.ExcHighThree.E6InF4Sylow
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Monster.B.Fischer.Fi22Order
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.Classical2.TwistedE6Phi3A2Case
public import CFSG.RankThree.PartOne.KE.SigmaUntwisted2
public import CFSG.RankThree.PartOne.KE6.Phi3Kernel
public import CFSG.RankThree.PartOne.KE6.Phi3Lattice
public import CFSG.RankThree.PartOne.KE6.Phi3Torus
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE6Three

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6
  CFSG.RankThree.Chevalley CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.LieType.SeitzGeneration CFSG.LieType.Steinberg.Minuscule
open CFSG.LieType.Steinberg.Isogeny
open CFSG.RankThree.PartOne.KE (twistedTorus mem_twistedTorus adjEmb adjEmb_injective
  adjEmb_mem adjEmb_frobenius sigma_embedding_data subtorusImage mem_subtorusImage_iff
  twistedTorusOf mem_twistedTorusOf twistedFixedPoints mem_twistedFixedPoints subtorusSigma)
open CFSG.RankThree.PartOne.KE6
open CFSG.RankThree.Classical2 (torusRootKernel torusRootKernel_rootDiagUnit
  rootSpan_torusRootKernel_le_centralizer rootChar_neg')
open CFSG.HardMathSupport.Lang.TwE6Step3
open CFSG.RankThree.Lattice (e6T3W)
open scoped Matrix MatrixGroups Pointwise

theorem exists_psi_of_kernelLayer {F : Type} [Field F] [Finite F] [CharP F 2]
    {n p : ℕ} (hcard : Nat.card F = 2 ^ n) (hp : p.Prime) (hp5 : 5 < p)
    (hpq : (p : ℤ) ∣ (Nat.card F : ℤ) ^ 2 + (Nat.card F : ℤ) + 1)
    {g0 : ModGL Tag.E6 (AlgebraicClosure F)}
    (hg0C : g0 ∈ adjointGroup Tag.E6 (AlgebraicClosure F))
    (hg0 : Units.map (entrywiseHom (iterateFrobenius (AlgebraicClosure F) 2 n)) g0 =
      g0 * phi3N (AlgebraicClosure F))
    (hperf : ∀ P : Subgroup (ModGL Tag.E6 (AlgebraicClosure F)),
      Finite P → P ≤ adjointGroup Tag.E6 (AlgebraicClosure F) →
      (∀ x ∈ P, Units.map (entrywiseHom (iterateFrobenius (AlgebraicClosure F) 2 n)) x = x) →
      ⁅P, P⁆ = P → P ≤ (adjEmb Tag.E6 F (AlgebraicClosure F)).range)
    {ι' : Type} {x : adjointGroup Tag.E6 F} {c : adjointGroup Tag.E6 F}
    {x_L : ModGL Tag.E6 (AlgebraicClosure F)}
    (hxL : x_L = g0⁻¹ * adjEmb Tag.E6 F (AlgebraicClosure F) (c * x * c⁻¹) * g0)
    (hxT : x_L ∈ twistedTorus (phi3N (AlgebraicClosure F))
      (iterateFrobenius (AlgebraicClosure F) 2 n))
    (hx : orderOf x = p)
    (KL : KernelLayer (phi3N (AlgebraicClosure F))
      (Units.map (entrywiseHom (iterateFrobenius (AlgebraicClosure F) 2 n)))
      (torusRootKernel x_L) F ι') :
    ∃ ψ : Subgroup.centralizer ({x} : Set (adjointGroup Tag.E6 F)) →*
        ModGL Tag.E6 (AlgebraicClosure F),
      Function.Injective ψ ∧
      (∀ y, ψ y = g0⁻¹ * adjEmb Tag.E6 F (AlgebraicClosure F) (c * y * c⁻¹) * g0) ∧
      (∀ y, ψ y ∈ torusGroup Tag.E6 (AlgebraicClosure F) ⊔
        rootSpan Tag.E6 (AlgebraicClosure F) (torusRootKernel x_L)) ∧
      (∀ y, phi3N (AlgebraicClosure F) *
        Units.map (entrywiseHom (iterateFrobenius (AlgebraicClosure F) 2 n)) (ψ y) *
          (phi3N (AlgebraicClosure F))⁻¹ = ψ y) ∧
      (∀ i, KL.P i ≤ ψ.range) := by
  classical
  haveI : CharP (AlgebraicClosure F) 2 :=
    charP_of_injective_algebraMap (algebraMap F (AlgebraicClosure F)).injective 2
  have hFr : ∀ c, iterateFrobenius (AlgebraicClosure F) 2 n c = c ^ (2 ^ n) :=
    fun c => iterateFrobenius_def 2 n c
  have hFrK : ∀ c, iterateFrobenius (AlgebraicClosure F) 2 n c = c ^ Nat.card F := by
    intro c
    rw [hFr, hcard]
  have hS : ∀ α ∈ torusRootKernel x_L, IsRoot Tag.E6 α := fun α hα => hα.1
  have hSn : ∀ α ∈ torusRootKernel x_L, -α ∈ torusRootKernel x_L := by
    rintro α ⟨hα, b, hb, hc⟩
    exact ⟨IsRoot.neg hα, b, hb, by rw [CFSG.RankThree.Classical2.rootChar_neg', hc, inv_one]⟩
  have hkerZ : ∀ a : Fin Tag.E6.rank → (AlgebraicClosure F)ˣ,
      rootDiagUnit Tag.E6 a = g0⁻¹ * adjEmb Tag.E6 F (AlgebraicClosure F) (c * x * c⁻¹) * g0 →
      rootCharKernel a ⊆ torusRootKernel x_L := by
    intro a ha
    have ha' : rootDiagUnit Tag.E6 a = x_L := by rw [ha, ← hxL]
    rw [← torusRootKernel_rootDiagUnit, ha']
  have hcS : c * x * c⁻¹ ∈ subtorusImage (adjEmb Tag.E6 F (AlgebraicClosure F)) g0
      (subtorusSigma (phi3N (AlgebraicClosure F))
        (Units.map (entrywiseHom (iterateFrobenius (AlgebraicClosure F) 2 n)))
        (torusRootKernel x_L)) := by
    rw [mem_subtorusImage_iff, ← hxL]
    have hxT' := mem_twistedTorus.1 hxT
    refine Subgroup.mem_inf.mpr ⟨mem_twistedTorusOf.mpr
      ⟨hxT'.1, mem_twistedFixedPoints.mp hxT'.2⟩, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have hle := rootSpan_torusRootKernel_le_centralizer hxT'.1
    have h1 : g * x_L = x_L * g := Subgroup.mem_centralizer_singleton_iff.1 (hle hg)
    exact h1
  have hordW : ¬ p ∣ Nat.card (WeylGroup Tag.E6) := not_dvd_card_weyl_E6 hp hp5
  obtain ⟨ψ, hψinj, hψ, hψHQ, hψR, -, hPψ, -⟩ :=
    sigma_embedding_data (adjEmb Tag.E6 F (AlgebraicClosure F)) adjEmb_injective adjEmb_mem
      (Units.map (entrywiseHom (iterateFrobenius (AlgebraicClosure F) 2 n)))
      (adjEmb_frobenius (iterateFrobenius (AlgebraicClosure F) 2 n) hFrK)
      (phi3N (AlgebraicClosure F)) g0 hg0C hg0 hperf hp hordW hS hSn KL.P KL.fin KL.quasi
      KL.le_span KL.le_fixed
      (fun i => (KL.le_span i).trans (rootSpan_le_adjointGroup (AlgebraicClosure F) _))
      KL.norm
      (fun y hy hyR hc => Subgroup.mem_inf.mpr
        ⟨mem_twistedTorusOf.mpr ⟨(KL.cent y hy hc).1, mem_twistedFixedPoints.mp hyR⟩,
          (KL.cent y hy hc).2⟩)
      hx c hcS hkerZ
  exact ⟨ψ, hψinj, hψ, hψHQ, hψR, hPψ⟩

theorem neg_stable_of_image_parabolicRoots {L : Type} [Field L]
    {S : Set (Fin Tag.E6.rank → ℤ)} {w : WeylGroup Tag.E6} {J : Set (Fin Tag.E6.rank)}
    (hS : (w • ·) '' S = parabolicRoots Tag.E6 J) :
    ∀ α ∈ S, -α ∈ S := by
  intro α hα
  have hwα : w • α ∈ parabolicRoots Tag.E6 J := by
    have h := Set.mem_image_of_mem (fun β => w • β) hα
    rwa [hS] at h
  have hwα' : w • (-α) ∈ parabolicRoots Tag.E6 J := by
    have := neg_mem_parabolicRoots hwα
    simpa using this
  have hmem : w • (-α) ∈ (w • ·) '' S := by rwa [hS]
  obtain ⟨b, hb, hba⟩ := hmem
  have hEq : b = -α := by
    have := congrArg (fun z => w⁻¹ • z) hba
    simpa using this
  rwa [hEq] at hb

theorem ncard_of_image_parabolicRoots {L : Type} [Field L]
    {S : Set (Fin Tag.E6.rank → ℤ)} {w : WeylGroup Tag.E6}
    (hS : (w • ·) '' S = parabolicRoots Tag.E6 support13) : S.ncard = 6 := by
  have h := Set.ncard_image_of_injective (s := S) (f := fun α => w • α)
    (MulAction.injective w)
  rw [hS, ncard_parabolicRoots_support13] at h
  exact h.symm

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE6Three
