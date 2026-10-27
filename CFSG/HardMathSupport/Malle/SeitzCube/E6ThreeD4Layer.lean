module

public import CFSG.HardMathSupport.Malle.SeitzCube.E6D4SingerMonomial
public import CFSG.HardMathSupport.Malle.SeitzCube.E6D4LineLayerConj
public import CFSG.HardMathSupport.Malle.SeitzCube.E6ThreeD4Frame
public import CFSG.HardMathSupport.Malle.SeitzCube.D4LayerBridgeCat
public import CFSG.HardMathSupport.Malle.SeitzCube.D4PlaneGen
public import CFSG.HardMathSupport.Lang.SeitzPlane.Phi3D4LayerData
public import CFSG.RankThree.PartOne.KE.CTLang
public import CFSG.GH74.GLS.SP.Local.SPLRestrict
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4MpMain
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4Q1Main
public import CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator.Cover
public import CFSG.HardMathSupport.Seitz.G2Anisotropic.ExceptionsTransport.FamilyProved
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator.Handback
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator.OuterThree
public import CFSG.LieType.Chevalley.E6SecondGraphFullCentralizer
public import CFSG.LieType.SeitzGeneration.ExcOuterTriality
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverFour
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotAlignCores
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotHR7Split
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotXiCaseLTorus
public import CFSG.RankThree.PartOne.SEITZ6.G2MaxDone

public noncomputable section

namespace CFSG.HardMathSupport.Malle.SeitzCube

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6
open CFSG.RankThree.PartOne.KE (twistedFixedPoints mem_twistedFixedPoints)

open CFSG.RankThree.PartOne.KE6 (phi3N)

open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)

open scoped MatrixGroups

section Conj

variable {Ω : Type} [Field Ω] [IsAlgClosed Ω]

theorem exists_twisted_conj {Fr : Ω →+* Ω} {q : ℕ} (hFr : ∀ c, Fr c = c ^ q)
    (Qh : ModGL Tag.E6 Ω)
    (hn' : Qh⁻¹ * Units.map (entrywiseHom Fr) Qh ∈ monomialSubgroup Tag.E6 Ω)
    (hw : weylQuotientHom Tag.E6 Ω ⟨_, hn'⟩ = e6D4wp) :
    ∃ c ∈ torusGroup Tag.E6 Ω,
      (∀ y : ModGL Tag.E6 Ω, Units.map (entrywiseHom Fr) y = y →
        (c * canonicalRep (coxeterSystem Tag.E6) Ω e6D4m * Qh⁻¹) * y *
          (c * canonicalRep (coxeterSystem Tag.E6) Ω e6D4m * Qh⁻¹)⁻¹ ∈
            twistedFixedPoints (phi3N Ω) (Units.map (entrywiseHom Fr))) ∧
      (∀ z ∈ twistedFixedPoints (phi3N Ω) (Units.map (entrywiseHom Fr)),
        Units.map (entrywiseHom Fr)
          ((c * canonicalRep (coxeterSystem Tag.E6) Ω e6D4m * Qh⁻¹)⁻¹ * z *
            (c * canonicalRep (coxeterSystem Tag.E6) Ω e6D4m * Qh⁻¹)) =
          (c * canonicalRep (coxeterSystem Tag.E6) Ω e6D4m * Qh⁻¹)⁻¹ * z *
            (c * canonicalRep (coxeterSystem Tag.E6) Ω e6D4m * Qh⁻¹)) := by
  obtain ⟨c, hc, hconj⟩ := e6D4_twistedFixedPoints_conj hFr _ hn' hw
  set Φ : ModGL Tag.E6 Ω →* ModGL Tag.E6 Ω := Units.map (entrywiseHom Fr) with hΦ
  set n' : ModGL Tag.E6 Ω := Qh⁻¹ * Φ Qh with hn'def
  set w : ModGL Tag.E6 Ω := c * canonicalRep (coxeterSystem Tag.E6) Ω e6D4m with hw'
  have hΦQ : Φ Qh = Qh * n' := by rw [hn'def]; group
  refine ⟨c, hc, fun y hy => ?_, fun z hz => ?_⟩
  · have hv : Qh⁻¹ * y * Qh ∈ twistedFixedPoints n' Φ := by
      rw [mem_twistedFixedPoints, map_mul, map_mul, map_inv, hy, hΦQ]
      group
    have hm : (MulAut.conj w).toMonoidHom (Qh⁻¹ * y * Qh) ∈
        twistedFixedPoints (phi3N Ω) (Units.map (entrywiseHom Fr)) :=
      hconj ▸ Subgroup.mem_map_of_mem _ hv
    have e : (w * Qh⁻¹) * y * (w * Qh⁻¹)⁻¹ = w * (Qh⁻¹ * y * Qh) * w⁻¹ := by group
    rw [e]
    exact hm
  · rw [← hconj] at hz
    obtain ⟨v, hv, rfl⟩ := hz
    have hv' : n' * Φ v * n'⁻¹ = v := hv
    have e : (w * Qh⁻¹)⁻¹ * ((MulAut.conj w).toMonoidHom v) * (w * Qh⁻¹) = Qh * v * Qh⁻¹ := by
      change (w * Qh⁻¹)⁻¹ * (w * v * w⁻¹) * (w * Qh⁻¹) = Qh * v * Qh⁻¹
      group
    rw [e, map_mul, map_mul, map_inv, hΦQ]
    calc Qh * n' * Φ v * (Qh * n')⁻¹ = Qh * (n' * Φ v * n'⁻¹) * Qh⁻¹ := by group
      _ = Qh * v * Qh⁻¹ := by rw [hv']

end Conj

section LayerEquiv

variable {K : Type} [Field K] [Finite K] {Ω : Type} [Field Ω] [Algebra K Ω]
  [Algebra.IsAlgebraic K Ω]

@[expose] def layerHom (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (H : ModGL Tag.E6 Ω) :
    adjointGroup Tag.E6 K →* ModGL Tag.E6 Ω :=
  (MulAut.conj H).toMonoidHom.comp
    ((baseChangeGL (algebraMap K Ω)).comp (adjointGroup Tag.E6 K).subtype)

theorem layerHom_injective (H : ModGL Tag.E6 Ω) : Function.Injective (layerHom K Ω H) :=
  (MulAut.conj H).injective.comp ((baseChangeGL_injective _).comp (Subgroup.subtype_injective _))

theorem exists_layer_equiv {Fr : Ω →+* Ω} (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (H : ModGL Tag.E6 Ω) (hH : H ∈ adjointGroup Tag.E6 Ω) (P : Subgroup (ModGL Tag.E6 Ω))
    [Finite P] (hPadj : P ≤ adjointGroup Tag.E6 Ω) (hPperf : ⁅P, P⁆ = P)
    (hPfix : ∀ z ∈ P, Units.map (entrywiseHom Fr) (H⁻¹ * z * H) = H⁻¹ * z * H) :
    (∀ z ∈ P, ∃ y : adjointGroup Tag.E6 K, layerHom K Ω H y = z) ∧
      Nonempty (↥(P.comap (layerHom K Ω H)) ≃* ↥P) := by
  set X : Subgroup (ModGL Tag.E6 Ω) := P.map (MulAut.conj H⁻¹).toMonoidHom with hX
  have hXfin : Finite X :=
    Finite.of_equiv P (Subgroup.equivMapOfInjective P _ (MulAut.conj H⁻¹).injective).toEquiv
  have hXadj : X ≤ adjointGroup Tag.E6 Ω := by
    rintro _ ⟨z, hz, rfl⟩
    exact mul_mem (mul_mem (inv_mem hH) (hPadj hz)) (by simpa using hH)
  have hXfix : ∀ x ∈ X, Units.map (entrywiseHom Fr) x = x := by
    rintro _ ⟨z, hz, rfl⟩
    exact hPfix z hz
  have hXperf : ⁅X, X⁆ = X := by
    rw [hX, ← Subgroup.map_commutator, hPperf]
  obtain ⟨-, -, hrat⟩ := CFSG.RankThree.PartOne.KE.finite_fixed_subgroup_rational_perfect
    (τ := Tag.E6) (K := K) (L := Ω) 3 (Or.inl ⟨rfl, rfl⟩) Fr hFr X hXadj hXfix
  have hsurj : ∀ z ∈ P, ∃ y : adjointGroup Tag.E6 K, layerHom K Ω H y = z := by
    intro z hz
    have hzX : H⁻¹ * z * H ∈ X := ⟨z, hz, rfl⟩
    obtain ⟨a, ha, hbc⟩ := hrat X le_rfl hXperf hzX
    refine ⟨⟨a, ha⟩, ?_⟩
    change H * (baseChangeGL (algebraMap K Ω) a) * H⁻¹ = z
    rw [hbc]
    group
  refine ⟨hsurj, ⟨?_⟩⟩
  refine MulEquiv.ofBijective
    (MonoidHom.codRestrict ((layerHom K Ω H).comp (P.comap (layerHom K Ω H)).subtype) P
      (fun y => y.2)) ⟨fun a b hab => ?_, fun z => ?_⟩
  · apply Subtype.ext
    apply layerHom_injective H
    exact congrArg Subtype.val hab
  · obtain ⟨y, hy⟩ := hsurj z.1 z.2
    exact ⟨⟨y, by simpa [hy] using z.2⟩, Subtype.ext hy⟩

end LayerEquiv

end CFSG.HardMathSupport.Malle.SeitzCube
