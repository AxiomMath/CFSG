module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.FP
public import CFSG.LocalAnalysis.GLTheoremA.CatA.MIInnDiag
public import CFSG.LocalAnalysis.GLTheoremA.CatA.MIAut3
public import CFSG.LocalAnalysis.GLTheoremA.CatA.OutCycGroup
public import CFSG.LocalAnalysis.GLTheoremA.CatA.OutCycMark
public import CFSG.LocalAnalysis.GLTheoremA.CatA.D4XAsm2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.D4YBMain
public import CFSG.LocalAnalysis.GLTheoremA.CatA.D4YIFinal
public import CFSG.LargeExtraspecial.S14Defs
public import CFSG.LargeExtraspecial.S14Inputs
public import CFSG.LieType.Multipliers.U62Sylow
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSporadicCasesC
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreEven
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreL34
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreRes
public import CFSG.Monster.B.TwoA.Base.FourNorm
public import CFSG.Monster.SteinbergMY443SimpleIsomorphism
public import CFSG.Sporadic.HeldB.OuterFixed

public section

namespace CFSG.LocalAnalysis.GLTheoremA.OutCyc

open CFSG.Open CFSG.Assembly CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.GLTheoremA.S3 CFSG.LocalAnalysis.GLTheoremA.MI
open CFSG.StandardType


@[expose] def P'D4 (p : ℕ) : LargeEvenLabel → LargeEvenRawCont := fun _ R _ I F =>
  (IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) → MI.RawInnBody p R I F) ∧
  FP.OddAutCentral p R I F ∧ FP.FieldCyc R I F ∧
  (IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) → FP.CMIiff R I F)

theorem hall_P'D4
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (lab : LargeEvenLabel)
    (hlab : LargeEvenInLambda2 lab) : MI.CAll lab (LargeEvenSimpleGuard (P'D4 p lab)) := by
  have h := MI.CAll.and (MI.canonRawInn' hp hp2 hlab)
    (MI.CAll.and (FP.canonOddAutCentral hp hp2 hlab)
      (MI.CAll.and (FP.canonFieldCyc hlab) (FP.canonMIiff hlab)))
  exact MI.CAll.mono (fun R _ I F h' => fun _ _ => ⟨h'.1, h'.2.1, h'.2.2.1, h'.2.2.2⟩) h


theorem outCyc_D4_case
    {G : Type} [Group G] [Finite G] (B : Subgroup G) (x : G) (L A : Subgroup G)
    (hS : IsSTriple 3 B x L) (hK : CFSG.Open.IsKGroup ↥(Subgroup.centralizer ({x} : Set G)))
    (hchev : IsChevSimple 2 (PSimple 3 L)) (hcat : catalogIs (PSimple 3 L) isD4any)
    (hAB : A ≤ B) (hBN : B ≤ Subgroup.normalizer (L : Set G))
    (M₀ : CFSG.Assembly.LargeEvenMarking (PQuot 3 L) fun lab R _ I F θ => True ∧ MarkedModel lab R) :
    ∃ A₀ : Subgroup G, A₀ ≤ A ∧ InnDiagOn 3 A₀ L ∧ Nat.card A ≤ 3 * Nat.card A₀ ∧
      ∀ a ∈ A, InnDiagOn 3 (Subgroup.zpowers a) L → a ∈ A₀ := by
  have hBel : CFSG.Open.IsElemAbelian 3 B := hS.1.1
  have hAN : A ≤ Subgroup.normalizer (L : Set G) := hAB.trans hBN
  have hexp : ∀ a ∈ A, a ^ 3 = 1 := fun a ha => hBel.2 a (hAB ha)
  have hMc := marking_transport_central_family (fun a : G => indRel 3 L a) (A : Set G)
    (Set.toFinite _) (fun a ha => D4T.noTrialityAt_of_autNorm D4YB.d4TwoAutNormInn_holds
        D4Y.noTrialityBigAt_holds B x L hS hK hchev hcat a (hAB ha)) M₀
  have hMs := FP.canon_marking_and_labelAll_simple' (P' := P'D4 3)
    (fun lab hlab => hall_P'D4 Nat.prime_three (by norm_num) lab hlab) hMc
  obtain ⟨hX, lab₁, hlab₁, hraw₁⟩ := hMs
  obtain ⟨R₁, _, I₁, F₁, hQ⟩ := CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw₁
  obtain ⟨hs, hna, θ₁, hPc, hP'⟩ := hQ
  haveI : Finite R₁ := Finite.of_equiv (PSimple 3 L) θ₁.toEquiv
  have hRaw := hP'.1 hs hna
  have hOAC := hP'.2.1 hs hna
  have hFC := hP'.2.2.1
  have hCMI := hP'.2.2.2 hs hna
  have hJI : ∀ y : MulAut R₁, y ∈ rawSubgroup hRaw ↔ y ∈ I₁ := fun y => Iff.rfl
  have hcent : ∀ a ∈ A, ∀ φ : MulAut R₁, LargeEvenInduces θ₁ (indRel 3 L a) φ →
      FP.CentralMod I₁ φ := fun a ha => hPc.2 a ha
  obtain ⟨S, g, hJS, hJn, hg, hψS, hgen⟩ :=
    d4_group_data (p := 3) (by norm_num) L A hAN hexp θ₁ (rawSubgroup hRaw) hJI hcent hOAC hFC
  exact outCyc_of_source (by norm_num) L A hAN hexp M₀ θ₁ hCMI (rawSubgroup hRaw) hJI S g hJS hJn hg
    hψS hgen


end CFSG.LocalAnalysis.GLTheoremA.OutCyc

end
