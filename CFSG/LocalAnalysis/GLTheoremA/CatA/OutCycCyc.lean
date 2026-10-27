module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.FP
public import CFSG.LocalAnalysis.GLTheoremA.CatA.MIInnDiag
public import CFSG.LocalAnalysis.GLTheoremA.CatA.MIAut3
public import CFSG.LocalAnalysis.GLTheoremA.CatA.OutCycGroup
public import CFSG.LocalAnalysis.GLTheoremA.CatA.OutCycMark
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011I91
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


@[expose] def P'Cyc (p : ℕ) : LargeEvenLabel → LargeEvenRawCont := fun lab R _ I F =>
  (¬ (lab.tag = .D ∧ lab.rank = 4 ∧ p = 3) → StandardType.GGRawPCyclic p R I F) ∧
  (IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) → FP.CMIiff R I F)

theorem hall_P'Cyc
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (lab : LargeEvenLabel)
    (hlab : LargeEvenInLambda2 lab) : MI.CAll lab (LargeEvenSimpleGuard (P'Cyc p lab)) := by
  have h2 := FP.canonMIiff hlab
  by_cases hc : lab.tag = .D ∧ lab.rank = 4 ∧ p = 3
  · have h1 : MI.CAll lab (fun R _ I F =>
        (¬ (lab.tag = .D ∧ lab.rank = 4 ∧ p = 3) → StandardType.GGRawPCyclic p R I F)) :=
      caTrue lab _ (fun R _ I F h' => absurd hc h')
    exact MI.CAll.mono (fun R _ I F h' => fun _ _ => ⟨h'.1, h'.2⟩) (MI.CAll.and h1 h2)
  · have h1 : MI.CAll lab (fun R _ I F =>
        (¬ (lab.tag = .D ∧ lab.rank = 4 ∧ p = 3) → StandardType.GGRawPCyclic p R I F)) :=
      MI.CAll.mono (fun R _ I F h' _ => h') (FP.canonRawPCyclic hp hp2 hlab hc)
    exact MI.CAll.mono (fun R _ I F h' => fun _ _ => ⟨h'.1, h'.2⟩) (MI.CAll.and h1 h2)


theorem outCyc_cyc_case
    {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (B : Subgroup G) (x : G) (L A : Subgroup G) (hS : IsSTriple p B x L)
    (hchev : IsChevSimple 2 (PSimple p L))
    (hD : ¬ (p = 3 ∧ catalogIs (PSimple p L) isD4any)) (hAB : A ≤ B)
    (hBN : B ≤ Subgroup.normalizer (L : Set G))
    (M₀ : CFSG.Assembly.LargeEvenMarking (PQuot p L) fun lab R _ I F θ => True ∧ MarkedModel lab R) :
    ∃ A₀ : Subgroup G, A₀ ≤ A ∧ InnDiagOn p A₀ L ∧ Nat.card A ≤ p * Nat.card A₀ ∧
      ∀ a ∈ A, InnDiagOn p (Subgroup.zpowers a) L → a ∈ A₀ := by
  have hBel : CFSG.Open.IsElemAbelian p B := hS.1.1
  have hAN : A ≤ Subgroup.normalizer (L : Set G) := hAB.trans hBN
  have hexp : ∀ a ∈ A, a ^ p = 1 := fun a ha => hBel.2 a (hAB ha)
  have hp0 : 0 < p := hp.pos
  have hMs := FP.canon_marking_and_labelAll_simple' (P' := P'Cyc p)
    (fun lab hlab => hall_P'Cyc hp hp2 lab hlab) M₀
  obtain ⟨hX, lab₁, hlab₁, hraw₁⟩ := hMs
  obtain ⟨R₁, _, I₁, F₁, hQ⟩ := CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw₁
  obtain ⟨hs, hna, θ₁, hPθ, hP'⟩ := hQ
  haveI : Finite R₁ := Finite.of_equiv (PSimple p L) θ₁.toEquiv
  by_cases hc : lab₁.tag = .D ∧ lab₁.rank = 4 ∧ p = 3
  · exfalso
    obtain ⟨ht, hr, hp3⟩ := hc
    apply hD
    refine ⟨hp3, ?_⟩
    have hMM : MarkedModel lab₁ R₁ := hPθ.2
    have h1 : markTag lab₁ = .POmegaPlus := by simp [markTag, ht, hr]
    have h2 : markRank lab₁ = 4 := by simp [markRank, ht, hr]
    have h3 : markChar lab₁ = 2 := by simp [markChar, ht]
    have h4 : markDeg lab₁ = lab₁.n := by simp [markDeg, ht]
    unfold MarkedModel at hMM
    rw [h1, h2, h3, h4] at hMM
    exact (catalogIs_congr θ₁).2 (i91_catalog_D4 hlab₁.1 hMM)
  · have hG := hP'.1 hc hs hna
    have hCMI := hP'.2 hs hna
    obtain ⟨J, S, hJset, hJS, hJn, ⟨g, hg, hgen₀⟩, hSpow⟩ := hG
    have hJI : ∀ x, x ∈ J ↔ x ∈ I₁ := fun x => Set.ext_iff.1 hJset x
    have hψS : ∀ (a : G) (ha : a ∈ A), psiHom p L θ₁ ⟨a, hAN ha⟩ ∈ S := by
      intro a ha
      apply hSpow
      exact ⟨1, by rw [pow_one]; exact psiHom_pow_eq_one L A hAN hexp θ₁ ha⟩
    exact outCyc_of_source hp0 L A hAN hexp M₀ θ₁ hCMI J hJI S g hJS hJn hg hψS
      (fun a ha => hgen₀ _ (hψS a ha))


end CFSG.LocalAnalysis.GLTheoremA.OutCyc

end
