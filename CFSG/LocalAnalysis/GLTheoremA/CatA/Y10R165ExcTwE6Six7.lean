module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcTwE6Six6
public import CFSG.HardMathSupport.Lang.SeitzPlane.TwE6FrameLayer

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcTwE6

open CFSG.Open CFSG.SectionRank CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.E6 CFSG.RankThree.Lattice CFSG.HardMathSupport.Lang.TwE6Step3
  CFSG.RankThree.PartOne.KE6 CFSG.RankThree.PartOne.KE CFSG.RankThree.Classical2
  CFSG.HardMathSupport.Lang.SeitzPlane
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix MatrixGroups Pointwise

theorem exists_qTorus_in_A2_layer {K : Type} [Field K] [Finite K] {Ω : Type} [Field Ω]
    [Algebra K Ω] [IsAlgClosure K Ω] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP Ω ℓ] (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) {Fr : Ω →+* Ω} (hFr : ∀ c, Fr c = c ^ (ℓ ^ f))
    {q : ℕ} [Fact q.Prime] {ζ : Ω} (hζ : IsPrimitiveRoot ζ q) (hqd : q ∣ Nat.card K + 1)
    {S : Set (Fin Tag.E6.rank → ℤ)} (hSroots : ∀ α ∈ S, IsRoot Tag.E6 α)
    (hvS : ∀ α ∈ S, e6T3W • α ∈ S) {w : WeylGroup Tag.E6}
    (hw : (w • ·) '' S = parabolicRoots Tag.E6 support13) :
    ∃ (Φ : Matrix.SpecialLinearGroup (Fin 3) Ω ≃*
        Matrix.SpecialLinearGroup (Fin 3) Ω) (T : Subgroup (ModGL Tag.E6 Ω)),
      T ≤ rootSpan Tag.E6 Ω S ⊓ (tw6Theta Ω Fr).eqLocus (MonoidHom.id _) ∧
      IsElemAbelian q T ∧ Nat.card T = q ^ 2 := by
  classical
  obtain ⟨Φ, ⟨e⟩, ⟨H, hchar⟩, -, -⟩ :=
    CFSG.HardMathSupport.Lang.SeitzPlane.tw6_A2_layer_equiv (Ω := Ω) hf hK hFr hSroots hvS hw
  have hq1 : 1 ≤ ℓ ^ f := by
    have := pow_pos (Fact.out : ℓ.Prime).pos f
    omega
  have hqd' : q ∣ ℓ ^ f + 1 := by rwa [← hK]
  obtain ⟨T, hTle, hTel, hTcard⟩ :=
    exists_qTorus_in_layer (Ω := Ω) hζ hq1 hqd' hchar e
  exact ⟨Φ, T, hTle, hTel, hTcard⟩

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcTwE6
