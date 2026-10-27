module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallGammaCore
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.AGLEmbedding.KFactProofs.RankOneCore

open CFSG.AGLEmbedding.KFactProofs.SmallGamma

@[expose] def NormalizerQuotientComm (p : ℕ) (L : Type*) [Group L] : Prop :=
  ∀ T : Sylow p L, (T : Subgroup L) ≠ ⊥ →
    ∀ x ∈ Subgroup.normalizer ((T : Subgroup L) : Set L),
    ∀ y ∈ Subgroup.normalizer ((T : Subgroup L) : Set L), x * y * x⁻¹ * y⁻¹ ∈ (T : Subgroup L)

theorem NormalizerQuotientComm.of_mulEquiv {L L' : Type*} [Group L] [Finite L] [Group L']
    {p : ℕ} [Fact p.Prime] (e : L ≃* L') (h : NormalizerQuotientComm p L) :
    NormalizerQuotientComm p L' := by
  have : Finite L' := Finite.of_equiv L e.toEquiv
  intro T' hT' x' hx' y' hy'
  set T : Sylow p L := T'.mapSurjective (f := (e.symm : L' →* L)) e.symm.surjective with hTdef
  have hT : ∀ g : L, g ∈ (T : Subgroup L) ↔ e g ∈ (T' : Subgroup L') := fun g => by
    rw [hTdef, Sylow.coe_mapSurjective, Subgroup.mem_map]
    constructor
    · rintro ⟨z, hz, rfl⟩
      simpa using hz
    · intro hg
      exact ⟨e g, hg, by simp⟩
  have hTne : (T : Subgroup L) ≠ ⊥ := by
    intro hbot
    apply hT'
    rw [Subgroup.eq_bot_iff_forall]
    intro z hz
    have h1 : e.symm z ∈ (T : Subgroup L) := (hT _).mpr (by simpa using hz)
    rw [hbot, Subgroup.mem_bot] at h1
    simpa using congrArg e h1
  have hmem : ∀ n : L, n ∈ Subgroup.normalizer ((T : Subgroup L) : Set L) ↔
      e n ∈ Subgroup.normalizer ((T' : Subgroup L') : Set L') := fun n =>
    SmallGammaData.mem_normalizer_iff e hT n
  have hx : e.symm x' ∈ Subgroup.normalizer ((T : Subgroup L) : Set L) :=
    (hmem _).mpr (by simpa using hx')
  have hy : e.symm y' ∈ Subgroup.normalizer ((T : Subgroup L) : Set L) :=
    (hmem _).mpr (by simpa using hy')
  have h1 := (hT _).mp (h T hTne _ hx _ hy)
  simpa using h1

end CFSG.AGLEmbedding.KFactProofs.RankOneCore
