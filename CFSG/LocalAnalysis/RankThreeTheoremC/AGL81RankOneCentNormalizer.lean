module

public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
public import CFSG.LocalAnalysis.AGLEmbedding.CoverNotCaseTwo
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVL34SqAbs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent

open CFSG.AGLEmbedding CFSG.Open CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111

variable {G : Type} [Group G] [Finite G]

theorem le_of_le_normalizer_of_isSylowOf {p : ℕ} [Fact p.Prime] {M N D B₂ : Subgroup G}
    (hND : N ≤ Subgroup.normalizer (D : Set G)) (hDM : D ≤ M)
    (hB : CFSG.ABGLocalTools.IsSylowOf p B₂ D)
    (hBM : Subgroup.normalizer (B₂ : Set G) ≤ M) : N ≤ M := by
  intro g hg
  have hgD := hND hg
  set B' : Subgroup G := B₂.comap (MulAut.conj g).toMonoidHom with hB'def
  have hmem : ∀ x, x ∈ B' ↔ g * x * g⁻¹ ∈ B₂ := fun x => Iff.rfl
  have hB'D : B' ≤ D := by
    intro x hx
    have h1 : g * x * g⁻¹ ∈ D := hB.le ((hmem x).mp hx)
    have h2 := (Subgroup.mem_normalizer_iff.mp hgD (g⁻¹ * (g * x * g⁻¹) * g)).mpr
      (by simpa [mul_assoc] using h1)
    simpa [mul_assoc] using h2
  have hcard : Nat.card B' = Nat.card B₂ := by
    exact Nat.card_congr (Equiv.subtypeEquiv (MulAut.conj g).toEquiv fun x => Iff.rfl)
  have hB' : CFSG.ABGLocalTools.IsSylowOf p B' D :=
    CFSG.ABGLocalTools.isSylowOf_of_card hB'D (hcard.trans hB.card_eq)
  obtain ⟨k, hkD, hk⟩ := CFSG.ABGLocalTools.IsSylowOf.exists_mem_conj hB hB'
  have hn : g * k ∈ Subgroup.normalizer (B₂ : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have h := hk (k * x * k⁻¹)
    rw [hmem] at h
    have e1 : k⁻¹ * (k * x * k⁻¹) * k = x := by group
    have e2 : g * (k * x * k⁻¹) * g⁻¹ = g * k * x * (g * k)⁻¹ := by group
    rw [e1, e2] at h
    exact h.symm
  have e : g = g * k * k⁻¹ := by group
  rw [e]
  exact M.mul_mem (hBM hn) (M.inv_mem (hDM hkD))

end CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent
