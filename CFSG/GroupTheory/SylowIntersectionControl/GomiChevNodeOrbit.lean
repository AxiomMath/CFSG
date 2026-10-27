module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevBorelAtoms
public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevOrbitSwapDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParModel
import CFSG.LieType.RootSystem.DiagramTwoGroupOrbit
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.GOrbConn

public section

namespace CFSG.GroupTheory

open CFSG.ABGLocalTools Subgroup CFSG.LieType.Universal CFSG.LieType.CurtisTits
  CFSG.LieType.Steinberg CFSG.AGLEmbedding.ParabHub
open CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar (HasBQ parJ)
open scoped Pointwise

variable {K₀ K : Type} [Group K₀] [Finite K₀] [Group K] [Finite K] {D : UniversalRootDatum K₀}
  {n : Fin D.rank → K₀} {H : Fin D.rank → Subgroup K₀} {π : K₀ →* K} {M : ℕ}

omit [Finite K] in
private lemma subtype_smul_eq_map {𝒜 : Subgroup (MulAut K)} (α : MulAut K) (hα : α ∈ 𝒜)
    (A : Subgroup K) : (⟨α, hα⟩ : 𝒜) • A = A.map α.toMonoidHom := by
  rw [Subgroup.mk_smul, Subgroup.pointwise_smul_def]
  rfl

theorem map_parJ_eq_or_of_isPGroup [IsSimpleGroup K] (hnab : ∃ a b : K, a * b ≠ b * a)
    (h : BorelQuotient D n H π M) {𝒜 : Subgroup (MulAut K)} (h𝒜 : IsPGroup 2 𝒜)
    (hfix : ∀ α ∈ 𝒜, ((posUnipotent D).map π).map α.toMonoidHom = (posUnipotent D).map π)
    (i : Fin D.rank) {α₁ α₂ : MulAut K} (h₁ : α₁ ∈ 𝒜) (h₂ : α₂ ∈ 𝒜) :
    ((parJ D H {i}).map π).map α₁.toMonoidHom = (parJ D H {i}).map π ∨
      ((parJ D H {i}).map π).map α₂.toMonoidHom = (parJ D H {i}).map π ∨
      ((parJ D H {i}).map π).map α₁.toMonoidHom =
        ((parJ D H {i}).map π).map α₂.toMonoidHom := by
  have hrange : ∀ (g : ↥𝒜) (j : Fin D.rank),
      ∃ k, g • (fun i => (parJ D H {i}).map π) j = (fun i => (parJ D H {i}).map π) k := by
    rintro ⟨α, hα⟩ j
    obtain ⟨k, hk⟩ := exists_map_map_parJ_eq h (hfix α hα) j
    exact ⟨k, by rw [subtype_smul_eq_map]; exact hk⟩
  have hadj : ∀ (g : ↥𝒜) (j k j' k' : Fin D.rank),
      g • (fun i => (parJ D H {i}).map π) j = (fun i => (parJ D H {i}).map π) j' →
      g • (fun i => (parJ D H {i}).map π) k = (fun i => (parJ D H {i}).map π) k' →
      ((TauCeti.diagramGraph D.cartan).Adj j' k' ↔
        (TauCeti.diagramGraph D.cartan).Adj j k) := by
    rintro ⟨α, hα⟩ j k j' k' hj hk
    rw [subtype_smul_eq_map] at hj hk
    exact diagramGraph_adj_iff_of_map_map_parJ_eq h α hj hk
  have key := CFSG.LieType.RootSystem.smul_eq_or_smul_eq_or_smul_eq_smul_of_isFiniteType
    (A := D.cartan) D.isFiniteType
    (CFSG.AGLEmbeddingD2.Tits.GN516.Conn.diagram_connected h hnab)
    (G := ↥𝒜) (X := Subgroup K) h𝒜 (f := fun i => (parJ D H {i}).map π)
    (CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar.parJ_map_injective h)
    hrange hadj i ⟨α₁, h₁⟩ ⟨α₂, h₂⟩
  simpa only [subtype_smul_eq_map] using key

theorem gomiAtomOrbitTop_of_hasBQ [IsSimpleGroup K] (hnab : ∃ a b : K, a * b ≠ b * a)
    (h : HasBQ K) : GomiAtomOrbitTop K := by
  obtain ⟨K₀, _, _, D, n, H, π, M, hπ⟩ := h
  intro S A 𝒜 hS h𝒜 hfix hA α₁ hα₁ α₂ hα₂
  obtain ⟨π', hπ', hS'⟩ := exists_borelQuotient_map_posUnipotent_eq hπ hS
  rw [← hS'] at hA hfix
  obtain ⟨i, rfl⟩ := (isGomiAtom_iff_exists_eq_map_parJ hπ').1 hA
  exact map_parJ_eq_or_of_isPGroup hnab hπ' h𝒜 hfix i hα₁ hα₂

end CFSG.GroupTheory
