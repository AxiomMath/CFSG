module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.FactsS
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.FrameKit
public import Certificates.Data.CFSGNative.CosetTable.Enum

public section

namespace CFSG.OddStandard.HigherRank.G2Three.Sec1Proof.Tab

open CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.Open Subgroup CFSG.CosetTable
open scoped commutatorElement

variable {Γ : Type} [Group Γ] {D : TabData} {elt : ℕ → Γ} {I : FIdx}

@[expose] def rels11List : List (FreeGroup (Fin 6)) :=
  let a₁ : FreeGroup (Fin 6) := FreeGroup.of 0
  let b₁ : FreeGroup (Fin 6) := FreeGroup.of 1
  let a₂ : FreeGroup (Fin 6) := FreeGroup.of 2
  let b₂ : FreeGroup (Fin 6) := FreeGroup.of 3
  let h₀ : FreeGroup (Fin 6) := FreeGroup.of 4
  let σ : FreeGroup (Fin 6) := FreeGroup.of 5
  let z : FreeGroup (Fin 6) := b₁ ^ 2
  [z ^ 2, h₀ ^ 2, σ ^ 2, a₁ ^ 2 * z⁻¹, a₂ ^ 2 * z⁻¹, b₂ ^ 2 * z⁻¹,
    ⁅a₁, b₁⁆ * z⁻¹, ⁅a₂, b₂⁆ * z⁻¹,
    ⁅a₁, h₀⁆ * (b₁ * z)⁻¹, ⁅a₂, h₀⁆ * (b₂ * z)⁻¹, ⁅b₁, h₀⁆ * z⁻¹, ⁅b₂, h₀⁆ * z⁻¹,
    ⁅a₁, σ⁆ * (a₁ * a₂ * z)⁻¹, ⁅a₂, σ⁆ * (a₁ * a₂ * z)⁻¹,
    ⁅b₁, σ⁆ * (b₁ * b₂ * z)⁻¹, ⁅b₂, σ⁆ * (b₁ * b₂ * z)⁻¹, ⁅h₀, σ⁆ * z⁻¹,
    ⁅a₁, a₂⁆, ⁅a₁, b₂⁆, ⁅b₁, a₂⁆, ⁅b₁, b₂⁆]

@[expose] def ws11 : List (List (Fin 6 × Bool)) := rels11List.map FreeGroup.toWord

theorem rels11_eq_ws : Frame.rels11 = {r | r ∈ ws11.map FreeGroup.mk} := by
  ext r
  rw [Frame.rels11, ws11, rels11List, List.map_map]
  simp only [Set.mem_ofPred_eq, List.mem_map, Function.comp_apply]
  constructor
  · intro hr
    exact ⟨r, hr, FreeGroup.mk_toWord⟩
  · rintro ⟨a, ha, h⟩
    rw [FreeGroup.mk_toWord] at h
    exact h ▸ ha

end CFSG.OddStandard.HigherRank.G2Three.Sec1Proof.Tab
