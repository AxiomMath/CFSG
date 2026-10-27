module

public import CFSG.Assembly.InCatalog
import CFSG.Assembly.InvolutionGraph
import CFSG.StronglyEmbedded.Catalog
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Final
import CFSG.StronglyEmbedded.ParityCriterion

public section

namespace CFSG.Assembly.Disconnected

variable {G : Type*} [Group G]

@[expose] def disconnectedStronglyEmbedded (M : Subgroup G) : Prop :=
  M ≠ ⊤ ∧ Even (Nat.card M) ∧
    ∀ g : G, g ∉ M → Odd (Nat.card ↥(M ⊓ M.map (MulAut.conj g⁻¹).toMonoidHom))

@[expose] def disconnectedConjStabilizer (S : Set G) : Subgroup G where
  carrier := {g | (fun t => g⁻¹ * t * g) '' S = S}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at *
    have : (fun t => (a * b)⁻¹ * t * (a * b)) =
        (fun t => b⁻¹ * t * b) ∘ (fun t => a⁻¹ * t * a) := by
      funext t; simp [mul_assoc]
    rw [this, Set.image_comp, ha, hb]
  inv_mem' := by
    intro g hg
    simp only [Set.mem_ofPred_eq] at *
    conv_lhs => rw [← hg]
    rw [Set.image_image]
    simp [mul_assoc]

@[expose] def disconnectedComponentStabilizer (Δ : (involutionGraph G).ConnectedComponent) : Subgroup G :=
  disconnectedConjStabilizer (Subtype.val '' Δ.supp)

theorem component_stabilizer_strongly_embedded (G : Type*) [Group G] [Finite G]
    (heven : Even (Nat.card G))
    (htwo : ∃ Δ₁ Δ₂ : (involutionGraph G).ConnectedComponent, Δ₁ ≠ Δ₂)
    (Δ : (involutionGraph G).ConnectedComponent) :
    disconnectedStronglyEmbedded (disconnectedComponentStabilizer Δ) := by
  obtain ⟨Δ₁, Δ₂, h12⟩ := htwo
  obtain ⟨Δ', hne⟩ : ∃ Δ', Δ' ≠ Δ := by
    by_cases h : Δ₁ = Δ
    · exact ⟨Δ₂, fun h2 => h12 (h.trans h2.symm)⟩
    · exact ⟨Δ₁, h⟩
  exact InvolutionGraph.stronglyEmbedded_of_ne (fun _ => Iff.rfl) hne

theorem simple_strongly_embedded (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hse : ∃ M : Subgroup G, disconnectedStronglyEmbedded M) : InCatalog G := by
  obtain ⟨M, hMne, hMeven, hModd⟩ := hse
  have hM := BenderSuzuki.isStronglyEmbedded_of_components M hMne hMeven
    fun g hg => by simpa using hModd g⁻¹ (by simpa using hg)
  exact BenderSuzuki.inCatalog_of_isSimpleBenderGroup hnonab
    (BenderSuzuki.theorem_SE_simple M hM inferInstance)

end CFSG.Assembly.Disconnected

namespace CFSG.Assembly

open Disconnected in
theorem disconnected_involution_graph (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (heven : Even (Nat.card G))
    (hdisc : ¬ (involutionGraph G).Preconnected) : InCatalog G := by
  obtain ⟨u, v, huv⟩ : ∃ u v, ¬ (involutionGraph G).Reachable u v := by
    simpa [SimpleGraph.Preconnected] using hdisc
  have hne : (involutionGraph G).connectedComponentMk u ≠
      (involutionGraph G).connectedComponentMk v := by
    rwa [Ne, SimpleGraph.ConnectedComponent.eq]
  exact simple_strongly_embedded G hnonab
    ⟨_, component_stabilizer_strongly_embedded G heven ⟨_, _, hne⟩
      ((involutionGraph G).connectedComponentMk u)⟩

end CFSG.Assembly
