module

public import CFSG.GH74.Generic.S3.LyB2Sl2
public import CFSG.GH74.L5U5.ModelsBridge

public section

namespace CFSG.GH74.Generic.S3

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.GH74.GLS CFSG.BenderSuzuki.MatrixGroups Subgroup
open scoped commutatorElement

@[expose] def BlockData (L : Type) [Group L] : Prop :=
  ∀ s : L, s * s = 1 → s ≠ 1 → ∃ (F₀ : Type) (_ : Field F₀) (_ : Finite F₀) (S : Subgroup L)
    (ρ : ↥S →* PSL2MatrixGroup F₀), Odd (Nat.card F₀) ∧ (∀ g ∈ ρ.ker, g ∈ center ↥S) ∧
      ∀ a ∈ centralizer ({s} : Set L), ∀ b ∈ centralizer ({s} : Set L), ⁅a, b⁆ ∈ S

@[expose] def G2Table (G : Type) [Group G] : Prop :=
  ∀ u : G, orderOf u = 2 → ∀ L : Subgroup (CentralizerBar u), IsComponent L → InG2 ↥L →
    xbar u ∉ L ∧ center ↥L = ⊥ ∧ BlockData ↥L

theorem exc_false_of_blockData
    {L : Type} [Group L] (hL : BlockData L) {s : L} (hs2 : s * s = 1) (hs1 : s ≠ 1) {I : Subgroup L}
    (hIC : I ≤ centralizer ({s} : Set L)) (hIperf : ⁅I, I⁆ = I) {K₀ : Type} [Group K₀]
    (hK₀ : IsExcB2 K₀) (φ : ↥I →* K₀) (hφ : Function.Surjective φ) : False := by
  obtain ⟨F₀, _, _, S, ρ, hodd, hρ, hcomm⟩ := hL s hs2 hs1
  have hIS : I ≤ S := by
    have h1 : ⁅I, I⁆ ≤ S := by
      rw [Subgroup.commutator_le]
      intro a ha b hb
      exact hcomm a (hIC ha) b (hIC hb)
    rwa [hIperf] at h1
  let P : Subgroup ↥S := I.subgroupOf S
  let e : ↥P ≃* ↥I := Subgroup.subgroupOfEquivOfLe hIS
  exact false_of_exc_quotient hodd ρ hρ P hK₀ (φ.comp e.toMonoidHom)
    (hφ.comp e.surjective)

end CFSG.GH74.Generic.S3
