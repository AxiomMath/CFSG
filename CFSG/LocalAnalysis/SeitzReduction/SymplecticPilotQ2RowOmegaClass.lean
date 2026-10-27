module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14OmegaOuterRows
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2FieldCT

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.ComponentClassification.UnbalancedCatalog.OmegaRadical
open CFSG.ClassicalGroups.Orthogonal (elementaryGroup)

section Linear

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem exists_conj_linear_of_conj_nsGlobal (hset : SeitzSetting G L) {m : ℕ}
    (hm : 3 ≤ m) (e : L ≃* StatedSp (m + 1) K) (hK : Nat.card K = 2) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {K' : Type} [Field K'] [Finite K'] (hK' : Nat.card K' = 2 ^ 1)
    {Q : QuadraticForm K' (Fin (2 * (m + 1 + 1)) → K')} (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K' (Fin (2 * (m + 1 + 1)) → K'), Module.finrank K' T = 3 ∧
      ∀ x ∈ T, Q x = 0)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q)
    (hconj : ∀ α : MulAut (matrixProjectiveDerived Q), α * α = 1 →
      ∃ β, β⁻¹ * α * β ∈ matrixProjectiveImage Q)
    (ε : nsGlobal e ≃* matrixProjectiveDerived Q) {g : G}
    (hg : g⁻¹ * t * g ∈ normalizer (nsGlobal e : Set G)) :
    ∃ (β : MulAut (matrixProjectiveDerived Q)) (s : matrixIsometries Q), s * s = 1 ∧
      β⁻¹ * MulAut.congr ε ((nsGlobal e).normalizerMonoidHom ⟨g⁻¹ * t * g, hg⟩) * β =
        matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s) := by
  have hKc : Nat.card K = 2 ^ 1 := by rw [hK, pow_one]
  have htt : t * t = 1 := by rw [← _root_.sq, ← ht, pow_orderOf_eq_one]
  set θ := (nsGlobal e).normalizerMonoidHom ⟨g⁻¹ * t * g, hg⟩ with hθ
  have hθθ : θ * θ = 1 := normalizerMonoidHom_mul_self (mul_self_inv_conj_eq_one htt g) hg
  have hαα : MulAut.congr ε θ * MulAut.congr ε θ = 1 := by rw [← map_mul, hθθ, map_one]
  have hemb : ∀ P : Subgroup (matrixProjectiveDerived Q), P ≤ fixedSubgroup (MulAut.congr ε θ) →
      commutator P = ⊤ → ∃ φ : P →* StatedSp (m + 1 + 1 - 1) K, Function.Injective φ := by
    intro P hPF hPc
    exact exists_injective_of_congr ε θ
      (fun P' hP'c hP'F => exists_injective_of_perfect_le_fixedSubgroup_conj hset (by omega) e ht
        hKt hg P' hP'c hP'F) P hPc hPF
  rcases exists_conj_linear_of_embedding le_rfl hK' (by omega) hQ hT hE hconj hKc hαα hemb with
    h | h
  · exact h
  · exact absurd h.1 (by decide)

end Linear

end CFSG.SeitzReduction.SymplecticPilot
