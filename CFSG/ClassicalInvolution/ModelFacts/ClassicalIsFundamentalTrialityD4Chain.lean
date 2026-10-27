module

public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Return
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTrialityD4Untwist

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.ToralSign
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped MatrixGroups

variable (p : ℕ) [Fact p.Prime] {k : Type} [Field k] [IsAlgClosed k] [CharP k p]

theorem nil_mem_omegaWords_d4 {r : SignRep .D4} (hr : r ∈ d4SignDiagramReps) :
    ([] : List (Fin Tag.D4.rank)) ∈ r.omegaWords := by
  simp only [d4SignDiagramReps, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> simp [d4OmegaWords0, d4OmegaWords4]

theorem d4_exists_conj_eq_fixedRankOne (hp : p ≠ 2)
    (hk : letI := ZMod.algebra k p; Algebra.IsAlgebraic (ZMod p) k) {e : ℕ} (he : 1 ≤ e)
    {x : ModGL TwistTag.D4.tag k}
    (hx : x ∈ fixedPointsIn (adjointGroup TwistTag.D4.tag k)
      (frobTwistGL TwistTag.D4.tag k p e (diagramMap TwistTag.D4 k)))
    (hx2 : x ^ 2 = 1) {L : Subgroup (ModGL TwistTag.D4.tag k)}
    (hL : L ≤ ⁅fixedPointsIn (adjointGroup TwistTag.D4.tag k)
        (frobTwistGL TwistTag.D4.tag k p e (diagramMap TwistTag.D4 k)),
        fixedPointsIn (adjointGroup TwistTag.D4.tag k)
          (frobTwistGL TwistTag.D4.tag k p e (diagramMap TwistTag.D4 k))⁆ ⊓
          Subgroup.centralizer {x})
    (hLc : CFSG.IsPComponent 2 (L.subgroupOf (⁅fixedPointsIn (adjointGroup TwistTag.D4.tag k)
      (frobTwistGL TwistTag.D4.tag k p e (diagramMap TwistTag.D4 k)),
      fixedPointsIn (adjointGroup TwistTag.D4.tag k)
      (frobTwistGL TwistTag.D4.tag k p e (diagramMap TwistTag.D4 k))⁆ ⊓
        Subgroup.centralizer {x})))
    {Y : Type} [Group Y] (φ₀ : Y ≃* L) (O : Subgroup Y) [O.Normal] (hO : Odd (Nat.card O))
    {F₂ : Type} [Field F₂] [Finite F₂] (hF₂ : Nat.card F₂ = p ^ e) (h5 : 5 ≤ p ^ e)
    (eY : Y ⧸ O ≃* SL(2, F₂)) :
    ∃ g₁ ∈ adjointGroup TwistTag.D4.tag k,
      frobTwistGL TwistTag.D4.tag k p e (diagramMap TwistTag.D4 k) g₁ = g₁ ∧
      ∃ β : Fin TwistTag.D4.tag.rank → ℤ, IsRoot TwistTag.D4.tag β ∧
        permLattice TwistTag.D4.perm β = β ∧
        L = (fixedPointsIn (rootSubgroup TwistTag.D4.tag k β)
            (frobTwistGL TwistTag.D4.tag k p e (diagramMap TwistTag.D4 k)) ⊔
          fixedPointsIn (rootSubgroup TwistTag.D4.tag k (-β))
            (frobTwistGL TwistTag.D4.tag k p e (diagramMap TwistTag.D4 k))).map
              (MulAut.conj g₁⁻¹).toMonoidHom := by
  obtain ⟨-, -, h4⟩ := rational_toral_sign_diagram_arithmetic
  obtain ⟨-, -, n4⟩ := rational_toral_twist_semilinear_pinning_normalization (k := k) p hp e he
  exact exists_conj_eq_fixedRankOne_of_isPComponent p TwistTag.D4 hp hk he d4SignDiagramReps
    (r₀ := 3) symmetrizedCartan_perm_D4 h4.permChar_eq h4.exists_rep (untwistAt_d4 p hp e)
    (fun r hr => h4.theta r hr [] (nil_mem_omegaWords_d4 hr))
    (fun r hr => n4 r hr [] (nil_mem_omegaWords_d4 hr)) hx hx2 hL hLc φ₀ O hO hF₂ h5 eY

end CFSG.ClassicalInvolution.ModelFacts
