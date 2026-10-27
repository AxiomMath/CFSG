module

public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Return

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.ToralSign
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped MatrixGroups

variable (p : ℕ) [Fact p.Prime] {k : Type} [Field k] [IsAlgClosed k] [CharP k p]

theorem nil_mem_omegaWords_e6 {r : SignRep .E6} (hr : r ∈ e6SignDiagramReps) :
    ([] : List (Fin Tag.E6.rank)) ∈ r.omegaWords := by
  simp only [e6SignDiagramReps, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> simp [e6OmegaWords0, e6OmegaWords20, e6OmegaWords2]

theorem e6_exists_conj_eq_fixedRankOne (hp : p ≠ 2)
    (hk : letI := ZMod.algebra k p; Algebra.IsAlgebraic (ZMod p) k) {e : ℕ} (he : 1 ≤ e)
    {x : ModGL TwistTag.E6.tag k}
    (hx : x ∈ fixedPointsIn (adjointGroup TwistTag.E6.tag k)
      (frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k)))
    (hx2 : x ^ 2 = 1) {L : Subgroup (ModGL TwistTag.E6.tag k)}
    (hL : L ≤ ⁅fixedPointsIn (adjointGroup TwistTag.E6.tag k)
        (frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k)),
        fixedPointsIn (adjointGroup TwistTag.E6.tag k)
          (frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k))⁆ ⊓
          Subgroup.centralizer {x})
    (hLc : CFSG.IsPComponent 2 (L.subgroupOf (⁅fixedPointsIn (adjointGroup TwistTag.E6.tag k)
      (frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k)),
      fixedPointsIn (adjointGroup TwistTag.E6.tag k)
      (frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k))⁆ ⊓
        Subgroup.centralizer {x})))
    {Y : Type} [Group Y] (φ₀ : Y ≃* L) (O : Subgroup Y) [O.Normal] (hO : Odd (Nat.card O))
    {F₂ : Type} [Field F₂] [Finite F₂] (hF₂ : Nat.card F₂ = p ^ e) (h5 : 5 ≤ p ^ e)
    (eY : Y ⧸ O ≃* SL(2, F₂)) :
    ∃ g₁ ∈ adjointGroup TwistTag.E6.tag k,
      frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k) g₁ = g₁ ∧
      ∃ β : Fin TwistTag.E6.tag.rank → ℤ, IsRoot TwistTag.E6.tag β ∧
        permLattice TwistTag.E6.perm β = β ∧
        L = (fixedPointsIn (rootSubgroup TwistTag.E6.tag k β)
            (frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k)) ⊔
          fixedPointsIn (rootSubgroup TwistTag.E6.tag k (-β))
            (frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k))).map
              (MulAut.conj g₁⁻¹).toMonoidHom := by
  have hk2 : ringChar k ≠ 2 := by
    rw [ringChar.eq k p]
    exact hp
  obtain ⟨-, h6, -⟩ := rational_toral_sign_diagram_arithmetic
  obtain ⟨-, n6, -⟩ := rational_toral_twist_semilinear_pinning_normalization (k := k) p hp e he
  refine exists_conj_eq_fixedRankOne_of_isPComponent p TwistTag.E6 hp hk he e6SignDiagramReps
    (r₀ := 2) symmetrizedCartan_perm_E6 h6.permChar_eq h6.exists_rep ?_
    (fun r hr => h6.theta r hr [] (nil_mem_omegaWords_e6 hr))
    (fun r hr => n6 r hr [] (nil_mem_omegaWords_e6 hr)) hx hx2 hL hLc φ₀ O hO hF₂ h5 eY
  intro r hr
  refine untwistAt_of_eq _ _ ?_
  have ha := signCharTuple_sign (k := k) (signMaskChar TwistTag.E6.tag r.mask)
  exact (exceptional_toral_centralizer_identity_component TwistTag.E6.tag k hk2 _ ha).2.2.2.2.1
    (Or.inr (Or.inr (Or.inl rfl)))

end CFSG.ClassicalInvolution.ModelFacts
