
module

public import CFSG.GF2Type.Smith1979.GammaU.SigmaInputs
public import CFSG.GF2Type.Smith1979.GammaU.Violation

public section

namespace CFSG.GF2Type.Smith1979.GammaU.SigmaP

open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA
open CFSG.GF2Type.Smith1979.GammaU.Viol CFSG.GF2Type.Smith1979.GammaU.ResPair Module

structure SigmaFacts (i : ℕ) : Prop where
  orbit_subset : ∀ U ∈ genGrp (n2Gens i), ∃ y ∈ s45 i, U (vecOf a0) = vecOf y
  orbit_reach : ∀ x ∈ s45 i, ∃ U ∈ genGrp (n2Gens i), U (vecOf a0) = vecOf x
  finrank_sigma : finrank (ZMod 2) (spanOf (sigmaBasis i)) = 6
  orbit_mem_sigma : ∀ x ∈ s45 i, vecOf x ∈ spanOf (sigmaBasis i)
  sigma_le_span : spanOf (sigmaBasis i) ≤ Submodule.span (ZMod 2) {v | ∃ x ∈ s45 i, vecOf x = v}
  q0_sigma : ∀ v ∈ spanOf (sigmaBasis i), q0 v = 0
  theta0_sigma : ∀ v ∈ spanOf (sigmaBasis i), theta0 v ∈ spanOf (sigmaBasis i)
  outPts_length : (outPts i).length = 18
  outPts_not_collinear : ∀ x ∈ outPts i, ∀ y ∈ outPts i, ∀ w ∈ outPts i,
    F4Indep (vecOf x) (vecOf y) → F4Indep (vecOf x) (vecOf w) → F4Indep (vecOf y) (vecOf w) →
      vecOf w ∉ spanOf [x, theta0N x, y, theta0N y]
  card_p2 : Nat.card (genGrp (pGens i)) = 17280
  commutator_n2 : ⁅genGrp (n2Gens i), genGrp (n2Gens i)⁆ = genGrp (pGens i)
  commutator_p2 : ⁅genGrp (pGens i), genGrp (pGens i)⁆ = genGrp (pGens i)
  theta0_mem_p2 : ∃ U ∈ genGrp (pGens i), ∀ v, U v = theta0 v
  exists_noncentral : ∃ c ∈ genGrp (pGens i), (∀ v ∈ spanOf (sigmaBasis i), c v = v) ∧
    ∃ p ∈ genGrp (pGens i), c * p ≠ p * c

end CFSG.GF2Type.Smith1979.GammaU.SigmaP

end
