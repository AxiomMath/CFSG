module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Fi22
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.OrthFieldExport

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.Assembly.LowTwoRank

theorem lieCompsExport_omega_outer (hOm : OmegaFactorFacts) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {t : StatedLieTag} (ht : t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus)
    {G : Type} [Group G] [Finite G] {n ℓ f : ℕ} (hG : StatedClassicalModel G t n ℓ f)
    (hD4 : t = .POmegaPlus → n = 4 → p ≠ 3) (β : MulAut G) (hβ : β ^ p = 1)
    (hout : ∀ a : G, MulAut.conj a ≠ β) : LieCompsExport ℓ β :=
  ⟨(omega_outer_layer_comps hOm hp hp2 ht hG hD4 β hβ hout).1,
    (omega_outer_layer_comps hOm hp hp2 ht hG hD4 β hβ hout).2⟩

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
