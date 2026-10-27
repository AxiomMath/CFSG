module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Defs
public import CFSG.Foundations.QuasisimpleMulEquiv

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

private theorem pPrimeCore_two_eq_oddCore (X : Type*) [Group X] :
    pPrimeCore 2 X = oddCore X := by
  unfold pPrimeCore oddCore
  congr 1
  ext N
  simp only [Set.mem_ofPred_eq, Nat.coprime_two_left]

theorem isComponent_of_isPComponent_two_of_oddCore_eq_bot {X : Type} [Group X] [Finite X]
    (hO : oddCore X = ⊥) {K : Subgroup X} (hK : IsPComponent 2 K) : IsComponent K := by
  have hcore : pPrimeCore 2 X = ⊥ := by rw [pPrimeCore_two_eq_oddCore X, hO]
  obtain ⟨K', hK'comp, hKsub, hmap, -⟩ := hK
  have hinj : Function.Injective (QuotientGroup.mk' (pPrimeCore 2 X)) :=
    (MonoidHom.ker_eq_bot_iff _).1 (by rw [QuotientGroup.ker_mk']; exact hcore)
  refine ⟨?_, hKsub⟩
  cases hmap
  exact IsQuasisimple.of_mulEquiv (K.equivMapOfInjective _ hinj) hK'comp.1

theorem aschA1_of_balanced {G : Type} [Group G] [Finite G]
    (h : ∀ z : G, orderOf z = 2 → oddCore (centralizer ({z} : Set G)) = ⊥) : AschA1 G := by
  intro x hx K hK
  exact isComponent_of_isPComponent_two_of_oddCore_eq_bot (h x hx) hK

end CFSG.OddStandard.SmallF3.Omega
