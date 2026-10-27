module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.PerfThreeOrth.CharSum
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusCentOrthFixed

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.PerfThreeOrth

open Polynomial Module CFSG.AGLEmbedding.ToralCensus CFSG.RankThree.PartOne.KCOrthogonal

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {x : V ≃ₗ[K] V}

theorem perfectThreeIn_orthFixed_of_card_two_minus (hx : OddOrderIsometry Q 3 x)
    (hd : finrank K (fixedSpace x) = 4)
    (hts : ¬ ∃ W : Submodule K V, W ≤ fixedSpace x ∧ finrank K W = 2 ∧ ∀ w ∈ W, Q w = 0) :
    PerfectThreeIn (supportedBlock Q x (X - 1)) := by
  have hts' : ∀ U : Submodule K (fixedSpace x), finrank K U = 2 →
      ∃ u ∈ U, (Q.comp (fixedSpace x).subtype) u ≠ 0 := by
    intro U hU
    by_contra hall
    push Not at hall
    refine hts ⟨U.map (fixedSpace x).subtype, Submodule.map_subtype_le _ _, ?_, ?_⟩
    · rw [Submodule.finrank_map_subtype_eq]
      exact hU
    · rintro _ ⟨u, hu, rfl⟩
      exact hall u hu
  refine (((perfectThreeIn_orth_minus_four hx.polarBilin_fixed_nondegenerate hd hts').top_of_le
    le_rfl).map ((supportedBlock Q x (X - 1)).subtype.comp (fixedBlockEquiv hx).symm.toMonoidHom)
    ((Subgroup.subtype_injective _).comp (fixedBlockEquiv hx).symm.injective)).mono ?_
  rintro _ ⟨g, -, rfl⟩
  exact ((fixedBlockEquiv hx).symm g).2

theorem perfectThreeIn_isometryCentralizer_fixedFour (hK : Nat.card K = 2)
    (hx : OddOrderIsometry Q 3 x) (hdim : finrank K V = 10)
    (hmax : ∃ U : Submodule K V, finrank K U = 5 ∧ ∀ u ∈ U, Q u = 0)
    (hd : finrank K (fixedSpace x) = 4) : PerfectThreeIn (isometryCentralizer Q x) :=
  (perfectThreeIn_orthFixed_of_card_two_minus hx hd
    (not_exists_totallySingular_fixed_of_odd hK hx (r := 5) (m := 3) hdim hmax (by omega)
      (by decide))).mono (supportedBlock_le_isometryCentralizer _)

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.PerfThreeOrth
