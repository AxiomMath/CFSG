module

public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLinTwoField

public section

namespace CFSG.GH74.GLS.IVK

open CFSG CFSG.GorensteinWalter CFSG.Assembly.LowTwoRank Matrix
open CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo

theorem isQuasisimple_range_pslIncl {F : Type} [Field F] [Finite F]
    (σ : F ≃+* F) (h4 : 4 ≤ Nat.card (fixedField σ)) :
    CFSG.IsQuasisimple (pslIncl σ).range := by
  classical
  haveI : Fintype (fixedField σ) := Fintype.ofFinite _
  obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset (fixedField σ))) (n := 4)
    (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact h4)
  have hsimple := CFSG.LinearGroups.linear_projective_simple (n := 2) (K := fixedField σ)
    (by norm_num) (Or.inr ⟨s, hs⟩)
  have hperf := (CFSG.LinearGroups.linear_projective_perfect (n := 2) (K := fixedField σ)
    (by norm_num) (Or.inr ⟨s, hs⟩)).commutator_eq_top
  haveI : Nontrivial (PSL2 (fixedField σ)) := hsimple.1
  haveI : IsSimpleGroup (PSL2 (fixedField σ)) := hsimple.2.1
  let eJ : PSL2 (fixedField σ) ≃* (pslIncl σ).range :=
    MonoidHom.ofInjective (pslIncl_injective σ)
  haveI : IsSimpleGroup ((pslIncl σ).range) := eJ.symm.isSimpleGroup
  refine isQuasisimple_of_simple_nonabelian ?_
  intro hc
  refine not_comm_of_commutator_eq_top hperf fun a b => ?_
  apply eJ.injective
  have := hc (eJ a) (eJ b)
  simpa [map_mul] using this

end CFSG.GH74.GLS.IVK

end
