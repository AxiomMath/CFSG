module

public import CFSG.ClassicalInvolution.Generic.Generation.DeltaClosureDefs
import CFSG.LocalAnalysis.SignalizerFunctor.Maximality
import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.ClassicalInvolution.Generic.Generation.DeltaClosureBasic

public section

namespace CFSG.ClassicalInvolution.Generic.DeltaClosure

open CFSG.Open
open CFSG.ClassicalInvolution.Balance (oddCoreIn odd_card_oddCoreIn)

variable {G : Type} [Group G] {Ω : Set (Subgroup G)} {A : Subgroup G}

theorem comm_of_mem_elemAbelian (hA : IsElemAbelian 2 A) {x y : G} (hx : x ∈ A) (hy : y ∈ A) :
    x * y = y * x := CFSG.Open.IsElemAbelian.comm hA hx hy

theorem le_rankThreeSpan_of_le_centralizer {K E₀ : Subgroup G}
    (hE₀ : E₀ ∈ signalizerFunctorEk 2 3 A) (hK : K ≤ Subgroup.centralizer (E₀ : Set G)) :
    K ≤ rankThreeSpan A :=
  hK.trans (le_iSup₂ (f := fun (E : Subgroup G) (_ : E ∈ signalizerFunctorEk 2 3 A) =>
    Subgroup.centralizer (E : Set G)) E₀ hE₀)

theorem le_normalizer_oddCoreIn_centralizingLayer [Finite G] (hΩ : ConjInvariant Ω)
    (hA : IsElemAbelian 2 A) {a : G} (ha : a ∈ A) :
    A ≤ Subgroup.normalizer (oddCoreIn (centralizingLayer Ω {a}) : Set G) := fun _ hg =>
  mem_normalizer_oddCoreIn_centralizingLayer hΩ
    (Subgroup.mem_centralizer_singleton_iff.mpr (comm_of_mem_elemAbelian hA hg ha))

theorem oddCoreIn_centralizingLayer_le_rankThreeSpan [Finite G] (hΩ : ConjInvariant Ω)
    (hA : IsElemAbelian 2 A) (h16 : 16 ≤ Nat.card A) {a : G} (ha : a ∈ A) :
    oddCoreIn (centralizingLayer Ω {a}) ≤ rankThreeSpan A := by
  have hgen := CFSG.SignalizerFunctor.Helpers.elementary_abelian_centralizer_generation 2 3
    Nat.prime_two A (oddCoreIn (centralizingLayer Ω {a})) hA (by simpa using h16)
    (le_normalizer_oddCoreIn_centralizingLayer hΩ hA ha)
    (Nat.coprime_two_left.mpr (odd_card_oddCoreIn _))
  conv_lhs => rw [← hgen]
  exact iSup₂_le fun E₀ hE₀ => le_rankThreeSpan_of_le_centralizer hE₀ inf_le_right

theorem centralizingLayer_le_rankThreeSpan [Finite G] (hΩ : ConjInvariant Ω)
    (hA : IsElemAbelian 2 A) (h16 : 16 ≤ Nat.card A) {a : G} (ha : a ∈ A)
    (hgen : CentralizerGenerationModO Ω A a) : centralizingLayer Ω {a} ≤ rankThreeSpan A :=
  hgen.trans (sup_le (oddCoreIn_centralizingLayer_le_rankThreeSpan hΩ hA h16 ha)
    (iSup₂_le fun _ hE₀ => le_rankThreeSpan_of_le_centralizer hE₀ inf_le_left))

end CFSG.ClassicalInvolution.Generic.DeltaClosure
