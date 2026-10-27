module

public import CFSG.GH74.Generic.S1.TQ3BadFrame

public section

namespace CFSG.GH74.Generic.S1

open Matrix CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.Assembly.LowTwoRank Subgroup CFSG.GH74.Generic
open CFSG.ClassicalInvolution.WeakCT CFSG.GH74.Filter.ClassicalOdd
open scoped MatrixGroups commutatorElement

section Frame

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F]

omit [Finite F] in
theorem exists_q3FrameB_data (hExact : S1LiftExactProp) {x : G} {K : Subgroup (CentralizerBar x)}
    (hset : S1Setup G x K) {u : Fin 4 → G} {hu : ∀ i, u i ∈ centralizer ({x} : Set G)}
    (hf : S1Frame x K u hu) (hlin : S1SymFrameLin x u F) :
    ∃ Fr : Q3FrameB G F, Fr.X = symX x u ∧
      ∀ e, S1Setup G (Fr.X e) (Fr.D e).K ∧ S1Front G (Fr.X e) (Fr.D e).K := by
  obtain ⟨hconj, hsq, hXc, hprod, hinj⟩ := symX_facts hset.shape.2 hset.inv hf
  have hw : ∀ e j, symX x u (e.succAbove j) ∈ centralizer ({symX x u e} : Set G) := fun e j =>
    mem_centralizer_singleton_iff.2 (hXc _ _)
  have hloc : ∀ e : Fin 5, ∃ (K' : Subgroup (CentralizerBar (symX x u e)))
      (hw' : ∀ j, symX x u (e.succAbove j) ∈ centralizer ({symX x u e} : Set G)),
        S1Setup G (symX x u e) K' ∧ S1Front G (symX x u e) K' ∧
        ∃ e' : ↥K' ≃* ↥(StatedSL 4 F), ∀ j, ActsAsReflOn e' (barOf (hw' j)) (reflDiag F j) := by
    intro e
    obtain ⟨K', hw', hset', hfront', -, e', he'⟩ := hlin e
    exact ⟨K', hw', hset', hfront', e', he'⟩
  choose D hDK hDact using sym_layerData hExact x u hw hloc
  refine ⟨⟨symX x u, D, hsq, ?_, hinj, hXc, hprod, fun e j => hDact e j, ?_, ?_⟩, rfl, ?_⟩
  · intro e h
    have h1 := hconj e
    rw [h] at h1
    have : x = 1 := isConj_one_right.1 h1.symm
    have := hset.inv
    rw [‹x = 1›, orderOf_one] at this
    exact absurd this (by norm_num)
  · intro e
    obtain ⟨K', hw', hset', hfront', -⟩ := hlin e
    rw [(hDK e).trans hfront'.layer_eq]
    exact hfront'.cent_eq
  · intro e
    obtain ⟨K', hw', hset', hfront', -⟩ := hlin e
    rw [(hDK e).trans hfront'.layer_eq]
    exact hset'.shape.2
  · intro e
    obtain ⟨K', hw', hset', hfront', -⟩ := hlin e
    show S1Setup G (symX x u e) (D e).K ∧ S1Front G (symX x u e) (D e).K
    rw [(hDK e).trans hfront'.layer_eq]
    exact ⟨hset', hfront'⟩

end Frame

end CFSG.GH74.Generic.S1
