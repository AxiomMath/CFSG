module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lTCBasic
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lTCOrder
public import CFSG.LocalAnalysis.ComponentClassification.FiveCatEvenBasic

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open CFSG Subgroup CFSG.Blueprint CFSG.ComponentClassification
  CFSG.ComponentClassification.CatLeaf CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.SolMax.FiveCat.Even (EvenFiveInner)

@[expose] def EvenTCList (τ : Open.StatedLieTag) (n f : ℕ) : Prop :=
  (τ = .PSL ∧ n = 4 ∧ f = 1) ∨ (τ = .PSL ∧ n = 4 ∧ f = 2) ∨ (τ = .PSL ∧ n = 5 ∧ f = 1) ∨
    (τ = .PSU ∧ n = 4 ∧ f = 1) ∨ (τ = .PSU ∧ n = 5 ∧ f = 1) ∨ (τ = .PSp ∧ n = 2 ∧ f = 2) ∨
    (τ = .G2 ∧ n = 0 ∧ f = 2)

@[expose] def EvenTCConc (τ : Open.StatedLieTag) (n f : ℕ) {X : Type} [Group X]
    (P : Subgroup X) : Prop :=
  TCSmall (P ⧸ Open.fusionZStar P) → EvenTCList τ n f

@[expose] def EvenTCOuter (τ : Open.StatedLieTag) : Prop :=
  ∀ (K : Type) [Group K] (n f : ℕ), Open.StatedLieAdmissible τ n 2 f →
    Blueprint.LieModel K τ n 2 f → ∀ α : MulAut K, orderOf α = 2 →
    α ∉ (MulAut.conj : K →* MulAut K).range →
    ∀ P : Subgroup (fixedSubgroup α), IsPComponent 2 P → EvenTCConc τ n f P

theorem EvenTCConc.of_model (hO : LieOrderFormulasInput) {τ : Open.StatedLieTag} {n f : ℕ}
    {X : Type} [Group X] {P : Subgroup X} {τ' : Open.StatedLieTag} {n' f' : ℕ}
    (hadm : Open.StatedLieAdmissible τ' n' 2 f')
    (hm : Blueprint.LieModel (P ⧸ Open.fusionZStar P) τ' n' 2 f')
    (himp : τ' = .PSU → n' = 4 → f' = 1 → EvenTCList τ n f) : EvenTCConc τ n f P := by
  intro hS
  obtain ⟨-, h1, h2, h3⟩ := a2l_lieModel_two_card hO hadm hm (a2l_card_tcSmall hS)
  exact himp h1 h2 h3

theorem EvenTCConc.of_model_ne (hO : LieOrderFormulasInput) {τ : Open.StatedLieTag} {n f : ℕ}
    {X : Type} [Group X] {P : Subgroup X} {τ' : Open.StatedLieTag} {n' f' : ℕ}
    (hadm : Open.StatedLieAdmissible τ' n' 2 f')
    (hm : Blueprint.LieModel (P ⧸ Open.fusionZStar P) τ' n' 2 f') (hne : τ' ≠ .PSU) :
    EvenTCConc τ n f P :=
  EvenTCConc.of_model hO hadm hm fun h => absurd h hne

theorem EvenTCConc.of_mulEquiv {τ : Open.StatedLieTag} {n f : ℕ} {X Y : Type} [Group X] [Group Y]
    [Finite X] [Finite Y] (Φ : X ≃* Y)
    (h : ∀ M : Subgroup Y, IsPComponent 2 M → EvenTCConc τ n f M) {P : Subgroup X}
    (hP : IsPComponent 2 P) : EvenTCConc τ n f P := by
  have hM := LocalAnalysis.ComponentInitial.isPComponent_map_of_isPComponent 2 Φ hP
  obtain ⟨eZ⟩ := GrSLit.nonempty_fusionZStar_equiv_of_mulEquiv'
    (P.equivMapOfInjective Φ.toMonoidHom Φ.injective)
  intro hS
  exact h _ hM (hS.of_mulEquiv eZ)

theorem EvenTCConc.of_simple {τ : Open.StatedLieTag} {n f : ℕ} {X Y : Type} [Group X] [Finite X]
    [Group Y] [IsSimpleGroup Y] (e : X ≃* Y) (hY : TCSmall Y → EvenTCList τ n f)
    {P : Subgroup X} (hP : IsPComponent 2 P) : EvenTCConc τ n f P := by
  have hXs : IsSimpleGroup X := e.isSimpleGroup
  have htop : P = ⊤ := GrSLit.eq_top_of_isPComponent_of_isSimpleGroup hP
  obtain ⟨eZ⟩ := GrSLit.nonempty_fusionZStar_equiv_of_simple hP
    (((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv).trans e)
  intro hS
  exact hY (hS.of_mulEquiv eZ)

theorem a2l_evenTCList_of_inner_outer {τ : Open.StatedLieTag} (hin : EvenFiveInner τ)
    (hout : EvenTCOuter τ) {S : Type} [Group S] [Finite S] (hs : IsSimpleGroup S)
    (hna : ∃ x y : S, x * y ≠ y * x) {n f : ℕ} (hL : Blueprint.LieModel S τ n 2 f)
    {σ : MulAut S} {P : Subgroup S} (h : ProperFixedComponent σ P)
    (hS : TCSmall (P ⧸ Open.fusionZStar P)) : EvenTCList τ n f := by
  have := hs
  have hσ1 := h.ne_one
  have hσ2 : orderOf σ = 2 :=
    orderOf_eq_prime (by rw [sq]; exact MulEquiv.ext fun y => h.1 y) hσ1
  rcases exists_conj_or_not_mem_range σ with ⟨t, ht⟩ | hout'
  · exfalso
    obtain ⟨ht2, -, hPc, -⟩ := h.inner hna ht
    exact hin S hna n f hL t ht2 _ hPc
  · obtain ⟨eL⟩ := GrSLit.nonempty_fusionZStar_equiv_of_mulEquiv' (subgroupOfEquivOfLe h.2.1)
    exact hout S n f hL.admissible hL σ hσ2 hout' _ h.2.2.1 (hS.of_mulEquiv eL.symm)

end CFSG.OddStandard.SmallF3.HypA2Leaves
