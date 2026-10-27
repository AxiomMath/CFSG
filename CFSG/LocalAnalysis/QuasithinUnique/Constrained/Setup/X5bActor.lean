module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X35Interface
public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents

public section

namespace CFSG.QuasithinUnique.Setup.X5

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X35 CFSG.Quasithin
  CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification

@[expose] def ActorComponentSection : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (H T M E : Subgroup (MulAut V)),
    ActorBase V H T M E → ¬ Group.IsSolvable H →
    ∀ L : Subgroup (MulAut V), IsComponentIn L H →
      ∃ (W : Type) (_ : CommGroup W) (_ : Finite W) (ρ : L →* MulAut W)
        (A₀ : Subgroup (MulAut W)),
        (∀ w : W, w * w = 1) ∧ Nontrivial W ∧ ρ.range ≠ ⊥ ∧
        (∀ U : Subgroup W, (∀ g ∈ ρ.range, ∀ u ∈ U, g u ∈ U) → U = ⊥ ∨ U = ⊤) ∧
        A₀ ≠ ⊥ ∧ IsElemAbelian2 A₀ ∧ A₀ ≤ Subgroup.normalizer (ρ.range : Set (MulAut W)) ∧
        Nat.card W ≤ Nat.card A₀ * Nat.card (fixV A₀)

@[expose] def EvenUnitaryThreeNoOffender : Prop :=
  ∀ (f : ℕ), 2 ≤ f → ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w * w = 1) → Nontrivial W →
    ∀ (L₀ A₀ : Subgroup (MulAut W)), Group.IsPerfect L₀ →
      (∀ U : Subgroup W, (∀ g ∈ L₀, ∀ u ∈ U, g u ∈ U) → U = ⊥ ∨ U = ⊤) →
      CFSG.Assembly.LowTwoRank.StatedClassicalModel (L₀ ⧸ Subgroup.center L₀) .PSU 3 2 f →
      A₀ ≠ ⊥ → IsElemAbelian2 A₀ → A₀ ≤ Subgroup.normalizer (L₀ : Set (MulAut W)) →
      Nat.card A₀ * Nat.card (fixV A₀) < Nat.card W


theorem map_center_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) :
    (Subgroup.center G).map e.toMonoidHom = Subgroup.center H := by
  ext y
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Subgroup.mem_center_iff] at hx ⊢
    intro g
    obtain ⟨g', rfl⟩ := e.surjective g
    show e g' * e x = e x * e g'
    rw [← map_mul, ← map_mul, hx g']
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    rw [Subgroup.mem_center_iff] at hy ⊢
    intro g
    apply e.injective
    rw [map_mul, map_mul, e.apply_symm_apply]
    exact hy (e g)

theorem quasisimple_range_centerQuotientEquiv {Q H : Type*} [Group Q] [Group H]
    (hQ : CFSG.IsQuasisimple Q) (ρ : Q →* H) (h0 : ρ.range ≠ ⊥) :
    CFSG.IsQuasisimple ρ.range ∧
      Nonempty ((ρ.range ⧸ Subgroup.center ρ.range) ≃* (Q ⧸ Subgroup.center Q)) := by
  have hker : ρ.ker ≤ Subgroup.center Q := by
    rcases quasisimple_normal_subgroups hQ ρ.normal_ker with h | h
    · exact absurd (by rw [MonoidHom.range_eq_bot_iff, ← MonoidHom.ker_eq_top_iff]; exact h) h0
    · exact h
  obtain ⟨hqs, -, hmap⟩ := quasisimple_central_quotient hQ hker
  let e₁ : Q ⧸ ρ.ker ≃* ρ.range := QuotientGroup.quotientKerEquivRange ρ
  refine ⟨(isQuasisimple_congr e₁).1 hqs, ⟨?_⟩⟩
  have hc : (Subgroup.center (Q ⧸ ρ.ker)).map e₁.toMonoidHom = Subgroup.center ρ.range :=
    map_center_mulEquiv e₁
  have h1 : (Q ⧸ ρ.ker) ⧸ Subgroup.center (Q ⧸ ρ.ker) ≃* ρ.range ⧸ Subgroup.center ρ.range :=
    QuotientGroup.congr _ _ e₁ hc
  have h2 : (Q ⧸ ρ.ker) ⧸ (Subgroup.center Q).map (QuotientGroup.mk' ρ.ker) ≃* Q ⧸ Subgroup.center Q :=
    QuotientGroup.quotientQuotientEquivQuotient ρ.ker (Subgroup.center Q) hker
  have h3 : (Q ⧸ ρ.ker) ⧸ Subgroup.center (Q ⧸ ρ.ker) ≃*
      (Q ⧸ ρ.ker) ⧸ (Subgroup.center Q).map (QuotientGroup.mk' ρ.ker) :=
    QuotientGroup.quotientMulEquivOfEq hmap
  exact h1.symm.trans (h3.trans h2)


theorem no_even_unitary_three_component (hSec : ActorComponentSection)
    (hN : EvenUnitaryThreeNoOffender) {V : Type} [CommGroup V] [Finite V]
    {H T M E : Subgroup (MulAut V)} (hA : ActorBase V H T M E) (hns : ¬ Group.IsSolvable H)
    {L : Subgroup (MulAut V)} (hL : IsComponentIn L H) (f : ℕ) :
    ¬ CFSG.Assembly.LowTwoRank.StatedClassicalModel (L ⧸ Subgroup.center L) .PSU 3 2 f := by
  intro hmodel
  obtain ⟨W, hWg, hWf, ρ, A₀, helem, hnt, h0, hirr, hA0, hAe, hAn, hoff⟩ :=
    hSec V H T M E hA hns L hL
  have hqL : CFSG.IsQuasisimple L :=
    (isQuasisimple_congr (Subgroup.subgroupOfEquivOfLe hL.1)).mp hL.2.1
  obtain ⟨hq0, ⟨e⟩⟩ := quasisimple_range_centerQuotientEquiv hqL ρ h0
  have hf : 2 ≤ f := by
    obtain ⟨-, h1, -, h3⟩ := hmodel.1
    by_contra hlt
    have : f = 1 := by omega
    subst this
    exact h3 (by norm_num)
  have hmodel0 := CFSG.SectionRank.statedClassicalModel_of_mulEquiv e hmodel
  have := hN f hf W helem hnt ρ.range A₀ hq0.1 hirr hmodel0 hA0 hAe hAn
  omega

theorem no_even_unitary_three_component_of_ffActor (hSec : ActorComponentSection)
    (hN : EvenUnitaryThreeNoOffender) {V : Type} [CommGroup V] [Finite V]
    {H T M E : Subgroup (MulAut V)} (hA : FFActor V H T M E) (hns : ¬ Group.IsSolvable H)
    {L : Subgroup (MulAut V)} (hL : IsComponentIn L H) (f : ℕ) :
    ¬ CFSG.Assembly.LowTwoRank.StatedClassicalModel (L ⧸ Subgroup.center L) .PSU 3 2 f :=
  no_even_unitary_three_component hSec hN (ActorBase.of_ffActor hA) hns hL f

end CFSG.QuasithinUnique.Setup.X5
