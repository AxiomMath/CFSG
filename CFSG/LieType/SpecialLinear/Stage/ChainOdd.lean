module

public import CFSG.LieType.SpecialLinear.Stage.Block222False
public import CFSG.LieType.SpecialLinear.Stage.GraphThree
public import CFSG.LieType.SpecialLinear.Stage.TwoEnd

public section

namespace CFSG.LieType.SpecialLinear

open Matrix CFSG.Quasithin.SmithCurtis
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw
open CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
open CFSG.Theory.Representation
open scoped TensorProduct

noncomputable section

theorem stage_odd_false (j : ℕ) {F : Type} [Field F] [Fintype F] [CharP F 2]
    (hq : 4 ≤ Fintype.card F)
    {E : Type} [Field E] [Fintype E] [CharP E 2] [Algebra (ZMod 2) E]
    {k : Type} [Field k] [CharP k 2] [Algebra E k] [Algebra F k]
    {D : Type} [Group D] [Finite D]
    {X : Type} [AddCommGroup X] [Module (ZMod 2) X] [Module E X]
    [IsScalarTower (ZMod 2) E X] [Finite X]
    (σ : Representation E (SpecialLinearGroup (Fin (2 * j + 3)) F) X)
    (hsimp : IsSimpleRep (extendScalars k σ))
    {y : k ⊗[E] X} {χ : SpecialLinearGroup (Fin (2 * j + 3)) F → k}
    {J : Finset (Fin (2 * j + 2))}
    (ht : IsCoverType (rankOne (2 * j + 2) F 2) (extendScalars k σ) y χ J)
    (hJ : ∃ s, s ∉ J)
    (δ : Representation (ZMod 2) D X)
    (hδE : ∀ d (c : E) (x : X), δ d (c • x) = c • δ d x)
    (hD : IsPGroup 2 D) (hD2 : ∀ d, δ d * δ d = 1)
    (hquad : ∀ a b x, δ b (δ a x - x) = δ a x - x)
    (hcompat : ∀ d, ∃ A : GL (Fin (2 * j + 3)) F, IsUpperGL A ∧
      ∃ (τ : F ≃+* F) (ε : ℕ),
        ∀ g x, δ d (σ g x) = σ (borelStd (2 * j + 3) F A τ ε g) (δ d x))
    (hgraph : ∃ d, ∃ A : GL (Fin (2 * j + 3)) F, IsUpperGL A ∧ ∃ τ : F ≃+* F,
      ∀ g x, δ d (σ g x) = σ (borelStd (2 * j + 3) F A τ 1 g) (δ d x))
    (hered : ∀ Z : Submodule (ZMod 2) X, (∀ d, ∀ z ∈ Z, δ d z ∈ Z) →
      IsOffenderOn δ ⊤ Z) : False := by
  classical
  induction j generalizing E k X with
  | zero =>
      obtain ⟨s, hs⟩ := hJ
      obtain ⟨g, hg⟩ := exists_ne_one_of_not_mem_isCoverType (n := 2) (p := 2)
        (F := F) (V := k ⊗[E] X) (ρ := extendScalars k σ) ht (s := s) hs
      obtain ⟨g, hg'⟩ := exists_ne_one_of_extendScalars (E := E) (k := k) σ ⟨g, hg⟩
      exact stage_three_false (F := F) (E := E) (k := k) (D := D) (X := X) hq σ hsimp
        ⟨g, hg'⟩ δ hδE hD hD2 hcompat hgraph hered
  | succ j ih =>
      by_cases h0 : (⟨0, by omega⟩ : Fin (2 * (j + 1) + 2)) ∉ J
      · exact stage_block222_false (c := 2 * j + 1) hq σ hsimp ht δ hδE hD hD2 hquad
          hcompat hgraph hered h0
      · push Not at h0
        have hends := stage_ends_mem (c := 2 * j + 1) hq σ hsimp ht δ hδE hD hD2 hquad
          hcompat hgraph hered
        obtain ⟨hend0, hendl⟩ := hends
        obtain ⟨s, hs⟩ := hJ
        have hs0 : s ≠ 0 := by
          intro h
          apply hs
          rw [h]
          exact hend0
        have hslast : s ≠ (⟨2 * j + 3, by omega⟩ : Fin (2 * (j + 1) + 2)) := by
          intro h
          apply hs
          rw [h]
          exact hendl
        obtain ⟨t, rfl⟩ := Fin.exists_succ_eq.mpr hs0
        have htlast : t ≠ Fin.last (2 * j + 2) := by
          intro h
          apply hslast
          rw [h, Fin.succ_last]
          apply Fin.ext
          rfl
        obtain ⟨s', rfl⟩ := Fin.eq_castSucc_of_ne_last htlast
        have hJ' : ∃ u : Fin (2 * j + 2),
            u ∉ (Finset.univ.filter fun v : Fin (2 * j + 2) =>
              v.castSucc.succ ∈ J) := by
          refine ⟨s', ?_⟩
          intro hs'
          apply hs
          simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hs'
        have hsimp' : IsSimpleRep (extendScalars k (twoEndRestrict (2 * j + 2) F σ)) :=
          stage_twoEnd_isSimpleRep (m := 2 * j + 2) σ hsimp ht
        obtain ⟨y', ht'⟩ := stage_twoEnd_isCoverType (m := 2 * j + 2) σ ht
        have hδE' : ∀ d (c : E) (x : twoEndFix (2 * j + 2) F σ),
            stageRestrict δ (twoEndFix (2 * j + 2) F σ)
              (twoEndFix_actor_mem hδE hcompat) d (c • x) =
            c • stageRestrict δ (twoEndFix (2 * j + 2) F σ)
              (twoEndFix_actor_mem hδE hcompat) d x :=
          stageRestrict_smul δ hδE (twoEndFix (2 * j + 2) F σ)
            (twoEndFix_actor_mem hδE hcompat)
        have hD2' : ∀ d, stageRestrict δ (twoEndFix (2 * j + 2) F σ)
              (twoEndFix_actor_mem hδE hcompat) d *
            stageRestrict δ (twoEndFix (2 * j + 2) F σ)
              (twoEndFix_actor_mem hδE hcompat) d = 1 :=
          stageRestrict_mul_self δ hD2 (twoEndFix (2 * j + 2) F σ)
            (twoEndFix_actor_mem hδE hcompat)
        have hquad' : ∀ a b (x : twoEndFix (2 * j + 2) F σ),
            stageRestrict δ (twoEndFix (2 * j + 2) F σ)
                (twoEndFix_actor_mem hδE hcompat) b
              (stageRestrict δ (twoEndFix (2 * j + 2) F σ)
                (twoEndFix_actor_mem hδE hcompat) a x - x) =
            stageRestrict δ (twoEndFix (2 * j + 2) F σ)
              (twoEndFix_actor_mem hδE hcompat) a x - x :=
          stageRestrict_quad δ hquad (twoEndFix (2 * j + 2) F σ)
            (twoEndFix_actor_mem hδE hcompat)
        have hcompat' := twoEnd_actor_compat (m := 2 * j + 2) hδE hcompat
        have hgraph' := twoEnd_actor_graph (m := 2 * j + 2) hδE hcompat hgraph
        have hered' : ∀ Z : Submodule (ZMod 2) (twoEndFix (2 * j + 2) F σ),
            (∀ d, ∀ z ∈ Z, stageRestrict δ (twoEndFix (2 * j + 2) F σ)
              (twoEndFix_actor_mem hδE hcompat) d z ∈ Z) →
            IsOffenderOn (stageRestrict δ (twoEndFix (2 * j + 2) F σ)
              (twoEndFix_actor_mem hδE hcompat)) ⊤ Z :=
          stageRestrict_hered δ (twoEndFix (2 * j + 2) F σ)
            (twoEndFix_actor_mem hδE hcompat) hered
        exact ih (X := twoEndFix (2 * j + 2) F σ)
          (twoEndRestrict (2 * j + 2) F σ) hsimp' ht' hJ'
          (stageRestrict δ (twoEndFix (2 * j + 2) F σ)
            (twoEndFix_actor_mem hδE hcompat)) hδE' hD2' hquad' hcompat' hgraph' hered'


end

end CFSG.LieType.SpecialLinear
