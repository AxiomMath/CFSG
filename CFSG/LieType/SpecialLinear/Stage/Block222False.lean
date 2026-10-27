module

public import CFSG.LieType.SpecialLinear.Stage.GraphSymmetry
public import CFSG.LieType.SpecialLinear.Stage.Block222
public import CFSG.LieType.SpecialLinear.SL2SwapCommuting

public section

namespace CFSG.LieType.SpecialLinear

open Matrix CFSG.Quasithin.SmithCurtis
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw
open CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
open CFSG.Theory.Representation
open scoped TensorProduct

noncomputable section

variable {F : Type} [Field F] [Fintype F] [CharP F 2]
  {E : Type} [Field E] [Fintype E] [CharP E 2] [Algebra (ZMod 2) E]
  {k : Type} [Field k] [CharP k 2] [Algebra E k] [Algebra F k]
  {D : Type} [Group D] [Finite D]
  {c : ℕ} {X : Type} [AddCommGroup X] [Module (ZMod 2) X] [Module E X]
  [IsScalarTower (ZMod 2) E X] [Finite X]

theorem stage_block222_false (hq : 4 ≤ Fintype.card F)
    (σ : Representation E (SpecialLinearGroup (Fin (c + 4)) F) X)
    (hsimp : IsSimpleRep (extendScalars k σ))
    {y : k ⊗[E] X} {χ : SpecialLinearGroup (Fin (c + 4)) F → k} {J : Finset (Fin (c + 3))}
    (ht : IsCoverType (rankOne (c + 3) F 2) (extendScalars k σ) y χ J)
    (δ : Representation (ZMod 2) D X)
    (hδE : ∀ d (c : E) (x : X), δ d (c • x) = c • δ d x)
    (hD : IsPGroup 2 D) (hD2 : ∀ d, δ d * δ d = 1)
    (hquad : ∀ a b x, δ b (δ a x - x) = δ a x - x)
    (hcompat : ∀ d, ∃ A : GL (Fin (c + 4)) F, IsUpperGL A ∧
      ∃ (τ : F ≃+* F) (ε : ℕ),
        ∀ g x, δ d (σ g x) = σ (borelStd (c + 4) F A τ ε g) (δ d x))
    (hgraph : ∃ d, ∃ A : GL (Fin (c + 4)) F, IsUpperGL A ∧ ∃ τ : F ≃+* F,
      ∀ g x, δ d (σ g x) = σ (borelStd (c + 4) F A τ 1 g) (δ d x))
    (hered : ∀ Z : Submodule (ZMod 2) X, (∀ d, ∀ z ∈ Z, δ d z ∈ Z) →
      IsOffenderOn δ ⊤ Z)
    (h0 : (⟨0, by omega⟩ : Fin (c + 3)) ∉ J) : False := by
  classical
  have hlast : (⟨c + 2, by omega⟩ : Fin (c + 3)) ∉ J := by
    intro hmem
    apply h0
    have hEq : Fin.rev (⟨0, by omega⟩ : Fin (c + 3)) =
        (⟨c + 2, by omega⟩ : Fin (c + 3)) := by
      apply Fin.ext
      rfl
    exact (stage_mem_iff_rev_mem (n := c + 3) σ hsimp ht δ hδE hD2 hgraph
      (⟨0, by omega⟩ : Fin (c + 3))).mpr (by simpa only [hEq] using hmem)
  let X' : Submodule E X := blockFix222 c F σ
  have hX' : ∀ d, ∀ x ∈ X', δ d x ∈ X' := blockFix222_actor_mem hδE hcompat
  let σ' : Representation E (SpecialLinearGroup (Fin 2) F ×
      SpecialLinearGroup (Fin c) F × SpecialLinearGroup (Fin 2) F) X' :=
    blockRestrict222 c F σ
  let σ₂ : Representation (ZMod 2) (SpecialLinearGroup (Fin 2) F ×
      SpecialLinearGroup (Fin c) F × SpecialLinearGroup (Fin 2) F) X' :=
    { toFun := fun m => (σ' m).restrictScalars (ZMod 2)
      map_one' := by
        rw [map_one]
        rfl
      map_mul' := by
        intro g h
        rw [map_mul]
        rfl }
  have hσE : ∀ m (a : E) (x : X'), σ₂ m (a • x) = a • σ₂ m x := by
    intro m a x
    change (σ' m) (a • x) = a • (σ' m) x
    exact (σ' m).map_smul a x
  have hsimp' : ∀ W : Submodule E X', (∀ m, ∀ w ∈ W, σ₂ m w ∈ W) →
      W = ⊥ ∨ W = ⊤ := by
    intro W hW
    exact (stage_block222_isSimpleRep (c := c) (F := F) σ hsimp ht).2 W
      (fun m w hw => hW m w hw)
  have h₁ : ∃ g : SpecialLinearGroup (Fin 2) F, σ₂ (g, 1, 1) ≠ 1 := by
    obtain ⟨g, hg⟩ := stage_block222_left_ne_one (c := c) (F := F) σ ht h0
    refine ⟨g, fun h => hg ?_⟩
    apply LinearMap.ext
    intro x
    exact congrArg (fun f : X' →ₗ[ZMod 2] X' => f x) h
  have h₃ : ∃ g : SpecialLinearGroup (Fin 2) F, σ₂ (1, 1, g) ≠ 1 := by
    obtain ⟨g, hg⟩ := stage_block222_right_ne_one (c := c) (F := F) σ ht hlast
    refine ⟨g, fun h => hg ?_⟩
    apply LinearMap.ext
    intro x
    exact congrArg (fun f : X' →ₗ[ZMod 2] X' => f x) h
  let δ' : Representation (ZMod 2) D X' := stageRestrict δ X' hX'
  have hD2' : ∀ d, δ' d * δ' d = 1 := by
    intro d
    exact stageRestrict_mul_self δ hD2 X' hX' d
  have hquad' : ∀ a b (x : X'), δ' b (δ' a x - x) = δ' a x - x := by
    intro a b x
    exact stageRestrict_quad δ hquad X' hX' a b x
  have hcompat' : ∀ d, ∃ (A₁ A₃ : GL (Fin 2) F) (τ : F ≃+* F) (sw : Bool)
      (β : SpecialLinearGroup (Fin c) F →* SpecialLinearGroup (Fin c) F),
      ∀ g₁ g₂ g₃ x,
        δ' d (σ₂ (g₁, g₂, g₃) x) =
          σ₂ ((pairAut A₁ A₃ τ sw (g₁, g₃)).1, β g₂,
            (pairAut A₁ A₃ τ sw (g₁, g₃)).2) (δ' d x) := by
    intro d
    obtain ⟨A₁, A₃, τ, sw, β, hd⟩ := block222_actor_compat hδE hcompat d
    exact ⟨A₁, A₃, τ, sw, β, fun g₁ g₂ g₃ x => by
      dsimp only [δ', σ₂, σ', X', hX']
      exact hd g₁ g₂ g₃ x⟩
  have hswap' : ∃ d, ∃ (A₁ A₃ : GL (Fin 2) F) (τ : F ≃+* F)
      (β : SpecialLinearGroup (Fin c) F →* SpecialLinearGroup (Fin c) F),
      ∀ g₁ g₂ g₃ x,
        δ' d (σ₂ (g₁, g₂, g₃) x) =
          σ₂ ((pairAut A₁ A₃ τ true (g₁, g₃)).1, β g₂,
            (pairAut A₁ A₃ τ true (g₁, g₃)).2) (δ' d x) := by
    obtain ⟨d, A₁, A₃, τ, β, hd⟩ := block222_actor_swap hδE hcompat hgraph
    exact ⟨d, A₁, A₃, τ, β, fun g₁ g₂ g₃ x => by
      dsimp only [δ', σ₂, σ', X', hX']
      exact hd g₁ g₂ g₃ x⟩
  have hered' : ∀ Z : Submodule (ZMod 2) X', (∀ d, ∀ z ∈ Z, δ' d z ∈ Z) →
      IsOffenderOn δ' ⊤ Z := by
    intro Z hZ
    exact stageRestrict_hered δ X' hX' hered Z hZ
  exact sl2Triple_swap_false (F := F) (E := E) (G := SpecialLinearGroup (Fin c) F)
    (X := X') (D := D) hq σ₂ hσE hsimp' h₁ h₃ δ' hD hD2' hquad' hcompat' hswap' hered'


theorem stage_ends_mem (hq : 4 ≤ Fintype.card F)
    (σ : Representation E (SpecialLinearGroup (Fin (c + 4)) F) X)
    (hsimp : IsSimpleRep (extendScalars k σ))
    {y : k ⊗[E] X} {χ : SpecialLinearGroup (Fin (c + 4)) F → k} {J : Finset (Fin (c + 3))}
    (ht : IsCoverType (rankOne (c + 3) F 2) (extendScalars k σ) y χ J)
    (δ : Representation (ZMod 2) D X)
    (hδE : ∀ d (c : E) (x : X), δ d (c • x) = c • δ d x)
    (hD : IsPGroup 2 D) (hD2 : ∀ d, δ d * δ d = 1)
    (hquad : ∀ a b x, δ b (δ a x - x) = δ a x - x)
    (hcompat : ∀ d, ∃ A : GL (Fin (c + 4)) F, IsUpperGL A ∧
      ∃ (τ : F ≃+* F) (ε : ℕ),
        ∀ g x, δ d (σ g x) = σ (borelStd (c + 4) F A τ ε g) (δ d x))
    (hgraph : ∃ d, ∃ A : GL (Fin (c + 4)) F, IsUpperGL A ∧ ∃ τ : F ≃+* F,
      ∀ g x, δ d (σ g x) = σ (borelStd (c + 4) F A τ 1 g) (δ d x))
    (hered : ∀ Z : Submodule (ZMod 2) X, (∀ d, ∀ z ∈ Z, δ d z ∈ Z) →
      IsOffenderOn δ ⊤ Z) :
    (⟨0, by omega⟩ : Fin (c + 3)) ∈ J ∧ (⟨c + 2, by omega⟩ : Fin (c + 3)) ∈ J := by
  classical
  constructor
  · by_contra h0
    exact stage_block222_false hq σ hsimp ht δ hδE hD hD2 hquad hcompat hgraph hered h0
  · by_contra hl
    have h0 : (⟨0, by omega⟩ : Fin (c + 3)) ∉ J := by
      intro h
      have hrev := (stage_mem_iff_rev_mem (n := c + 3) σ hsimp ht δ hδE hD2 hgraph
        (⟨0, by omega⟩ : Fin (c + 3))).mp h
      have hEq : Fin.rev (⟨0, by omega⟩ : Fin (c + 3)) =
          (⟨c + 2, by omega⟩ : Fin (c + 3)) := by
        apply Fin.ext
        rfl
      exact hl (by simpa only [← hEq] using hrev)
    exact stage_block222_false hq σ hsimp ht δ hδE hD hD2 hquad hcompat hgraph hered h0


end

end CFSG.LieType.SpecialLinear
