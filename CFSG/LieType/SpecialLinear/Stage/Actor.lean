module

public import CFSG.LieType.SpecialLinear.Stage.Restrict
public import CFSG.LieType.SpecialLinear.TwoEnd.Automorphism
public import CFSG.LieType.SpecialLinear.Block222.Borel.Intertwine
public import CFSG.LieType.SpecialLinear.Block222.Section
public import CFSG.LieType.SpecialLinear.SL2Swap.Basic

public section

namespace CFSG.LieType.SpecialLinear

open Matrix CFSG.Quasithin.SmithCurtis

noncomputable section

variable {F : Type} [Field F]
  {E : Type} [Field E] [Algebra (ZMod 2) E]
  {X D : Type} [AddCommGroup X] [Module (ZMod 2) X] [Module E X]
    [IsScalarTower (ZMod 2) E X] [Group D]

@[expose] noncomputable def actorLin (δ : Representation (ZMod 2) D X)
    (hδE : ∀ d (c : E) (x : X), δ d (c • x) = c • δ d x) (d : D) : X →ₗ[E] X where
  toFun := δ d
  map_add' := (δ d).map_add
  map_smul' := hδE d

omit [Algebra (ZMod 2) E] [IsScalarTower (ZMod 2) E X] in
@[simp]
theorem actorLin_apply (δ : Representation (ZMod 2) D X)
    (hδE : ∀ d (c : E) (x : X), δ d (c • x) = c • δ d x) (d : D) (x : X) :
    actorLin δ hδE d x = δ d x :=
  rfl

@[simp]
theorem borelGraph_two_apply [CharP F 2] (g : SpecialLinearGroup (Fin 2) F) :
    borelGraph 2 F g = g := by
  rw [borelGraph_two_eq_one]
  rfl

section TwoEnd

variable {m : ℕ} {σ : Representation E (SpecialLinearGroup (Fin (m + 3)) F) X}
  {δ : Representation (ZMod 2) D X}

omit [Algebra (ZMod 2) E] [IsScalarTower (ZMod 2) E X] in
theorem twoEndFix_actor_mem
    (hδE : ∀ d (c : E) (x : X), δ d (c • x) = c • δ d x)
    (hcompat : ∀ d, ∃ A : GL (Fin (m + 3)) F, IsUpperGL A ∧
      ∃ (τ : F ≃+* F) (ε : ℕ),
        ∀ g x, δ d (σ g x) = σ (borelStd (m + 3) F A τ ε g) (δ d x)) :
    ∀ d, ∀ x ∈ twoEndFix m F σ, δ d x ∈ twoEndFix m F σ := by
  intro d x hx
  obtain ⟨A, hA, τ, ε, hd⟩ := hcompat d
  exact (twoEnd_intertwine_apply m F hA τ ε σ (actorLin δ hδE d) hd).1 x hx

theorem twoEnd_actor_compat
    (hδE : ∀ d (c : E) (x : X), δ d (c • x) = c • δ d x)
    (hcompat : ∀ d, ∃ A : GL (Fin (m + 3)) F, IsUpperGL A ∧
      ∃ (τ : F ≃+* F) (ε : ℕ),
        ∀ g x, δ d (σ g x) = σ (borelStd (m + 3) F A τ ε g) (δ d x)) :
    ∀ d, ∃ A' : GL (Fin (m + 1)) F, IsUpperGL A' ∧ ∃ (τ : F ≃+* F) (ε : ℕ),
      ∀ g x,
        stageRestrict δ (twoEndFix m F σ) (twoEndFix_actor_mem hδE hcompat) d
            (twoEndRestrict m F σ g x) =
          twoEndRestrict m F σ (borelStd (m + 1) F A' τ ε g)
            (stageRestrict δ (twoEndFix m F σ) (twoEndFix_actor_mem hδE hcompat) d x) := by
  intro d
  obtain ⟨A, hA, τ, ε, hd⟩ := hcompat d
  refine ⟨midGL m F A hA, isUpperGL_midGL m F hA, τ, ε, ?_⟩
  intro g x
  apply Subtype.ext
  have h := (twoEnd_intertwine_apply m F hA τ ε σ (actorLin δ hδE d) hd).2 g x x.2
  simpa only [coe_stageRestrict_apply, twoEndRestrict, restrictRep_apply,
    MonoidHom.comp_apply, actorLin_apply] using h

theorem twoEnd_actor_graph
    (hδE : ∀ d (c : E) (x : X), δ d (c • x) = c • δ d x)
    (hcompat : ∀ d, ∃ A : GL (Fin (m + 3)) F, IsUpperGL A ∧
      ∃ (τ : F ≃+* F) (ε : ℕ),
        ∀ g x, δ d (σ g x) = σ (borelStd (m + 3) F A τ ε g) (δ d x))
    (hgraph : ∃ d, ∃ A : GL (Fin (m + 3)) F, IsUpperGL A ∧ ∃ τ : F ≃+* F,
      ∀ g x, δ d (σ g x) = σ (borelStd (m + 3) F A τ 1 g) (δ d x)) :
    ∃ d, ∃ A' : GL (Fin (m + 1)) F, IsUpperGL A' ∧ ∃ τ : F ≃+* F,
      ∀ g x,
        stageRestrict δ (twoEndFix m F σ) (twoEndFix_actor_mem hδE hcompat) d
            (twoEndRestrict m F σ g x) =
          twoEndRestrict m F σ (borelStd (m + 1) F A' τ 1 g)
            (stageRestrict δ (twoEndFix m F σ) (twoEndFix_actor_mem hδE hcompat) d x) := by
  obtain ⟨d, A, hA, τ, hd⟩ := hgraph
  refine ⟨d, midGL m F A hA, isUpperGL_midGL m F hA, τ, ?_⟩
  intro g x
  apply Subtype.ext
  have h := (twoEnd_intertwine_apply m F hA τ 1 σ (actorLin δ hδE d) hd).2 g x x.2
  simpa only [coe_stageRestrict_apply, twoEndRestrict, restrictRep_apply,
    MonoidHom.comp_apply, actorLin_apply] using h

end TwoEnd

section Block

variable {c : ℕ} {σ : Representation E (SpecialLinearGroup (Fin (c + 4)) F) X}
  {δ : Representation (ZMod 2) D X}

omit [Algebra (ZMod 2) E] [IsScalarTower (ZMod 2) E X] in
theorem blockFix222_actor_mem
    (hδE : ∀ d (c : E) (x : X), δ d (c • x) = c • δ d x)
    (hcompat : ∀ d, ∃ A : GL (Fin (c + 4)) F, IsUpperGL A ∧
      ∃ (τ : F ≃+* F) (ε : ℕ),
        ∀ g x, δ d (σ g x) = σ (borelStd (c + 4) F A τ ε g) (δ d x)) :
    ∀ d, ∀ x ∈ blockFix222 c F σ, δ d x ∈ blockFix222 c F σ := by
  intro d x hx
  obtain ⟨A, hA, τ, ε, hd⟩ := hcompat d
  exact (block222_intertwine_apply c F A τ ε hA σ (actorLin δ hδE d) hd).1 x hx

theorem block222_actor_compat [CharP F 2]
    (hδE : ∀ d (c : E) (x : X), δ d (c • x) = c • δ d x)
    (hcompat : ∀ d, ∃ A : GL (Fin (c + 4)) F, IsUpperGL A ∧
      ∃ (τ : F ≃+* F) (ε : ℕ),
        ∀ g x, δ d (σ g x) = σ (borelStd (c + 4) F A τ ε g) (δ d x)) :
    ∀ d, ∃ (A₁ A₃ : GL (Fin 2) F) (τ : F ≃+* F) (sw : Bool)
      (β : SpecialLinearGroup (Fin c) F →* SpecialLinearGroup (Fin c) F),
      ∀ g₁ g₂ g₃ x,
        stageRestrict δ (blockFix222 c F σ) (blockFix222_actor_mem hδE hcompat) d
            (blockRestrict222 c F σ (g₁, g₂, g₃) x) =
          blockRestrict222 c F σ
            ((pairAut A₁ A₃ τ sw (g₁, g₃)).1, β g₂, (pairAut A₁ A₃ τ sw (g₁, g₃)).2)
            (stageRestrict δ (blockFix222 c F σ) (blockFix222_actor_mem hδE hcompat) d x) := by
  intro d
  obtain ⟨A, hA, τ, ε, hd⟩ := hcompat d
  rcases Nat.mod_two_eq_zero_or_one ε with hε | hε
  · refine ⟨blockGL1 c F A hA, blockGL3 c F A hA, τ, false,
      (CFSG.QuasithinUnique.K1.stdAut (blockGL2 c F A hA) τ 0).toMonoidHom, ?_⟩
    intro g₁ g₂ g₃ x
    apply Subtype.ext
    have h := (block222_intertwine_apply c F A τ ε hA σ (actorLin δ hδE d) hd).2
      (g₁, g₂, g₃) x x.2
    rw [blockStd222_apply_even c F A hA τ hε, blockStd222Even_apply] at h
    simpa only [coe_stageRestrict_apply, blockRestrict222, restrictRep_apply,
      MonoidHom.comp_apply, actorLin_apply, pairAut_false_apply, Prod.fst, Prod.snd,
      MulEquiv.coe_toMonoidHom] using h
  · refine ⟨blockGL1 c F A hA, blockGL3 c F A hA, τ, true,
      (CFSG.QuasithinUnique.K1.stdAut (blockGL2 c F A hA) τ 0).toMonoidHom.comp
        (borelGraph c F).toMonoidHom, ?_⟩
    intro g₁ g₂ g₃ x
    apply Subtype.ext
    have h := (block222_intertwine_apply c F A τ ε hA σ (actorLin δ hδE d) hd).2
      (g₁, g₂, g₃) x x.2
    rw [blockStd222_apply_odd c F A hA τ hε, blockStd222Odd_apply] at h
    simp only [borelGraph_two_apply] at h
    simpa only [coe_stageRestrict_apply, blockRestrict222, restrictRep_apply,
      MonoidHom.comp_apply, actorLin_apply, pairAut_true_apply, Prod.fst, Prod.snd,
      MulEquiv.coe_toMonoidHom, MulEquiv.refl_apply] using h

theorem block222_actor_swap [CharP F 2]
    (hδE : ∀ d (c : E) (x : X), δ d (c • x) = c • δ d x)
    (hcompat : ∀ d, ∃ A : GL (Fin (c + 4)) F, IsUpperGL A ∧
      ∃ (τ : F ≃+* F) (ε : ℕ),
        ∀ g x, δ d (σ g x) = σ (borelStd (c + 4) F A τ ε g) (δ d x))
    (hgraph : ∃ d, ∃ A : GL (Fin (c + 4)) F, IsUpperGL A ∧ ∃ τ : F ≃+* F,
      ∀ g x, δ d (σ g x) = σ (borelStd (c + 4) F A τ 1 g) (δ d x)) :
    ∃ d, ∃ (A₁ A₃ : GL (Fin 2) F) (τ : F ≃+* F)
      (β : SpecialLinearGroup (Fin c) F →* SpecialLinearGroup (Fin c) F),
      ∀ g₁ g₂ g₃ x,
        stageRestrict δ (blockFix222 c F σ) (blockFix222_actor_mem hδE hcompat) d
            (blockRestrict222 c F σ (g₁, g₂, g₃) x) =
          blockRestrict222 c F σ
            ((pairAut A₁ A₃ τ true (g₁, g₃)).1, β g₂, (pairAut A₁ A₃ τ true (g₁, g₃)).2)
            (stageRestrict δ (blockFix222 c F σ) (blockFix222_actor_mem hδE hcompat) d x) := by
  obtain ⟨d, A, hA, τ, hd⟩ := hgraph
  refine ⟨d, blockGL1 c F A hA, blockGL3 c F A hA, τ,
    (CFSG.QuasithinUnique.K1.stdAut (blockGL2 c F A hA) τ 0).toMonoidHom.comp
      (borelGraph c F).toMonoidHom, ?_⟩
  intro g₁ g₂ g₃ x
  apply Subtype.ext
  have h := (block222_intertwine_apply c F A τ 1 hA σ (actorLin δ hδE d) hd).2
    (g₁, g₂, g₃) x x.2
  rw [blockStd222_apply_odd c F A hA τ (by norm_num : (1 : ℕ) % 2 = 1), blockStd222Odd_apply]
    at h
  simp only [borelGraph_two_apply] at h
  simpa only [coe_stageRestrict_apply, blockRestrict222, restrictRep_apply,
    MonoidHom.comp_apply, actorLin_apply, pairAut_true_apply, Prod.fst, Prod.snd,
    MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] using h

end Block

end

end CFSG.LieType.SpecialLinear
