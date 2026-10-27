module

public import CFSG.CGT.Foote82.T66.BranchASmallGL
public import CFSG.HardMathSupport.Cooperstein.StructureLie.TypeScriptLModels
public import CFSG.RankThree.PartTwo.Sec19.SimsItem316SmallModels

public section

namespace CFSG.CGT.Foote82.BAS

open CFSG.Open CFSG.Quasithin.G11 CFSG.RankThree.PartTwo
open CFSG.HardMathSupport.Cooperstein.StructureLie
open scoped Matrix

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

private theorem matrix_eq_of_mulVec {ι : Type} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι (ZMod 2)} (h : ∀ x, A *ᵥ x = B *ᵥ x) : A = B := by
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simpa [Matrix.mulVec_single] using this

theorem exists_mulEquiv_of_model {ι : Type} [Fintype ι] [DecidableEq ι]
    {X : Subgroup (GL ι (ZMod 2))} {E : Subgroup (GLV V)} (φ : V ≃ₗ[ZMod 2] (ι → ZMod 2))
    (h1 : ∀ g ∈ mapGL E, ∃ A ∈ X,
      ∀ w : V, (A : Matrix ι ι (ZMod 2)) *ᵥ φ w = φ ((g : V →ₗ[ZMod 2] V) w))
    (h2 : ∀ A ∈ X, ∃ g ∈ mapGL E,
      ∀ w : V, (A : Matrix ι ι (ZMod 2)) *ᵥ φ w = φ ((g : V →ₗ[ZMod 2] V) w)) :
    ∃ Ψ : ↥E ≃* ↥X, ∀ (e : ↥E) (v : V),
      φ ((e : GLV V) v) = ((Ψ e : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2)) *ᵥ φ v := by
  have huniq : ∀ (A B : GL ι (ZMod 2)),
      (∀ w : V, (A : Matrix ι ι (ZMod 2)) *ᵥ φ w = (B : Matrix ι ι (ZMod 2)) *ᵥ φ w) → A = B := by
    intro A B h
    apply Units.ext
    apply matrix_eq_of_mulVec
    intro x
    have := h (φ.symm x)
    rwa [LinearEquiv.apply_symm_apply] at this
  have hex : ∀ e : ↥E, ∃ A ∈ X, ∀ w : V,
      (A : Matrix ι ι (ZMod 2)) *ᵥ φ w = φ ((e : GLV V) w) := fun e =>
    h1 (toGL (e : GLV V)) (toGL_mem_mapGL e.2)
  choose A hAX hA using hex
  let f : ↥E →* ↥X :=
    { toFun := fun e => ⟨A e, hAX e⟩
      map_one' := by
        apply Subtype.ext
        apply huniq
        intro w
        rw [hA 1]
        simp
      map_mul' := by
        intro e₁ e₂
        apply Subtype.ext
        apply huniq
        intro w
        show (A (e₁ * e₂) : Matrix ι ι (ZMod 2)) *ᵥ φ w =
          ((A e₁ * A e₂ : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2)) *ᵥ φ w
        rw [hA (e₁ * e₂), Units.val_mul, ← Matrix.mulVec_mulVec, hA e₂, hA e₁]
        rfl }
  have hinj : Function.Injective f := by
    intro e₁ e₂ h
    have h' : A e₁ = A e₂ := congrArg Subtype.val h
    apply Subtype.ext
    apply LinearEquiv.ext
    intro w
    apply φ.injective
    rw [← hA e₁, ← hA e₂, h']
  have hsurj : Function.Surjective f := by
    rintro ⟨B, hB⟩
    obtain ⟨g, hg, hgB⟩ := h2 B hB
    refine ⟨⟨toGL.symm g, (mem_mapGL).1 hg⟩, Subtype.ext ?_⟩
    apply huniq
    intro w
    show (A ⟨toGL.symm g, _⟩ : Matrix ι ι (ZMod 2)) *ᵥ φ w = (B : Matrix ι ι (ZMod 2)) *ᵥ φ w
    rw [hA, hgB]
    rfl
  refine ⟨MulEquiv.ofBijective f ⟨hinj, hsurj⟩, fun e v => ?_⟩
  show φ ((e : GLV V) v) = (A e : Matrix ι ι (ZMod 2)) *ᵥ φ v
  rw [hA e]

theorem isOmegaMinusFor_of_model {E : Subgroup (GLV V)} {m : ℕ}
    (h : IsOmegaMinusModel (mapGL E) m) : IsOmegaMinusFor E m := by
  obtain ⟨φ, h1, h2⟩ := h
  obtain ⟨Ψ, hΨ⟩ := exists_mulEquiv_of_model φ h1 h2
  exact ⟨Ψ, φ, hΨ⟩

theorem isAltHeartFor_eight_of_plus {E : Subgroup (GLV V)}
    (h : IsOmegaPlusModel (mapGL E) 3) : IsAltHeartFor E 8 := by
  obtain ⟨φ, h1, h2⟩ := h
  obtain ⟨Ψ, hΨ⟩ := exists_mulEquiv_of_model φ h1 h2
  obtain ⟨φ₈, ψ₈, h₈⟩ := CFSG.RankThree.PartTwo.Sec19.SimsItem316Small.omegaPlusTwo_three_model
  refine ⟨Ψ.trans φ₈, φ.toAddEquiv.trans ψ₈, fun e v x hx => ?_⟩
  show ψ₈ (φ ((e : GLV V) v)) = _
  rw [hΨ e v]
  exact h₈ (Ψ e) (φ v) x hx

theorem isAltHeartFor_of_model {E : Subgroup (GLV V)} {m : ℕ}
    (h : IsAltModel (mapGL E) m) : IsAltHeartFor E m := by
  obtain ⟨φ, θ, hθ⟩ := h
  refine ⟨(E.equivMapOfInjective (toGL : GLV V ≃* _).toMonoidHom toGL.injective).trans θ, φ,
    fun e v x hx => ?_⟩
  exact hθ ((E.equivMapOfInjective (toGL : GLV V ≃* _).toMonoidHom toGL.injective) e) v x hx

end CFSG.CGT.Foote82.BAS
