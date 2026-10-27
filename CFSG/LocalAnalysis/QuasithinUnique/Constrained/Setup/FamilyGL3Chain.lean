module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyGL3Tools
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.QuasithinUnique.Setup.Family

@[expose] def prodAct {G A B : Type*} (actA : G → A → A) (actB : G → B → B) :
    G → A × B → A × B :=
  fun g p => (actA g p.1, actB g p.2)

section Skeleton

variable {G : Type*}

theorem IsIrrAct.actIso_of_ne_zero {E E' : Type*} [AddCommMonoid E] [Module (ZMod 2) E]
    [AddCommMonoid E'] [Module (ZMod 2) E'] {act : G → E → E} {act' : G → E' → E'}
    (hX : IsIrrAct act) (hY : IsIrrAct act') {f : E →ₗ[ZMod 2] E'}
    (hf : IsEquivAct act act' f) (hf0 : f ≠ 0) : ActIso act act' :=
  ⟨LinearEquiv.ofBijective f (hX.bijective_of_ne_zero hY hf hf0), fun g x => hf g x⟩

theorem IsEquivAct.comp {E E' E'' : Type*} [AddCommMonoid E] [Module (ZMod 2) E]
    [AddCommMonoid E'] [Module (ZMod 2) E'] [AddCommMonoid E''] [Module (ZMod 2) E'']
    {act : G → E → E} {act' : G → E' → E'} {act'' : G → E'' → E''} {f : E →ₗ[ZMod 2] E'}
    {f' : E' →ₗ[ZMod 2] E''} (hf : IsEquivAct act act' f) (hf' : IsEquivAct act' act'' f') :
    IsEquivAct act act'' (f'.comp f) := fun g x => by
  simp only [LinearMap.comp_apply]
  rw [hf g x, hf' g (f x)]

theorem actIso_of_sub_quot {E U Y X : Type*} [AddCommMonoid E] [Module (ZMod 2) E]
    [AddCommMonoid U] [Module (ZMod 2) U] [AddCommMonoid Y] [Module (ZMod 2) Y]
    [AddCommMonoid X] [Module (ZMod 2) X] {actE : G → E → E} {actU : G → U → U}
    {actY : G → Y → Y} {actX : G → X → X} (hE : IsIrrAct actE) (hY : IsIrrAct actY)
    (hX : IsIrrAct actX) (κ : Y →ₗ[ZMod 2] U) (hκ : IsEquivAct actY actU κ) (θ : U →ₗ[ZMod 2] X)
    (hθ : Function.Surjective θ) (hθe : IsEquivAct actU actX θ)
    (hker : LinearMap.ker θ ≤ LinearMap.range κ) (φ : U →ₗ[ZMod 2] E)
    (hφ : IsEquivAct actU actE φ) (hφ0 : φ ≠ 0) : ActIso actY actE ∨ ActIso actX actE := by
  by_cases h : φ.comp κ = 0
  · right
    refine actIso_of_ker_le hX hE θ hθ hθe φ hφ hφ0 fun u hu => ?_
    obtain ⟨y, rfl⟩ := hker hu
    rw [LinearMap.mem_ker]
    exact LinearMap.congr_fun h y
  · left
    exact hY.actIso_of_ne_zero hE (hκ.comp hφ) h

theorem exists_ne_zero_summand {K U W E : Type*} [AddCommMonoid K] [Module (ZMod 2) K]
    [AddCommMonoid U] [Module (ZMod 2) U] [AddCommMonoid W] [Module (ZMod 2) W]
    [AddCommMonoid E] [Module (ZMod 2) E] (f : (K × (U × W)) →ₗ[ZMod 2] E) (hf : f ≠ 0) :
    f.comp (LinearMap.inl (ZMod 2) K (U × W)) ≠ 0 ∨
      (f.comp (LinearMap.inr (ZMod 2) K (U × W))).comp (LinearMap.inl (ZMod 2) U W) ≠ 0 ∨
      (f.comp (LinearMap.inr (ZMod 2) K (U × W))).comp (LinearMap.inr (ZMod 2) U W) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2, h3⟩ := hcon
  apply hf
  refine LinearMap.ext fun ⟨a, b, c⟩ => ?_
  have e1 := LinearMap.congr_fun h1 a
  have e2 := LinearMap.congr_fun h2 b
  have e3 := LinearMap.congr_fun h3 c
  simp only [LinearMap.comp_apply, LinearMap.inl_apply, LinearMap.inr_apply,
    LinearMap.zero_apply] at e1 e2 e3
  have : ((a, b, c) : K × (U × W)) = (a, 0) + ((0, b, 0) + (0, 0, c)) := by
    ext <;> simp
  rw [this, map_add, map_add, e1, e2, e3]
  simp

theorem classify_skeleton {E F K U W A Y X Y' X' : Type*}
    [AddCommMonoid E] [Module (ZMod 2) E] [AddCommMonoid F] [Module (ZMod 2) F]
    [AddCommMonoid K] [Module (ZMod 2) K] [AddCommMonoid U] [Module (ZMod 2) U]
    [AddCommMonoid W] [Module (ZMod 2) W] [AddCommMonoid A] [Module (ZMod 2) A]
    [AddCommMonoid Y] [Module (ZMod 2) Y] [AddCommMonoid X] [Module (ZMod 2) X]
    [AddCommMonoid Y'] [Module (ZMod 2) Y'] [AddCommMonoid X'] [Module (ZMod 2) X']
    {actE : G → E → E} {actF : G → F → F} {actK : G → K → K} {actU : G → U → U}
    {actW : G → W → W} {actA : G → A → A} {actY : G → Y → Y} {actX : G → X → X}
    {actY' : G → Y' → Y'} {actX' : G → X' → X'}
    (hU0 : ∀ g, actU g 0 = 0) (hW0 : ∀ g, actW g 0 = 0)
    (hE : IsIrrAct actE) (hA : IsIrrAct actA) (hK : IsIrrAct actK) (hY : IsIrrAct actY)
    (hX : IsIrrAct actX) (hY' : IsIrrAct actY') (hX' : IsIrrAct actX')
    (π : F →ₗ[ZMod 2] E) (hπ : IsEquivAct actF actE π) (hπ0 : π ≠ 0)
    (ι : (K × (U × W)) →ₗ[ZMod 2] F)
    (hι : IsEquivAct (prodAct actK (prodAct actU actW)) actF ι)
    (Ψ : F →ₗ[ZMod 2] A) (hΨ : Function.Surjective Ψ) (hΨe : IsEquivAct actF actA Ψ)
    (hΨker : LinearMap.ker Ψ ≤ LinearMap.range ι)
    (κ : Y →ₗ[ZMod 2] U) (hκ : IsEquivAct actY actU κ) (θ : U →ₗ[ZMod 2] X)
    (hθ : Function.Surjective θ) (hθe : IsEquivAct actU actX θ)
    (hθker : LinearMap.ker θ ≤ LinearMap.range κ)
    (κ' : Y' →ₗ[ZMod 2] W) (hκ' : IsEquivAct actY' actW κ') (θ' : W →ₗ[ZMod 2] X')
    (hθ' : Function.Surjective θ') (hθe' : IsEquivAct actW actX' θ')
    (hθker' : LinearMap.ker θ' ≤ LinearMap.range κ') :
    ActIso actA actE ∨ ActIso actK actE ∨ ActIso actY actE ∨ ActIso actX actE ∨
      ActIso actY' actE ∨ ActIso actX' actE := by
  by_cases h : π.comp ι = 0
  · left
    refine actIso_of_ker_le hA hE Ψ hΨ hΨe π hπ hπ0 fun x hx => ?_
    obtain ⟨d, rfl⟩ := hΨker hx
    rw [LinearMap.mem_ker]
    exact LinearMap.congr_fun h d
  · right
    have hπι : IsEquivAct (prodAct actK (prodAct actU actW)) actE (π.comp ι) := hι.comp hπ
    rcases exists_ne_zero_summand (π.comp ι) h with h1 | h2 | h3
    · left
      refine hK.actIso_of_ne_zero hE (f := (π.comp ι).comp (LinearMap.inl (ZMod 2) K (U × W)))
        (fun g x => ?_) h1
      simp only [LinearMap.comp_apply, LinearMap.inl_apply]
      have := hπι g (x, 0)
      simp only [LinearMap.comp_apply, prodAct, Prod.fst_zero, Prod.snd_zero, hU0 g, hW0 g] at this
      exact this
    · right
      have hφ : IsEquivAct actU actE
          (((π.comp ι).comp (LinearMap.inr (ZMod 2) K (U × W))).comp
            (LinearMap.inl (ZMod 2) U W)) := fun g u => by
        simp only [LinearMap.comp_apply, LinearMap.inl_apply, LinearMap.inr_apply]
        have := hπι g (0, (u, 0))
        simpa [prodAct, hK.2.1 g, hW0 g] using this
      rcases actIso_of_sub_quot hE hY hX κ hκ θ hθ hθe hθker _ hφ h2 with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · right
      right
      right
      have hφ : IsEquivAct actW actE
          (((π.comp ι).comp (LinearMap.inr (ZMod 2) K (U × W))).comp
            (LinearMap.inr (ZMod 2) U W)) := fun g w => by
        simp only [LinearMap.comp_apply, LinearMap.inr_apply]
        have := hπι g (0, (0, w))
        simpa [prodAct, hK.2.1 g, hU0 g] using this
      rcases actIso_of_sub_quot hE hY' hX' κ' hκ' θ' hθ' hθe' hθker' _ hφ h3 with h | h
      · exact Or.inl h
      · exact Or.inr h

end Skeleton

end CFSG.QuasithinUnique.Setup.Family
