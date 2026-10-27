module

public import CFSG.ClassicalGroups.Orthogonal.Eichler

public section

namespace CFSG.HardMathSupport.Timmesfeld.Proving

open CFSG.ClassicalGroups.Orthogonal QuadraticMap

variable {K V V' : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup V'] [Module K V']

@[expose] def isoConjHom (e : V ≃ₗ[K] V') : (V ≃ₗ[K] V) →* (V' ≃ₗ[K] V') where
  toFun g := (e.symm.trans g).trans e
  map_one' := LinearEquiv.ext fun x => by simp
  map_mul' g h := LinearEquiv.ext fun x => by simp [LinearEquiv.mul_apply]

theorem isoConjHom_apply (e : V ≃ₗ[K] V') (g : V ≃ₗ[K] V) (x : V') :
    isoConjHom e g x = e (g (e.symm x)) :=
  rfl

variable {Q : QuadraticForm K V} {Q' : QuadraticForm K V'}

theorem linearEquiv_one_apply' (x : V) : (1 : V ≃ₗ[K] V) x = x :=
  rfl

theorem isoConjHom_injective (e : V ≃ₗ[K] V') : Function.Injective (isoConjHom e) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  refine LinearEquiv.ext fun x => ?_
  have h := congrArg (fun f : V' ≃ₗ[K] V' => f (e x)) hg
  simp only [isoConjHom_apply, LinearEquiv.symm_apply_apply, linearEquiv_one_apply'] at h
  exact e.injective h

theorem polar_iso (e : V ≃ₗ[K] V') (he : ∀ x, Q' (e x) = Q x) (x y : V) :
    polar Q' (e x) (e y) = polar Q x y := by
  simp only [polar, ← map_add, he]

theorem isoConjHom_eichler (e : V ≃ₗ[K] V') (he : ∀ x, Q' (e x) = Q x) (u w : V) :
    isoConjHom e (eichler Q u w) = eichler Q' (e u) (e w) := by
  by_cases h : Q u = 0 ∧ polar Q u w = 0
  · have hu' : Q' (e u) = 0 := by rw [he]; exact h.1
    have hw' : polar Q' (e u) (e w) = 0 := by rw [polar_iso e he]; exact h.2
    refine LinearEquiv.ext fun x => ?_
    obtain ⟨y, rfl⟩ := e.surjective x
    rw [isoConjHom_apply, LinearEquiv.symm_apply_apply, eichler_apply h.1 h.2,
      eichler_apply hu' hw']
    simp [map_add, map_sub, map_smul, polar_iso e he, he]
  · have h' : ¬(Q' (e u) = 0 ∧ polar Q' (e u) (e w) = 0) := by
      rw [he, polar_iso e he]; exact h
    rw [eichler_of_not h, eichler_of_not h', map_one]

theorem isoConjHom_mem_elementaryGroup (e : V ≃ₗ[K] V') (he : ∀ x, Q' (e x) = Q x)
    {g : V ≃ₗ[K] V} (hg : g ∈ elementaryGroup Q) :
    isoConjHom e g ∈ elementaryGroup Q' := by
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨u, w, -, -, rfl⟩ := hg
    rw [isoConjHom_eichler e he]
    exact eichler_mem_elementaryGroup Q' _ _
  | one => exact (isoConjHom e).map_one ▸ one_mem _
  | mul a b _ _ ha hb => exact (isoConjHom e).map_mul a b ▸ mul_mem ha hb
  | inv a _ ha => exact (isoConjHom e).map_inv a ▸ inv_mem ha

end CFSG.HardMathSupport.Timmesfeld.Proving

end
