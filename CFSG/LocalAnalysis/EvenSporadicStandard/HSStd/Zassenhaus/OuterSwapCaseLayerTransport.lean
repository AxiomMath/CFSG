module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterSwapCaseLayerSingle

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer

open Subgroup CFSG.EvenSporadicStandard.HSStd

@[expose] def quotCenterEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (A ⧸ center A) ≃* (B ⧸ center B) :=
  QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)

theorem quotCenterEquiv_mk {A B : Type*} [Group A] [Group B] (e : A ≃* B) (a : A) :
    quotCenterEquiv e (a : A ⧸ center A) = ((e a : B) : B ⧸ center B) := rfl

theorem tauQuot_map_compat {X Y : Type*} [Group X] [Group Y] (f : X →* Y)
    (hf : Function.Injective f) {τ : X} (K : Subgroup X) (ht2 : τ * τ = 1)
    (hK : ∀ x ∈ K, τ * x * τ⁻¹ ∈ K) (ht2' : f τ * f τ = 1)
    (hK' : ∀ x ∈ K.map f, f τ * x * (f τ)⁻¹ ∈ K.map f) (y : ↥K ⧸ center ↥K) :
    quotCenterEquiv (K.equivMapOfInjective f hf) (tauQuot K ht2 hK y) =
      tauQuot (K.map f) ht2' hK' (quotCenterEquiv (K.equivMapOfInjective f hf) y) := by
  induction y using QuotientGroup.induction_on with
  | H k =>
    rw [quotCenterEquiv_mk, tauQuot_mk, quotCenterEquiv_mk, tauQuot_mk]
    congr 1
    apply Subtype.ext
    simp

section Transport

variable {S S' : Type*} [Group S] [Group S'] (ε : S ≃* S') {τ : MulAut S} {τ' : MulAut S'}

theorem sq_transport (hc : ∀ y, ε (τ y) = τ' (ε y)) (h : τ * τ = 1) : τ' * τ' = 1 := by
  ext y'
  obtain ⟨y, rfl⟩ := ε.surjective y'
  have h1 : τ (τ y) = y := by
    have := congrArg (fun f : MulAut S => f y) h
    simpa using this
  show τ' (τ' (ε y)) = ε y
  rw [← hc, ← hc, h1]

theorem ne_transport (hc : ∀ y, ε (τ y) = τ' (ε y)) (h : τ ≠ 1) : τ' ≠ 1 := by
  intro h1
  apply h
  ext y
  apply ε.injective
  rw [hc, h1]
  rfl

theorem map_autCentralizer (hc : ∀ y, ε (τ y) = τ' (ε y)) :
    (autCentralizer τ).map ε.toMonoidHom = autCentralizer τ' := by
  ext y'
  obtain ⟨y, rfl⟩ := ε.surjective y'
  constructor
  · rintro ⟨x, hx, hxy⟩
    have hx' : τ x = x := hx
    have : x = y := ε.injective hxy
    subst this
    show τ' (ε x) = ε x
    rw [← hc, hx']
  · intro hy
    have hy' : τ' (ε y) = ε y := hy
    refine ⟨y, ?_, rfl⟩
    show τ y = y
    apply ε.injective
    rw [hc, hy']

noncomputable def autCentralizerEquivOf (hc : ∀ y, ε (τ y) = τ' (ε y)) :
    ↥(autCentralizer τ) ≃* ↥(autCentralizer τ') :=
  (Subgroup.equivMapOfInjective _ ε.toMonoidHom ε.injective).trans
    (MulEquiv.subgroupCongr (map_autCentralizer ε hc))

theorem card_autCentralizer_transport (hc : ∀ y, ε (τ y) = τ' (ε y)) :
    Nat.card (autCentralizer τ') = Nat.card (autCentralizer τ) :=
  (Nat.card_congr (autCentralizerEquivOf ε hc).toEquiv).symm

theorem D_transport (hc : ∀ y, ε (τ y) = τ' (ε y))
    (hD : ∃ D : Subgroup ↥(autCentralizer τ), D.Normal ∧
      Nonempty (↥D ≃* alternatingGroup (Fin 8)) ∧ ∀ x : ↥(autCentralizer τ), ∃ n : ℕ, x ^ (2 ^ n) ∈ D) :
    ∃ D : Subgroup ↥(autCentralizer τ'), D.Normal ∧
      Nonempty (↥D ≃* alternatingGroup (Fin 8)) ∧ ∀ x : ↥(autCentralizer τ'), ∃ n : ℕ, x ^ (2 ^ n) ∈ D := by
  obtain ⟨D, hDn, ⟨e⟩, hD2⟩ := hD
  set Φ := autCentralizerEquivOf ε hc with hΦ
  refine ⟨D.map Φ.toMonoidHom, hDn.map _ Φ.surjective, ⟨?_⟩, ?_⟩
  · exact ((D.equivMapOfInjective Φ.toMonoidHom Φ.injective).symm).trans e
  · intro x
    obtain ⟨x0, rfl⟩ := Φ.surjective x
    obtain ⟨n, hn⟩ := hD2 x0
    exact ⟨n, ⟨x0 ^ (2 ^ n), hn, by simp⟩⟩

end Transport

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer
