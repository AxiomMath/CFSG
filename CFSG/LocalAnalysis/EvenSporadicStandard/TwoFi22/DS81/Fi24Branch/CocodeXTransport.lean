module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CocodeHomVanish
public import CFSG.Quasithin.Background.HZ82Base

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch

open Subgroup MulAction CFSG.Quasithin
open CFSG.Quasithin.H (congrHom congrHom_injective)

section Equiv

variable {V W : Type} [CommGroup V] [CommGroup W] (e : V ≃* W)

theorem congrHom_apply_equiv (g : MulAut V) (v : V) : congrHom e g (e v) = e (g v) := by
  rw [Quasithin.H.congrHom_apply, MulEquiv.symm_apply_apply]

theorem invariant_map {T : Subgroup (MulAut V)} {U : Subgroup V}
    (h : ∀ g ∈ T, ∀ u ∈ U, g u ∈ U) :
    ∀ g ∈ T.map (congrHom e), ∀ w ∈ U.map e.toMonoidHom, g w ∈ U.map e.toMonoidHom := by
  rintro _ ⟨g, hg, rfl⟩ _ ⟨u, hu, rfl⟩
  refine ⟨g u, h g hg u hu, ?_⟩
  exact (congrHom_apply_equiv e g u).symm

theorem conj_invariant_map {T S : Subgroup (MulAut V)}
    (h : ∀ g ∈ T, ∀ s ∈ S, g * s * g⁻¹ ∈ S) :
    ∀ g ∈ T.map (congrHom e), ∀ s ∈ S.map (congrHom e), g * s * g⁻¹ ∈ S.map (congrHom e) := by
  rintro _ ⟨g, hg, rfl⟩ _ ⟨s, hs, rfl⟩
  exact ⟨g * s * g⁻¹, h g hg s hs, by rw [map_mul, map_mul, map_inv]⟩

theorem centSub_zpowers_map (z : V) :
    centSub (zpowers (e z)) = (centSub (zpowers z)).map (congrHom e) := by
  rw [Quasithin.H.centSub_map_congrHom, MonoidHom.map_zpowers]
  rfl

theorem stabSub_closure_pair_map (t z : V) :
    stabSub (closure {e t, e z}) = (stabSub (closure {t, z})).map (congrHom e) := by
  rw [← Quasithin.H.ZTrans.stabSub_map_congrHom, MonoidHom.map_closure, Set.image_pair]
  rfl

theorem HomVanishX.of_map {T P : Subgroup (MulAut V)} {U : Subgroup V}
    (h : HomVanishX (T.map (congrHom e)) (P.map (congrHom e)) (U.map e.toMonoidHom)) :
    HomVanishX T P U := by
  intro ψ h1 h2 k hk
  let ψ' : MulAut W → W := fun m => e (ψ ((MulAut.congr e).symm m))
  have hψ' : ∀ m : MulAut V, ψ' (congrHom e m) = e (ψ m) := fun m => by
    simp only [ψ']
    rw [show congrHom e m = MulAut.congr e m from rfl, MulEquiv.symm_apply_apply]
  have key := h ψ' ?_ ?_ (congrHom e k) (Subgroup.mem_map_of_mem _ hk)
  · rw [hψ'] at key
    exact (Subgroup.mem_map_iff_mem e.injective).1 key
  · rintro _ ⟨k₁, hk₁, rfl⟩ _ ⟨k₂, hk₂, rfl⟩
    have e1 : congrHom e k₁ * congrHom e k₂ = congrHom e (k₁ * k₂) := (map_mul _ _ _).symm
    rw [e1, hψ', hψ', hψ']
    exact ⟨(ψ (k₁ * k₂))⁻¹ * (ψ k₁ * ψ k₂), h1 k₁ hk₁ k₂ hk₂, by simp⟩
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨k, hk', rfl⟩
    have e2 : congrHom e a * congrHom e k * (congrHom e a)⁻¹ = congrHom e (a * k * a⁻¹) := by
      rw [map_mul, map_mul, map_inv]
    rw [e2, hψ', hψ', congrHom_apply_equiv]
    exact ⟨(ψ (a * k * a⁻¹))⁻¹ * a (ψ k), h2 a ha k hk', by simp⟩

end Equiv

section Injective

theorem O23In_map_of_injective {A B : Type} [Group A] [Group B] (f : A →* B)
    (hf : Function.Injective f) (X : Subgroup A) :
    TwoFi22.O23In (X.map f) = (TwoFi22.O23In X).map f := by
  let φ : ↥X ≃* ↥(X.map f) := X.equivMapOfInjective f hf
  have h1 := DS81.Reifart.map_O23Abs φ
  show (DS81.Reifart.O23Abs ↥(X.map f)).map (X.map f).subtype =
    ((DS81.Reifart.O23Abs ↥X).map X.subtype).map f
  rw [← h1, Subgroup.map_map, Subgroup.map_map]
  rfl

end Injective

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch
