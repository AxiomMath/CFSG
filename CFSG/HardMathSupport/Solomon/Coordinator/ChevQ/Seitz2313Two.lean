module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Seitz2313Cover
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzBridge
import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalExcTwTag

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

open CFSG.Open

@[expose] def Seitz2313TwoEven : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (S : Type) [Group S] [Finite S] (d : TauCeti.ValidLieTypeIndex),
    Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group) → Seitz2313Cover.EvenScope d.1 →
    ∀ E : Subgroup (MulAut S), IsElemAbelian p E →
      (∃ U : Subgroup S, U ≠ ⊥ ∧ IsPGroup 2 ↥U ∧ ∀ φ ∈ E, ∀ u ∈ U, φ u ∈ U) →
        ∃ Q₁ Q₂ : Subgroup S, IsPGroup 2 ↥Q₁ ∧ IsPGroup 2 ↥Q₂ ∧
          (∀ φ ∈ E, ∀ u ∈ Q₁, φ u ∈ Q₁) ∧ (∀ φ ∈ E, ∀ u ∈ Q₂, φ u ∈ Q₂) ∧ Q₁ ⊔ Q₂ = ⊤

namespace Seitz2313TwoAux

open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzBridgeAux

theorem le_normalizer_of_conj {G : Type*} [Group G] {H T : Subgroup G}
    (h : ∀ g ∈ H, ∀ y ∈ T, g * y * g⁻¹ ∈ T) : H ≤ Subgroup.normalizer (T : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => h g hg y hy, fun hy => ?_⟩
  have := h g⁻¹ (H.inv_mem hg) _ hy
  simpa [mul_assoc] using this

variable {S : Type} [Group S] {E : Subgroup (MulAut S)}

theorem holE_le_normalizer_map {U : Subgroup S} (hU : ∀ φ ∈ E, ∀ u ∈ U, φ u ∈ U) :
    holE S E ≤ Subgroup.normalizer
      ((U.map (SemidirectProduct.inl : S →* Hol S E) : Subgroup (Hol S E)) : Set (Hol S E)) := by
  refine le_normalizer_of_conj fun g hg y hy => ?_
  obtain ⟨f, rfl⟩ := mem_holE.1 hg
  obtain ⟨u, hu, rfl⟩ := hy
  rw [inr_mul_inl_mul_inr_inv]
  exact ⟨(f : MulAut S) u, hU f f.2 u hu, rfl⟩

theorem range_inl_eq_holK : (SemidirectProduct.inl : S →* Hol S E).range = holK S E := by
  ext x
  rw [mem_holK]
  exact MonoidHom.mem_range

theorem invariant_comap_inl {Q : Subgroup (Hol S E)}
    (hQ : holE S E ≤ Subgroup.normalizer (Q : Set (Hol S E))) :
    ∀ φ ∈ E, ∀ u ∈ Q.comap (SemidirectProduct.inl : S →* Hol S E), φ u ∈ Q.comap
      (SemidirectProduct.inl : S →* Hol S E) := by
  intro φ hφ u hu
  have h1 : (SemidirectProduct.inr (⟨φ, hφ⟩ : E) : Hol S E) ∈ holE S E := mem_holE.2 ⟨⟨φ, hφ⟩, rfl⟩
  have h2 := (Subgroup.mem_normalizer_iff.1 (hQ h1) (SemidirectProduct.inl u)).1 hu
  rw [inr_mul_inl_mul_inr_inv] at h2
  exact h2

theorem isPGroup_comap_inl {p : ℕ} {Q : Subgroup (Hol S E)} (hQ : IsPGroup p ↥Q) :
    IsPGroup p ↥(Q.comap (SemidirectProduct.inl : S →* Hol S E)) := by
  intro x
  obtain ⟨k, hk⟩ := hQ ⟨SemidirectProduct.inl (x : S), x.2⟩
  refine ⟨k, Subtype.ext ?_⟩
  have h1 : SemidirectProduct.inl ((x : S) ^ (p ^ k)) = (1 : Hol S E) := by
    rw [map_pow]
    exact congrArg Subtype.val hk
  have h2 : (x : S) ^ (p ^ k) = 1 := SemidirectProduct.inl_injective (h1.trans (map_one _).symm)
  simpa using h2

end Seitz2313TwoAux

open Seitz2313TwoAux CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzBridgeAux in
theorem seitz2313TwoEven_holds : Seitz2313TwoEven := by
  intro p hp hp2 S _ _ d ⟨e⟩ hs E hE ⟨U, hU0, hU2, hUinv⟩
  obtain ⟨t, n, f, ht, hadm, h1, h2, hLM⟩ :=
    Seitz2313Cover.exists_blueprintLieModel_of_scope d hs
  obtain ⟨ψ₀, hsurj, hker, hsimpleC, hnabC⟩ := Seitz2313Cover.exists_cover_even ht hadm hLM
  haveI := hsimpleC
  have hsimple : IsSimpleGroup S := MulEquiv.isSimpleGroup e
  have hnab : ∃ a b : S, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnabC
    exact ⟨e.symm a, e.symm b, fun h => hab (e.symm.injective (by simpa using h))⟩
  have hrank : 2 ≤ (CFSG.StandardType.ggU t n f).D.rank := by
    have := CFSG.ClassicalInvolution.ModelFacts.two_le_rank t n 2 f Nat.prime_two ht.isFundTag'
      hadm h1 h2
    rwa [Seitz2313Cover.modelUniv_eq' ht] at this
  let ψ : (CFSG.StandardType.ggU t n f).K →* Hol S E :=
    (SemidirectProduct.inl : S →* Hol S E).comp (e.symm.toMonoidHom.comp ψ₀)
  have hrange : ψ.range = holK S E := by
    have : (e.symm.toMonoidHom.comp ψ₀).range = ⊤ :=
      MonoidHom.range_eq_top.2 (e.symm.surjective.comp hsurj)
    rw [show ψ = (SemidirectProduct.inl : S →* Hol S E).comp (e.symm.toMonoidHom.comp ψ₀) from rfl,
      MonoidHom.range_comp, this, ← MonoidHom.range_eq_map]
    exact range_inl_eq_holK
  have hψker : ψ.ker ≤ Subgroup.center (CFSG.StandardType.ggU t n f).K := by
    intro k hk
    apply hker
    have h1 : SemidirectProduct.inl (e.symm (ψ₀ k)) = (1 : Hol S E) := hk
    have h2 := SemidirectProduct.inl_injective (h1.trans (map_one SemidirectProduct.inl).symm)
    exact (map_eq_one_iff _ e.symm.injective).1 h2
  have hq := holK_isQuasisimple (E := E) hsimple hnab
  obtain ⟨eq⟩ := holK_quot_equiv (E := E) hsimple hnab e
  have hpres : CFSG.StandardType.GGPresentsG0 (holK S E) (CFSG.StandardType.ggU t n f).D t n f ψ :=
    ⟨⟨hadm, hrank⟩, ⟨hrange, hψker⟩, hq.1, hLM.of_mulEquiv eq.symm⟩
  have hEp : IsPGroup p ↥(holE S E) := by
    have hel := isElemAbelian_holE (E := E) hE
    intro x
    exact ⟨1, Subtype.ext (by simpa using hel.2 x x.2)⟩
  have hEN : holE S E ≤ Subgroup.normalizer ((holK S E : Subgroup (Hol S E)) : Set (Hol S E)) := by
    rw [Subgroup.normalizer_eq_top_iff.2 (holK_normal S E)]
    exact le_top
  set T : Subgroup (Hol S E) := U.map (SemidirectProduct.inl : S →* Hol S E) with hT
  have hTK : T ≤ holK S E := fun x hx => by
    obtain ⟨u, -, rfl⟩ := hx
    exact mem_holK.2 ⟨u, rfl⟩
  have hT0 : T ≠ ⊥ := fun h =>
    hU0 ((Subgroup.map_eq_bot_iff_of_injective U SemidirectProduct.inl_injective).1 h)
  have hT2 : IsPGroup 2 ↥T :=
    hU2.of_equiv (Subgroup.equivMapOfInjective U (SemidirectProduct.inl : S →* Hol S E)
      SemidirectProduct.inl_injective)
  have hET : holE S E ≤ Subgroup.normalizer (T : Set (Hol S E)) := holE_le_normalizer_map hUinv
  obtain ⟨Q₁, Q₂, hQ₁, hQ₂, h2₁, h2₂, hn₁, hn₂, hgen⟩ :=
    CFSG.StandardType.ggTwoSignalizerGenInput_holds (Hol S E) t n f ψ (holK S E) hpres p hp hp2
      (holE S E) hEp hEN T hTK hT0 hT2 hET
  refine ⟨Q₁.comap (SemidirectProduct.inl : S →* Hol S E),
    Q₂.comap (SemidirectProduct.inl : S →* Hol S E), isPGroup_comap_inl h2₁, isPGroup_comap_inl h2₂,
    invariant_comap_inl hn₁, invariant_comap_inl hn₂, ?_⟩
  apply Subgroup.map_injective (SemidirectProduct.inl_injective (N := S) (G := ↥E))
  rw [Subgroup.map_sup, Subgroup.map_comap_eq, Subgroup.map_comap_eq, range_inl_eq_holK,
    inf_of_le_right hQ₁, inf_of_le_right hQ₂, hgen, Subgroup.map_top, range_inl_eq_holK]

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
