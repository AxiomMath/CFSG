module

public import CFSG.ClassicalInvolution.Q3.TA3SmallTransport

public section

namespace CFSG.ClassicalInvolution.Q3.TA3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77
open scoped commutatorElement

variable {Y Y' : Type} [Group Y] [Group Y'] [Finite Y] (e : Y ≃* Y')

omit [Finite Y] in
theorem mem_conjClass_map_equiv {K X : Subgroup Y} (h : X ∈ CoreAssembly.conjClass K) :
    X.map e.toMonoidHom ∈ CoreAssembly.conjClass (K.map e.toMonoidHom) := by
  obtain ⟨g, rfl⟩ := h
  exact ⟨e g, conjSub_map_equiv e g K⟩

theorem mem_RSet_map_equiv {Ω : Set (Subgroup Y)} {Ω' : Set (Subgroup Y')}
    (hΩ : ∀ X ∈ Ω, X.map e.toMonoidHom ∈ Ω') {P : Subgroup Y} (hP : P ∈ RSet Ω) :
    P.map e.toMonoidHom ∈ RSet Ω' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨J, hJ, Q, rfl⟩ := hP
  let eJ := J.equivMapOfInjective e.toMonoidHom e.injective
  have hsurj : Function.Surjective eJ.toMonoidHom := eJ.surjective
  refine ⟨J.map e.toMonoidHom, hΩ J hJ, Q.mapSurjective hsurj, ?_⟩
  show _ = ((Q : Subgroup J).map eJ.toMonoidHom).map (J.map e.toMonoidHom).subtype
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem mem_omegaNbr_map_equiv {Ω : Set (Subgroup Y)} {Ω' : Set (Subgroup Y')}
    (hΩ : ∀ X ∈ Ω, X.map e.toMonoidHom ∈ Ω') {K J : Subgroup Y} (h : J ∈ omegaNbr Ω K) :
    J.map e.toMonoidHom ∈ omegaNbr Ω' (K.map e.toMonoidHom) := by
  obtain ⟨hJ, hne, P, hP, hPJ, hPN⟩ := h
  refine ⟨hΩ J hJ, fun h => hne (Subgroup.map_injective (f := e.toMonoidHom) e.injective h),
    P.map e.toMonoidHom, mem_RSet_map_equiv e hΩ hP, Subgroup.map_mono hPJ, ?_⟩
  rw [← Subgroup.map_equiv_normalizer_eq K e]
  exact Subgroup.map_mono hPN

theorem dAdj_map_equiv {Ω : Set (Subgroup Y)} {Ω' : Set (Subgroup Y')}
    (hΩ : ∀ X ∈ Ω, X.map e.toMonoidHom ∈ Ω') {K J : Subgroup Y}
    (h : Disconnected.dAdj Ω K J) :
    Disconnected.dAdj Ω' (K.map e.toMonoidHom) (J.map e.toMonoidHom) := by
  rcases h with h | h
  · exact Or.inl (mem_omegaNbr_map_equiv e hΩ h)
  · exact Or.inr (mem_omegaNbr_map_equiv e hΩ h)

variable {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem TightEdgeless.of_map_equiv (h : TightEdgeless (R.map e.toMonoidHom)) :
    TightEdgeless R := by
  have hΩ : ∀ X ∈ CoreAssembly.conjClass (tightCore R),
      X.map e.toMonoidHom ∈ CoreAssembly.conjClass (tightCore (R.map e.toMonoidHom)) := by
    intro X hX
    rw [← tightCore_map_equiv e]
    exact mem_conjClass_map_equiv e hX
  unfold TightEdgeless Disconnected.DEdgeless at h ⊢
  intro K hK J hJ hadj
  exact h _ (hΩ K hK) _ (hΩ J hJ) (dAdj_map_equiv e hΩ hadj)

omit [Finite Y] in
theorem TightActs3.map_equiv (h : TightActs3 R t) : TightActs3 (R.map e.toMonoidHom) (e t) := by
  obtain ⟨x, k, hxC, hx3, r, hr, hxr⟩ := h
  refine ⟨e x, k, ?_, by rw [← map_pow, hx3, map_one], e r, Subgroup.mem_map_of_mem _ hr, ?_⟩
  · rw [← map_centralizer_singleton e t]
    exact Subgroup.mem_map_of_mem _ hxC
  · rw [oddCoreImg_map_equiv e, ← map_commutatorElement]
    exact fun hmem => hxr ((mem_map_equiv_iff e).mp hmem)

omit [Finite Y] in
theorem GoodThreeElement.of_map_equiv (h : GoodThreeElement (R.map e.toMonoidHom) (e t)) :
    GoodThreeElement R t := by
  obtain ⟨x', k, hxC, hx3, ⟨r', hr', hxr⟩, hD⟩ := h
  obtain ⟨x, rfl⟩ := e.surjective x'
  have hC := map_centralizer_singleton e t
  refine ⟨x, k, ?_, ?_, ?_, ?_⟩
  · rw [← hC] at hxC
    exact (mem_map_equiv_iff e).mp hxC
  · apply e.injective
    rw [map_pow, hx3, map_one]
  · obtain ⟨r, hr, rfl⟩ := hr'
    refine ⟨r, hr, fun hmem => hxr ?_⟩
    rw [oddCoreImg_map_equiv e]
    have := Subgroup.mem_map_of_mem e.toMonoidHom hmem
    rw [map_commutatorElement] at this
    exact this
  · intro y hyC hyR
    have h1 := hD (e y) (by rw [← hC]; exact Subgroup.mem_map_of_mem _ hyC) (by
      intro r' hr'
      obtain ⟨r, hr, rfl⟩ := hr'
      rw [oddCoreImg_map_equiv e]
      have := Subgroup.mem_map_of_mem e.toMonoidHom (hyR r hr)
      rw [map_commutatorElement] at this
      exact this)
    rw [← hC, oddCoreImg_map_equiv e, ← map_commutatorElement] at h1
    exact (mem_map_equiv_iff e).mp h1

theorem TightEx.of_map_equiv {S' : Sylow 2 ↥(R.map e.toMonoidHom)}
    (h : TightEx Y' (R.map e.toMonoidHom) S' (e t)) : TightEx Y R S t := by
  rcases h with h2 | ⟨hE, h3⟩ | ⟨hE, f, hfs, hfk⟩ | h4
  · exact Or.inl (TightInO2.of_map_equiv e h2)
  · exact Or.inr (Or.inl ⟨TightEdgeless.of_map_equiv e hE,
      fun h => h3 (TightActs3.map_equiv e h)⟩)
  · refine Or.inr (Or.inr (Or.inl ⟨TightEdgeless.of_map_equiv e hE, f.comp e.toMonoidHom,
      hfs.comp e.surjective, ?_⟩))
    rw [← MonoidHom.comap_ker]
    exact hfk.comap_of_injective _ e.injective
  · exact Or.inr (Or.inr (Or.inr (h4.of_surjective e.toMonoidHom e.surjective
      (IsPGroup.ker_isPGroup_of_injective e.injective))))

theorem tightExOrGood_of_map_equiv (hd : TightDatum R S t) (hc : TightCls Y R S t)
    (hE2 : ¬ TightInO2 t)
    (h : ∀ S' : Sylow 2 ↥(R.map e.toMonoidHom), TightDatum (R.map e.toMonoidHom) S' (e t) →
      TightCls Y' (R.map e.toMonoidHom) S' (e t) → ¬ TightInO2 (e t) →
        TightEx Y' (R.map e.toMonoidHom) S' (e t) ∨
          GoodThreeElement (R.map e.toMonoidHom) (e t)) :
    TightEx Y R S t ∨ GoodThreeElement R t := by
  obtain ⟨S', hSS, hS₀⟩ := exists_sylow_map_equiv e S
  rcases h S' (TightDatum.map_equiv e hd hSS hS₀) (TightCls.map_equiv e hc hSS)
      (fun h => hE2 (TightInO2.of_map_equiv e h)) with hex | hgood
  · exact Or.inl (TightEx.of_map_equiv e hex)
  · exact Or.inr (GoodThreeElement.of_map_equiv e hgood)

end CFSG.ClassicalInvolution.Q3.TA3
