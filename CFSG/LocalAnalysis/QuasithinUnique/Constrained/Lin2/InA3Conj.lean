module

public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Basic245
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin

variable {G : Type*} [Group G]

section Blocks

theorem blockQ_map_equiv (f : G ≃* G) (L : Subgroup G) :
    blockQ (L.map f.toMonoidHom) = (blockQ L).map f.toMonoidHom :=
  pCoreOf_map_equiv 2 f L

theorem blockU_map_equiv (f : G ≃* G) (L : Subgroup G) :
    blockU (L.map f.toMonoidHom) = (blockU L).map f.toMonoidHom := by
  unfold blockU
  rw [blockQ_map_equiv, Subgroup.map_commutator]

theorem blockZ_map_equiv (f : G ≃* G) (L : Subgroup G) :
    blockZ (L.map f.toMonoidHom) = (blockZ L).map f.toMonoidHom := by
  unfold blockZ
  rw [blockU_map_equiv, centralizer_map_equiv, map_equiv_inf]

end Blocks

section Short

theorem IsShort2.map_equiv {L : Subgroup G} (hL : IsShort2 L) (f : G ≃* G) :
    IsShort2 (L.map f.toMonoidHom) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hL
  let φ : L ≃* (L.map f.toMonoidHom : Subgroup G) :=
    Subgroup.equivMapOfInjective L f.toMonoidHom f.injective
  refine ⟨?_, (charTwo_map_equiv_iff f L).2 h2, ?_, ?_, ?_⟩
  · intro N' _ hN'
    have hcomap : (N'.comap φ.toMonoidHom).map φ.toMonoidHom = N' :=
      Subgroup.map_comap_eq_self_of_surjective φ.surjective N'
    have e : (L ⧸ N'.comap φ.toMonoidHom) ≃* ((L.map f.toMonoidHom : Subgroup G) ⧸ N') :=
      QuotientGroup.congr _ _ φ hcomap
    have hN := h1 (N'.comap φ.toMonoidHom) (hN'.of_equiv e.symm)
    rw [← hcomap, hN, Subgroup.map_top, MonoidHom.range_eq_top_of_surjective _ φ.surjective]
  · rw [blockU_map_equiv, blockQ_map_equiv, centralizer_map_equiv, ← map_equiv_inf]
    refine ⟨Subgroup.map_mono h3.1, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    have := h3.2 y hy
    simpa using congrArg f this
  · let e : (L ⧸ CFSG.pCore 2 L) ≃* ((L.map f.toMonoidHom : Subgroup G) ⧸
        CFSG.pCore 2 (L.map f.toMonoidHom : Subgroup G)) :=
      QuotientGroup.congr _ _ φ (CFSG.pCore_map_iso 2 φ)
    rcases h4 with h | h
    · exact Or.inl ((CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr e).mp h)
    · exact Or.inr (by rw [← Nat.card_congr e.toEquiv]; exact h)
  · rw [blockZ_map_equiv, blockU_map_equiv]
    refine ⟨(Subgroup.map_lt_map_iff_of_injective f.injective).mpr h5.1, ?_⟩
    intro W' hW1 hW2 hW3
    have hW1' : blockZ L ≤ W'.map f.symm.toMonoidHom := by
      have := Subgroup.map_mono (f := f.symm.toMonoidHom) hW1
      rwa [map_equiv_symm_map_equiv] at this
    have hW2' : W'.map f.symm.toMonoidHom ≤ blockU L := by
      have := Subgroup.map_mono (f := f.symm.toMonoidHom) hW2
      rwa [map_equiv_symm_map_equiv] at this
    have hW3' : L ≤ Subgroup.normalizer ((W'.map f.symm.toMonoidHom : Subgroup G) : Set G) := by
      rw [normalizer_map_equiv]
      intro x hx
      exact ⟨f x, hW3 (Subgroup.mem_map_of_mem _ hx), by simp⟩
    rcases h5.2 _ hW1' hW2' hW3' with h | h
    · left
      have := congrArg (Subgroup.map f.toMonoidHom) h
      rwa [map_equiv_map_equiv_symm] at this
    · right
      have := congrArg (Subgroup.map f.toMonoidHom) h
      rwa [map_equiv_map_equiv_symm] at this

theorem isShort2_map_equiv_iff (f : G ≃* G) (L : Subgroup G) :
    IsShort2 (L.map f.toMonoidHom) ↔ IsShort2 L := by
  refine ⟨fun h => ?_, fun h => IsShort2.map_equiv h f⟩
  have := IsShort2.map_equiv h f.symm
  rwa [map_equiv_symm_map_equiv] at this

theorem isShort2_conjR_iff (L : Subgroup G) (g : G) : IsShort2 (conjR L g) ↔ IsShort2 L :=
  isShort2_map_equiv_iff (MulAut.conj g⁻¹) L

end Short

section Lin2Type

theorem IsLin2Type.map_equiv {L : Subgroup G} {n : ℕ} (hL : IsLin2Type L n) (f : G ≃* G) :
    IsLin2Type (L.map f.toMonoidHom) n := by
  obtain ⟨F, hF, hFin, hcard, α, hαs, hαker, β, hβs, hβker, hβeq⟩ := hL
  let φ : L ≃* (L.map f.toMonoidHom : Subgroup G) :=
    Subgroup.equivMapOfInjective L f.toMonoidHom f.injective
  have hφ : ∀ x : L, ((φ x : (L.map f.toMonoidHom : Subgroup G)) : G) = f x := fun x => rfl
  have hφsymm : ∀ y : (L.map f.toMonoidHom : Subgroup G), ((φ.symm y : L) : G) = f.symm y := by
    intro y
    apply f.injective
    rw [MulEquiv.apply_symm_apply, ← hφ, MulEquiv.apply_symm_apply]
  have hUmem : ∀ u : G, u ∈ blockU (L.map f.toMonoidHom) ↔ f.symm u ∈ blockU L := by
    intro u
    rw [blockU_map_equiv, Subgroup.mem_map_equiv]
  have hZmem : ∀ u : G, u ∈ blockZ (L.map f.toMonoidHom) ↔ f.symm u ∈ blockZ L := by
    intro u
    rw [blockZ_map_equiv, Subgroup.mem_map_equiv]
  let ψ : blockU (L.map f.toMonoidHom) →* blockU L :=
    MonoidHom.codRestrict (f.symm.toMonoidHom.comp (blockU (L.map f.toMonoidHom)).subtype)
      (blockU L) fun u => (hUmem u).1 u.2
  have hψ : ∀ u, ((ψ u : blockU L) : G) = f.symm (u : G) := fun u => rfl
  refine ⟨F, hF, hFin, hcard, α.comp φ.symm.toMonoidHom, hαs.comp φ.symm.surjective, ?_,
    β.comp ψ, ?_, ?_, ?_⟩
  · ext ℓ'
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hαker,
      ← CFSG.pCore_map_iso 2 φ, Subgroup.mem_map_equiv]
    rfl
  · intro y
    obtain ⟨u, hu⟩ := hβs y
    have hfu : f (u : G) ∈ blockU (L.map f.toMonoidHom) :=
      (hUmem _).2 (by rw [MulEquiv.symm_apply_apply]; exact u.2)
    refine ⟨⟨f u, hfu⟩, ?_⟩
    have h1 : ψ ⟨f u, hfu⟩ = u := Subtype.ext (by rw [hψ]; exact MulEquiv.symm_apply_apply f _)
    rw [MonoidHom.comp_apply, h1, hu]
  · ext u'
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hβker]
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, hψ]
    exact (hZmem _).symm
  · intro ℓ' u' v' h
    have h' : ((ψ v' : blockU L) : G) = ((φ.symm ℓ' : L) : G) * ((ψ u' : blockU L) : G) *
        ((φ.symm ℓ' : L) : G)⁻¹ := by
      rw [hψ, hψ, hφsymm, h, map_mul, map_mul, InvMemClass.coe_inv, map_inv]
    exact hβeq (φ.symm ℓ') (ψ u') (ψ v') h'

theorem isLin2Type_map_equiv_iff (f : G ≃* G) (L : Subgroup G) (n : ℕ) :
    IsLin2Type (L.map f.toMonoidHom) n ↔ IsLin2Type L n := by
  refine ⟨fun h => ?_, fun h => IsLin2Type.map_equiv h f⟩
  have := IsLin2Type.map_equiv h f.symm
  rwa [map_equiv_symm_map_equiv] at this

theorem isLin2Type_conjR_iff (L : Subgroup G) (g : G) (n : ℕ) :
    IsLin2Type (conjR L g) n ↔ IsLin2Type L n :=
  isLin2Type_map_equiv_iff (MulAut.conj g⁻¹) L n

end Lin2Type

end CFSG.QuasithinUnique.Lin2
