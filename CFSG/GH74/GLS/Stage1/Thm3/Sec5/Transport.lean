module

public import CFSG.GH74.GLS.Stage1.Thm2.Recip.Hat
public import CFSG.GH74.GLS.Stage1.Thm3.Sec4.Equiv

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec5

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm2.Recip

theorem mem_fixedSubgroup {Q : Type} [Group Q] (φ : MulAut Q) {x : Q} :
    x ∈ fixedSubgroup Q φ ↔ φ x = x := Iff.rfl

theorem fixedSubgroup_congr {Q Q' : Type} [Group Q] [Group Q'] (e : Q ≃* Q') (φ : MulAut Q) :
    fixedSubgroup Q' (MulAut.congr e φ) = (fixedSubgroup Q φ).map e.toMonoidHom := by
  ext x
  rw [Subgroup.mem_map_equiv, mem_fixedSubgroup, mem_fixedSubgroup]
  change e (φ (e.symm x)) = x ↔ φ (e.symm x) = e.symm x
  constructor
  · intro h
    have := congrArg e.symm h
    simpa using this
  · intro h
    rw [h]
    simp

theorem hasSolvableTwoComponentSL23_congr {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : HasSolvableTwoComponentSL23 X) : HasSolvableTwoComponentSL23 Y := by
  obtain ⟨W, hW, F, hF, hFin, hcard, ⟨iso⟩⟩ := h
  let q : X ⧸ pPrimeCore 2 X ≃* Y ⧸ pPrimeCore 2 Y :=
    QuotientGroup.congr _ _ e (pPrimeCore_map_iso 2 e)
  refine ⟨W.map q.toMonoidHom, hW.map (f := q.toMonoidHom) q.surjective, F, hF, hFin, hcard, ⟨?_⟩⟩
  exact (W.equivMapOfInjective q.toMonoidHom q.injective).symm.trans iso

theorem isFAutomorphism_congr {Q Q' : Type} [Group Q] [Group Q'] [Finite Q] [Finite Q']
    (e : Q ≃* Q') {φ : MulAut Q} (h : IsFAutomorphism Q φ) :
    IsFAutomorphism Q' (MulAut.congr e φ) := by
  obtain ⟨hq, hk, hr, ⟨k, hk2⟩, hfix⟩ := h
  refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e hq,
    CFSG.SectionRank.IsKGroupCat.of_mulEquiv hk e.symm,
    (pRank_eq_of_mulEquiv' e).symm.trans hr, ⟨k, ?_⟩, ?_⟩
  · rw [← hk2]
    exact orderOf_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective φ
  · have hF := fixedSubgroup_congr e φ
    let eF : ↥(fixedSubgroup Q φ) ≃* ↥(fixedSubgroup Q' (MulAut.congr e φ)) :=
      (MulEquiv.subgroupMap e _).trans (MulEquiv.subgroupCongr hF.symm)
    rcases hfix with ⟨L, hL⟩ | hS
    · exact Or.inl ⟨L.map eF.toMonoidHom,
        CFSG.LocalAnalysis.ComponentInitial.isPComponent_map_of_isPComponent 2 eF hL⟩
    · exact Or.inr (hasSolvableTwoComponentSL23_congr eF hS)

theorem inducesFAut_conj {G : Type} [Group G] [Finite G] {x : G} {K : Subgroup G} (g : G)
    (h : InducesFAut x K) :
    InducesFAut (g * x * g⁻¹) (K.map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨hx, hF⟩ := h
  have hx' : g * x * g⁻¹ ∈ normalizer ((K.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [Sec4.mem_cmap, Sec4.mem_cmap]
    have e : g⁻¹ * (g * x * g⁻¹ * y * (g * x * g⁻¹)⁻¹) * g = x * (g⁻¹ * y * g) * x⁻¹ := by group
    rw [e]
    exact Subgroup.mem_normalizer_iff.1 hx _
  refine ⟨hx', ?_⟩
  let e : ↥K ≃* ↥(K.map (MulAut.conj g).toMonoidHom) := MulEquiv.subgroupMap (MulAut.conj g) K
  let eH : Hat K ≃* Hat (K.map (MulAut.conj g).toMonoidHom) :=
    QuotientGroup.congr _ _ e (pPrimeCore_map_iso 2 e)
  have key : inducedQuotAut (K.map (MulAut.conj g).toMonoidHom)
        (pPrimeCore 2 ↥(K.map (MulAut.conj g).toMonoidHom)) ⟨g * x * g⁻¹, hx'⟩ =
      MulAut.congr eH (inducedQuotAut K (pPrimeCore 2 ↥K) ⟨x, hx⟩) := by
    ext y'
    obtain ⟨y, rfl⟩ := eH.surjective y'
    obtain ⟨k, rfl⟩ := hatMk_surjective K y
    have h1 : (MulAut.congr eH (inducedQuotAut K (pPrimeCore 2 ↥K) ⟨x, hx⟩)) (eH (hatMk K k)) =
        eH (phi K x hx (hatMk K k)) := by
      change eH (phi K x hx (eH.symm (eH (hatMk K k)))) = _
      rw [MulEquiv.symm_apply_apply]
    rw [h1]
    have he : ∀ k : ↥K, ((e k : ↥(K.map (MulAut.conj g).toMonoidHom)) : G) = g * (k : G) * g⁻¹ :=
      fun k => rfl
    have h2 : eH (hatMk K k) = hatMk _ (e k) := rfl
    change phi (K.map (MulAut.conj g).toMonoidHom) (g * x * g⁻¹) hx' (eH (hatMk K k)) =
      eH (phi K x hx (hatMk K k))
    rw [h2, phi_mk, phi_mk]
    change _ = hatMk _ (e ⟨x * (k : G) * x⁻¹, _⟩)
    congr 1
    apply Subtype.ext
    show g * x * g⁻¹ * ((e k : ↥(K.map (MulAut.conj g).toMonoidHom)) : G) * (g * x * g⁻¹)⁻¹ =
      ((e ⟨x * (k : G) * x⁻¹, _⟩ : ↥(K.map (MulAut.conj g).toMonoidHom)) : G)
    rw [he k, he ⟨x * (k : G) * x⁻¹, (Subgroup.mem_normalizer_iff.1 hx k).1 k.2⟩]
    group
  rw [key]
  exact isFAutomorphism_congr eH hF

end CFSG.GH74.GLS.Stage1.Thm3.Sec5
