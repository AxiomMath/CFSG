module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingPrime

public section

namespace CFSG.ComponentClassification.CatalogueBAlternating

@[expose] noncomputable def primeCoreQuotientEquiv {G H : Type*} [Group G] [Group H]
    (p : ℕ) (e : G ≃* H) : (G ⧸ pPrimeCore p G) ≃* (H ⧸ pPrimeCore p H) :=
  QuotientGroup.congr _ _ e (pPrimeCore_map_iso p e)

theorem primeCoreQuotientEquiv_mk {G H : Type*} [Group G] [Group H]
    (p : ℕ) (e : G ≃* H) (g : G) :
    primeCoreQuotientEquiv p e ((QuotientGroup.mk' (pPrimeCore p G)) g) =
      (QuotientGroup.mk' (pPrimeCore p H)) (e g) :=
  QuotientGroup.congr_mk' _ _ _ _ g

theorem primeCoreQuotient_map {G H : Type*} [Group G] [Group H]
    (p : ℕ) (e : G ≃* H) (J : Subgroup G) :
    (J.map (QuotientGroup.mk' (pPrimeCore p G))).map
        (primeCoreQuotientEquiv p e).toMonoidHom =
      (J.map e.toMonoidHom).map (QuotientGroup.mk' (pPrimeCore p H)) := by
  rw [Subgroup.map_map, Subgroup.map_map]
  apply congrArg (Subgroup.map · J)
  apply MonoidHom.ext
  exact primeCoreQuotientEquiv_mk p e

theorem pComponent_map_equiv {G H : Type*} [Group G] [Group H]
    (p : ℕ) (e : G ≃* H) (L : Subgroup G) (hL : CFSG.IsPComponent p L) :
    CFSG.IsPComponent p (L.map e.toMonoidHom) := by
  obtain ⟨hchain, hcomponent, hminimal⟩ := (pComponent_iff_minimal_image p L).mp hL
  apply (pComponent_iff_minimal_image p _).mpr
  refine ⟨?_, ?_, ?_⟩
  · have h := Components.chain_map e.toMonoidHom hchain
    rwa [Subgroup.map_top_of_surjective e.toMonoidHom e.surjective] at h
  · have h := (LocalComponents.equiv_iff (primeCoreQuotientEquiv p e)
      (L.map (QuotientGroup.mk' (pPrimeCore p G)))).mpr hcomponent
    rwa [primeCoreQuotient_map] at h
  · intro J hJL hJ himage
    let J' := J.map e.symm.toMonoidHom
    have hback : J'.map e.toMonoidHom = J :=
      (Subgroup.map_symm_eq_iff_map_eq J (e := e.symm)).mpr rfl
    have hJ'L : J' ≤ L := by
      apply (Subgroup.map_le_map_iff_of_injective (f := e.toMonoidHom) e.injective).mp
      rwa [hback]
    have hchain' : Open.IsSubnormal J' ⊤ := by
      have h := Components.chain_map e.symm.toMonoidHom hJ
      rwa [Subgroup.map_top_of_surjective e.symm.toMonoidHom e.symm.surjective] at h
    have himage' : J'.map (QuotientGroup.mk' (pPrimeCore p G)) =
        L.map (QuotientGroup.mk' (pPrimeCore p G)) := by
      apply Subgroup.map_injective (f := (primeCoreQuotientEquiv p e).toMonoidHom)
        (primeCoreQuotientEquiv p e).injective
      rw [primeCoreQuotient_map, primeCoreQuotient_map, hback]
      exact himage
    have heq := hminimal J' hJ'L hchain' himage'
    exact hback.symm.trans (congrArg (Subgroup.map e.toMonoidHom) heq)

theorem pComponent_equiv_iff {G H : Type*} [Group G] [Group H]
    (p : ℕ) (e : G ≃* H) (L : Subgroup G) :
    CFSG.IsPComponent p (L.map e.toMonoidHom) ↔ CFSG.IsPComponent p L := by
  constructor
  · intro hL
    have h := pComponent_map_equiv p e.symm (L.map e.toMonoidHom) hL
    have hback : (L.map e.toMonoidHom).map e.symm.toMonoidHom = L :=
      (Subgroup.map_symm_eq_iff_map_eq L (e := e)).mpr rfl
    rwa [hback] at h
  · exact pComponent_map_equiv p e L

@[expose] noncomputable def normalizerEquiv {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (S : Subgroup G) :
    Subgroup.normalizer (S : Set G) ≃*
      Subgroup.normalizer (S.map e.toMonoidHom : Set H) :=
  ((Subgroup.normalizer (S : Set G)).equivMapOfInjective e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr (Subgroup.map_equiv_normalizer_eq S e))

theorem normalizerEquiv_coe {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (S : Subgroup G) (g : Subgroup.normalizer (S : Set G)) :
    (normalizerEquiv e S g).val = e g.val := rfl

end CFSG.ComponentClassification.CatalogueBAlternating
