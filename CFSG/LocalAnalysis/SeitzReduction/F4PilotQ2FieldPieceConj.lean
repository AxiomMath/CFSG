module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2FieldRowPiece

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint
open CFSG.Quasithin (perfectCore perfectCore_le)


section General

variable {G H : Type} [Group G] [Group H]

theorem map_centralizer_of_injective_q2p {f : G →* H} (hf : Function.Injective f)
    (S : Subgroup G) :
    (centralizer (S : Set G)).map f = f.range ⊓ centralizer ((S.map f : Subgroup H) : Set H) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨⟨y, rfl⟩, mem_centralizer_iff.2 ?_⟩
    rintro _ ⟨s, hs, rfl⟩
    rw [← map_mul, ← map_mul, mem_centralizer_iff.1 hy s hs]
  · rintro ⟨⟨y, rfl⟩, hx⟩
    refine ⟨y, mem_centralizer_iff.2 fun s hs => hf ?_, rfl⟩
    rw [map_mul, map_mul]
    exact mem_centralizer_iff.1 hx (f s) ⟨s, hs, rfl⟩

theorem perfectCore_inf_centralizer_map_conj_inv [Finite G] (D S : Subgroup G) (m : G) :
    perfectCore (D ⊓ centralizer ((S.map (MulAut.conj m⁻¹).toMonoidHom : Subgroup G) : Set G)) =
      (perfectCore (D.map (MulAut.conj m).toMonoidHom ⊓ centralizer (S : Set G))).map
        (MulAut.conj m⁻¹).toMonoidHom := by
  rw [CFSG.Quasithin.map_perfectCore, Subgroup.map_inf_eq _ _ _ (MulAut.conj m⁻¹).injective,
    map_centralizer_mulEquiv, Subgroup.map_map]
  congr 2
  conv_lhs => rw [← Subgroup.map_id D]
  congr 1
  ext x
  simp only [MulAut.conj_apply, MonoidHom.id_apply, MonoidHom.coe_comp, Function.comp_apply,
    MulEquiv.coe_toMonoidHom, inv_inv]
  group

end General

section Weyl

variable {k K : Type} [Field k] [Field K]

theorem map_conj_baseChangeGL_weylRepC_rootSpan_orthRoots (ι : k →+* K) (w : WeylGroup .F4)
    (θ : Fin (Tag.rank .F4) → ℤ) :
    (rootSpan .F4 K (orthRoots θ)).map (MulAut.conj
        (baseChangeGL ι ((weylRepC k w : adjointGroup .F4 k) : ModGL .F4 k))).toMonoidHom =
      rootSpan .F4 K (orthRoots (w • θ)) := by
  change (rootSpan .F4 K (orthRoots θ)).map
      (MulAut.conj (baseChangeGL ι (canonicalRep (coxeterSystem .F4) k w))).toMonoidHom = _
  rw [CFSG.LieType.Chevalley.baseChangeGL_canonicalRep,
    (canonical_weyl_root_transport .F4 K).1 w _ fun α hα => hα.1, image_smul_orthRoots]

theorem map_conj_weylRepC_le_rootPair (w : WeylGroup .F4) {γ : Fin (Tag.rank .F4) → ℤ}
    (hγ : IsRoot .F4 γ) {A : Subgroup (adjointGroup .F4 k)}
    (hA : A.map (adjointGroup .F4 k).subtype ≤ rootSubgroup .F4 k γ ⊔ rootSubgroup .F4 k (-γ)) :
    (A.map (MulAut.conj (weylRepC k w)).toMonoidHom).map (adjointGroup .F4 k).subtype ≤
      rootSubgroup .F4 k (w • γ) ⊔ rootSubgroup .F4 k (-(w • γ)) := by
  rw [map_conj_weylRepC_map_subtype]
  refine (Subgroup.map_mono hA).trans ?_
  rw [Subgroup.map_sup, (canonical_weyl_root_transport .F4 k).2.1 w γ hγ,
    (canonical_weyl_root_transport .F4 k).2.1 w (-γ) (IsRoot.neg hγ), smul_neg]

end Weyl

section Image

variable {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {G : Type} [Group G] [Finite G]
  {L : Subgroup G} {e : L ≃* adjointGroup .F4 (fixSubfield σ)}

theorem map_subtype_neighbourLevi_q2p (N : AmalgamNeighbour) :
    (N.levi K).map (adjointGroup .F4 K).subtype = rootSpan .F4 K (orthRoots N.root) := by
  rw [AmalgamNeighbour.levi_eq K N, subgroupOf_map_subtype,
    inf_of_le_left (CFSG.LieType.Chevalley.rootSpan_le_adjointGroup K _)]

@[expose] noncomputable def Q2FieldParam.imageGL {N : AmalgamNeighbour} {E : Subgroup G}
    (h : Q2FieldParam σ e N E) (H : Subgroup (ModGL .F4 K)) : Subgroup G :=
  (((H.subgroupOf (adjointGroup .F4 K)).subgroupOf (N.levi K)).map h.Φ.toMonoidHom).map E.subtype

theorem Q2FieldParam.range_restrict_eq_imageGL {N : AmalgamNeighbour} {E : Subgroup G}
    (h : Q2FieldParam σ e N E) {J : Finset (Fin (Tag.rank .F4))} (hJ : J ⊆ N.nodes) :
    (h.restrict hJ).range = h.imageGL (rootSpan .F4 K (amalgamRoots J)) := by
  rw [h.range_restrict_eq_map, levi_f4Datum_eq, Q2FieldParam.imageGL, Subgroup.map_map]

theorem centralizerPerfectCore_map_leviInclusion_eq (N : AmalgamNeighbour)
    {W : Subgroup (adjointGroup .F4 (fixSubfield σ))} (hW : W ≤ N.levi (fixSubfield σ)) :
    centralizerPerfectCore ((W.subgroupOf (N.levi (fixSubfield σ))).map (leviInclusion σ N)) =
      ((perfectCore (rootSpan .F4 K (orthRoots N.root) ⊓ centralizer
        (((W.map (adjointGroup .F4 (fixSubfield σ)).subtype).map
          (baseChangeGL (fixSubfield σ).subtype) : Subgroup (ModGL .F4 K)) :
            Set (ModGL .F4 K)))).subgroupOf (adjointGroup .F4 K)).subgroupOf (N.levi K) := by
  have := finite_levi K N
  have : Finite (ModGL .F4 K) := finite_modGL
  set ψ : N.levi K →* ModGL .F4 K := (adjointGroup .F4 K).subtype.comp (N.levi K).subtype
    with hψdef
  have hψ : Function.Injective ψ :=
    (adjointGroup .F4 K).subtype_injective.comp (N.levi K).subtype_injective
  have hrange : ψ.range = rootSpan .F4 K (orthRoots N.root) := by
    rw [hψdef, MonoidHom.range_comp, Subgroup.range_subtype, map_subtype_neighbourLevi_q2p]
  have hcomp : ψ.comp (leviInclusion σ N) = (baseChangeGL (fixSubfield σ).subtype).comp
      ((adjointGroup .F4 (fixSubfield σ)).subtype.comp (N.levi (fixSubfield σ)).subtype) :=
    MonoidHom.ext fun x => coe_leviInclusion σ N x
  have hW' : ((W.subgroupOf (N.levi (fixSubfield σ))).map (leviInclusion σ N)).map ψ =
      (W.map (adjointGroup .F4 (fixSubfield σ)).subtype).map
        (baseChangeGL (fixSubfield σ).subtype) := by
    rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, ← Subgroup.map_map, subgroupOf_map_subtype,
      inf_of_le_left hW]
  set Q := perfectCore (rootSpan .F4 K (orthRoots N.root) ⊓ centralizer
    (((W.map (adjointGroup .F4 (fixSubfield σ)).subtype).map
      (baseChangeGL (fixSubfield σ).subtype) : Subgroup (ModGL .F4 K)) : Set (ModGL .F4 K)))
    with hQ
  have hQD : Q ≤ rootSpan .F4 K (orthRoots N.root) := (perfectCore_le _).trans inf_le_left
  apply Subgroup.map_injective hψ
  rw [centralizerPerfectCore, CFSG.Quasithin.map_perfectCore, map_centralizer_of_injective_q2p hψ,
    hrange, hW', hψdef, ← Subgroup.map_map, subgroupOf_map_subtype,
    Subgroup.map_inf_eq _ _ _ (adjointGroup .F4 K).subtype_injective, subgroupOf_map_subtype,
    map_subtype_neighbourLevi_q2p,
    inf_of_le_left (hQD.trans (CFSG.LieType.Chevalley.rootSpan_le_adjointGroup K _)),
    inf_of_le_left hQD]

theorem Q2FieldParam.centralizerPerfectCore_sup_eq_imageGL {N : AmalgamNeighbour}
    {E X : Subgroup G} (h : Q2FieldParam σ e N E) (hE : E = centralizerPerfectCore X)
    {W : Subgroup (adjointGroup .F4 (fixSubfield σ))} (hW : W ≤ N.levi (fixSubfield σ)) :
    centralizerPerfectCore (X ⊔ subgroupToG e W) =
      h.imageGL (perfectCore (rootSpan .F4 K (orthRoots N.root) ⊓ centralizer
        (((W.map (adjointGroup .F4 (fixSubfield σ)).subtype).map
          (baseChangeGL (fixSubfield σ).subtype) : Subgroup (ModGL .F4 K)) :
            Set (ModGL .F4 K)))) := by
  subst hE
  have hWW : (W.subgroupOf (N.levi (fixSubfield σ))).map (N.levi (fixSubfield σ)).subtype = W := by
    rw [subgroupOf_map_subtype, inf_of_le_left hW]
  have h1 := h.centralizerPerfectCore_sup_eq_map_levi (W.subgroupOf (N.levi (fixSubfield σ)))
  rw [hWW] at h1
  rw [h1, centralizerPerfectCore_map_leviInclusion_eq N hW]
  rfl

theorem Q2FieldParam.range_restrict_eq_centralizerPerfectCore_sup_GL {N : AmalgamNeighbour}
    {E X : Subgroup G} (h : Q2FieldParam σ e N E) (hE : E = centralizerPerfectCore X)
    {J : Finset (Fin (Tag.rank .F4))} (hJ : J ⊆ N.nodes)
    {W : Subgroup (adjointGroup .F4 (fixSubfield σ))} (hW : W ≤ N.levi (fixSubfield σ))
    (hP : perfectCore (rootSpan .F4 K (orthRoots N.root) ⊓ centralizer
        (((W.map (adjointGroup .F4 (fixSubfield σ)).subtype).map
          (baseChangeGL (fixSubfield σ).subtype) : Subgroup (ModGL .F4 K)) :
            Set (ModGL .F4 K))) = rootSpan .F4 K (amalgamRoots J)) :
    (h.restrict hJ).range = centralizerPerfectCore (X ⊔ subgroupToG e W) := by
  rw [h.range_restrict_eq_imageGL hJ, h.centralizerPerfectCore_sup_eq_imageGL hE hW, hP]

theorem subgroupToG_map_conj_q2p (e : L ≃* adjointGroup .F4 (fixSubfield σ))
    (U : Subgroup (adjointGroup .F4 (fixSubfield σ))) (n : adjointGroup .F4 (fixSubfield σ)) :
    subgroupToG e (U.map (MulAut.conj n).toMonoidHom) =
      (subgroupToG e U).map (MulAut.conj ((e.symm n : L) : G)).toMonoidHom := by
  unfold subgroupToG
  rw [Subgroup.map_map, Subgroup.map_map, Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply]

theorem Q2FieldParam.centralizerPerfectCore_map_conj_sup_eq_imageGL {N : AmalgamNeighbour}
    {E X : Subgroup G} (h : Q2FieldParam σ e N E) (hE : E = centralizerPerfectCore X)
    (n : adjointGroup .F4 (fixSubfield σ)) {U : Subgroup (adjointGroup .F4 (fixSubfield σ))}
    (hU : U.map (MulAut.conj n⁻¹).toMonoidHom ≤ N.levi (fixSubfield σ)) :
    centralizerPerfectCore (X.map (MulAut.conj ((e.symm n : L) : G)).toMonoidHom ⊔
        subgroupToG e U) =
      (h.imageGL ((perfectCore ((rootSpan .F4 K (orthRoots N.root)).map
          (MulAut.conj (baseChangeGL (fixSubfield σ).subtype
            (n : ModGL .F4 (fixSubfield σ)))).toMonoidHom ⊓ centralizer
          (((U.map (adjointGroup .F4 (fixSubfield σ)).subtype).map
            (baseChangeGL (fixSubfield σ).subtype) : Subgroup (ModGL .F4 K)) :
              Set (ModGL .F4 K)))).map
        (MulAut.conj (baseChangeGL (fixSubfield σ).subtype
          (n : ModGL .F4 (fixSubfield σ)))⁻¹).toMonoidHom)).map
        (MulAut.conj ((e.symm n : L) : G)).toMonoidHom := by
  have hUU : (U.map (MulAut.conj n⁻¹).toMonoidHom).map (MulAut.conj n).toMonoidHom = U := by
    rw [Subgroup.map_map]
    conv_rhs => rw [← Subgroup.map_id U]
    congr 1
    ext x
    simp only [MulAut.conj_apply, MonoidHom.id_apply, MonoidHom.coe_comp, Function.comp_apply,
      MulEquiv.coe_toMonoidHom]
    group
  have hU' : subgroupToG e U = (subgroupToG e (U.map (MulAut.conj n⁻¹).toMonoidHom)).map
      (MulAut.conj ((e.symm n : L) : G)).toMonoidHom := by
    rw [← subgroupToG_map_conj_q2p, hUU]
  rw [hU', ← Subgroup.map_sup, ← map_centralizerPerfectCore,
    h.centralizerPerfectCore_sup_eq_imageGL hE hU, ← perfectCore_inf_centralizer_map_conj_inv]
  congr 6
  rw [Subgroup.map_map, Subgroup.map_map, Subgroup.map_map, Subgroup.map_map]
  congr 1
  refine MonoidHom.ext fun x => ?_
  change baseChangeGL (fixSubfield σ).subtype
      ((n⁻¹ * x * n⁻¹⁻¹ : adjointGroup .F4 (fixSubfield σ)) : ModGL .F4 (fixSubfield σ)) =
    (baseChangeGL (fixSubfield σ).subtype (n : ModGL .F4 (fixSubfield σ)))⁻¹ *
      baseChangeGL (fixSubfield σ).subtype (x : ModGL .F4 (fixSubfield σ)) *
        (baseChangeGL (fixSubfield σ).subtype (n : ModGL .F4 (fixSubfield σ)))⁻¹⁻¹
  rw [inv_inv, inv_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_mul,
    map_inv]

theorem Q2FieldParam.centralizerPerfectCore_map_conj_sup_eq {N : AmalgamNeighbour}
    {E X : Subgroup G} (h : Q2FieldParam σ e N E) (hE : E = centralizerPerfectCore X)
    (n : adjointGroup .F4 (fixSubfield σ)) {U U' : Subgroup (adjointGroup .F4 (fixSubfield σ))}
    (hU : U.map (MulAut.conj n⁻¹).toMonoidHom ≤ N.levi (fixSubfield σ))
    (hU' : U'.map (MulAut.conj n⁻¹).toMonoidHom ≤ N.levi (fixSubfield σ))
    (hUU' : perfectCore ((rootSpan .F4 K (orthRoots N.root)).map
          (MulAut.conj (baseChangeGL (fixSubfield σ).subtype
            (n : ModGL .F4 (fixSubfield σ)))).toMonoidHom ⊓ centralizer
          (((U.map (adjointGroup .F4 (fixSubfield σ)).subtype).map
            (baseChangeGL (fixSubfield σ).subtype) : Subgroup (ModGL .F4 K)) :
              Set (ModGL .F4 K))) =
      perfectCore ((rootSpan .F4 K (orthRoots N.root)).map
          (MulAut.conj (baseChangeGL (fixSubfield σ).subtype
            (n : ModGL .F4 (fixSubfield σ)))).toMonoidHom ⊓ centralizer
          (((U'.map (adjointGroup .F4 (fixSubfield σ)).subtype).map
            (baseChangeGL (fixSubfield σ).subtype) : Subgroup (ModGL .F4 K)) :
              Set (ModGL .F4 K)))) :
    centralizerPerfectCore (X.map (MulAut.conj ((e.symm n : L) : G)).toMonoidHom ⊔
        subgroupToG e U) =
      centralizerPerfectCore (X.map (MulAut.conj ((e.symm n : L) : G)).toMonoidHom ⊔
        subgroupToG e U') := by
  rw [h.centralizerPerfectCore_map_conj_sup_eq_imageGL hE n hU,
    h.centralizerPerfectCore_map_conj_sup_eq_imageGL hE n hU', hUU']

end Image

end CFSG.SeitzReduction.F4Pilot
