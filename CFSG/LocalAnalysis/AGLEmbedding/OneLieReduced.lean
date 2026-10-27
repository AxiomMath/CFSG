module

public import CFSG.LocalAnalysis.AGLEmbedding.OneLieDefs

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.PreuniquenessRankFour.Helpers

section Reduced

variable {Y : Type} [Group Y] [Finite Y] {p : ℕ} {Rb : Sylow p Y} {Y₀ : Subgroup Y}

theorem isCyclic_inf_of_isCyclic_inf_map [Fact p.Prime] (R : Sylow p Y) {K : Subgroup Y}
    (e : Y ≃* Y) (hK : K.IsSubnormal) (hKe : (K.map e.toMonoidHom).IsSubnormal)
    (hc : IsCyclic ((R : Subgroup Y) ⊓ K.map e.toMonoidHom : Subgroup Y)) :
    IsCyclic ((R : Subgroup Y) ⊓ K : Subgroup Y) := by
  set L := K.map e.toMonoidHom
  obtain ⟨P, hP⟩ := Walter.exists_sylow_map_eq_inf_of_isSubnormal R hK
  obtain ⟨P', hP'⟩ := Walter.exists_sylow_map_eq_inf_of_isSubnormal R hKe
  let f : K ≃* L := K.equivMapOfInjective e.toMonoidHom e.injective
  have hf : Function.Surjective f.toMonoidHom := f.surjective
  let Q : Sylow p L := P.mapSurjective hf
  have E : ((R : Subgroup Y) ⊓ K : Subgroup Y) ≃* ((R : Subgroup Y) ⊓ L : Subgroup Y) :=
    (((MulEquiv.subgroupCongr hP).symm.trans
      ((P : Subgroup K).equivMapOfInjective K.subtype K.subtype_injective).symm).trans
      (((P : Subgroup K).equivMapOfInjective f.toMonoidHom f.injective).trans
        (MulEquiv.subgroupCongr (Sylow.coe_mapSurjective (f := f.toMonoidHom) hf P).symm))).trans
    ((Sylow.equiv Q P').trans
      (((P' : Subgroup L).equivMapOfInjective L.subtype L.subtype_injective).trans
        (MulEquiv.subgroupCongr hP')))
  exact isCyclic_of_surjective E.symm.toMonoidHom E.symm.surjective

theorem ReducedNongeneration.normal_of_rankOne (h : ReducedNongeneration p Y Rb Y₀)
    {K : Subgroup Y} (hK : IsComponentOf K ⊤)
    (hnc : ¬ IsCyclic ((Rb : Subgroup Y) ⊓ K : Subgroup Y)) : K.Normal := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hrK : 2 ≤ Open.pRank p ((Rb : Subgroup Y) ⊓ K) :=
    two_le_pRank_of_isPGroup_not_isCyclic hp h.ne_two (Rb.isPGroup'.to_le inf_le_left) hnc
  refine ⟨fun n hn g => ?_⟩
  have hL : IsComponentOf (K.map (MulAut.conj g).toMonoidHom) ⊤ :=
    (ComponentClassification.LocalComponents.equiv_iff (MulAut.conj g) K).mpr hK
  have hncL : ¬ IsCyclic ((Rb : Subgroup Y) ⊓ K.map (MulAut.conj g).toMonoidHom :
      Subgroup Y) := fun hc =>
    hnc (isCyclic_inf_of_isCyclic_inf_map Rb (MulAut.conj g)
      (ComponentClassification.Components.mathlib_subnormal_of_chain hK.2.1
        Subgroup.IsSubnormal.top)
      (ComponentClassification.Components.mathlib_subnormal_of_chain hL.2.1
        Subgroup.IsSubnormal.top) hc)
  have hrL : 2 ≤ Open.pRank p ((Rb : Subgroup Y) ⊓ K.map (MulAut.conj g).toMonoidHom) :=
    two_le_pRank_of_isPGroup_not_isCyclic hp h.ne_two (Rb.isPGroup'.to_le inf_le_left) hncL
  rw [← h.eq_of_two_le_pRank hL hK hrL hrK]
  exact ⟨n, hn, rfl⟩

theorem ReducedNongeneration.centralizer_le_of_rankOne (h : ReducedNongeneration p Y Rb Y₀)
    {K : Subgroup Y} (hnc : ¬ IsCyclic ((Rb : Subgroup Y) ⊓ K : Subgroup Y)) {z : Y}
    (hzR : z ∈ (Rb : Subgroup Y)) (hzK : z ∉ K) (hzp : orderOf z = p)
    (hzc : z ∈ Subgroup.centralizer (K : Set Y)) :
    Subgroup.centralizer (K : Set Y) ≤ Y₀ :=
  (Subgroup.centralizer_le inf_le_right).trans ((Subgroup.centralizer_le_normalizer _).trans
    (h.normalizer_inf_le_of_rankOne hnc hzR hzK hzp hzc))

theorem ReducedNongeneration.isCyclic_of_le_centralizer (h : ReducedNongeneration p Y Rb Y₀)
    {K : Subgroup Y} [K.Normal] (hK : IsComponentOf K ⊤) (hKY₀ : ¬ K ≤ Y₀) {A : Subgroup Y}
    (hA : IsPGroup p A) (hAC : A ≤ Subgroup.centralizer (K : Set Y)) : IsCyclic A := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  by_contra hnc
  obtain ⟨S, hAS⟩ := hA.exists_le_sylow
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq Y Rb S
  set A' := A.map (MulAut.conj g⁻¹).toMonoidHom
  have hA'le : A' ≤ (Rb : Subgroup Y) ⊓ Subgroup.centralizer (K : Set Y) := by
    rintro _ ⟨a, ha, rfl⟩
    have haS : a ∈ ((g • Rb : Sylow p Y) : Subgroup Y) := hAS ha
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def,
      ← map_inv, MulAut.conj_apply, inv_inv] at haS
    have hconj : (MulAut.conj g⁻¹).toMonoidHom a = g⁻¹ * a * g := by
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [hconj]
    exact ⟨haS, (inferInstance : (Subgroup.centralizer (K : Set Y)).Normal).conj_mem' a
      (hAC ha) g⟩
  have hncA' : ¬ IsCyclic A' := fun hc =>
    let e := A.equivMapOfInjective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective
    hnc (isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective)
  have h2 : 2 ≤ Open.pRank p A' :=
    two_le_pRank_of_isPGroup_not_isCyclic hp h.ne_two (hA.map _) hncA'
  have h1 := h.pRank_inf_centralizer_le_one_of_not_le hK hKY₀
  have h3 := pRank_mono p hp hA'le
  omega

end Reduced

section OneLieFacts

variable {Y : Type} [Group Y] [Finite Y] {p : ℕ} {Rb : Sylow p Y}

omit [Finite Y] in
theorem inv_mul_mem_centralizer_of_conjNormal_eq {K : Subgroup Y} [K.Normal] {y : Y} {t : K}
    (hyt : MulAut.conjNormal y = MulAut.conj t) :
    (t : Y)⁻¹ * y ∈ Subgroup.centralizer (K : Set Y) := by
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  have h1 : y * k * y⁻¹ = t * k * (t : Y)⁻¹ := by
    have := congrArg (fun f : MulAut K => ((f ⟨k, hk⟩ : K) : Y)) hyt
    simpa only [MulAut.conjNormal_apply, MulAut.conj_apply, Subgroup.coe_mul,
      Subgroup.coe_inv] using this
  calc k * ((t : Y)⁻¹ * y) = (t : Y)⁻¹ * (t * k * (t : Y)⁻¹) * y := by group
    _ = (t : Y)⁻¹ * (y * k * y⁻¹) * y := by rw [h1]
    _ = (t : Y)⁻¹ * y * k := by group

omit [Finite Y] in
theorem map_subtype_centerOf {K : Subgroup Y} (T : Subgroup K) :
    (centerOf T).map K.subtype = centerOf (T.map K.subtype) := by
  ext y
  constructor
  · rintro ⟨x, ⟨hxT, hxC⟩, rfl⟩
    refine ⟨⟨x, hxT, rfl⟩, Subgroup.mem_centralizer_iff.mpr ?_⟩
    rintro _ ⟨x', hx'T, rfl⟩
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hxC x' hx'T)
  · rintro ⟨⟨x, hxT, rfl⟩, hyC⟩
    refine ⟨x, ⟨hxT, Subgroup.mem_centralizer_iff.mpr fun x' hx'T => Subtype.ext ?_⟩, rfl⟩
    exact Subgroup.mem_centralizer_iff.mp hyC _ ⟨x', hx'T, rfl⟩

omit [Finite Y] in
theorem coe_mem_normalizer_map {K : Subgroup Y} {T : Subgroup K} {n : K}
    (hn : n ∈ Subgroup.normalizer (T : Set K)) :
    (n : Y) ∈ K ⊓ Subgroup.normalizer ((T.map K.subtype : Subgroup Y) : Set Y) :=
  ⟨n.2, Subgroup.le_normalizer_map K.subtype ⟨n, hn, rfl⟩⟩

theorem centralizer_le_sup_of_oneLieFacts {K : Subgroup Y} [K.Normal]
    (_hZ : Subgroup.center K = ⊥) (T₁ : Sylow p K) (hF : OneLieFacts p K T₁)
    {V : Subgroup Y} (hVT : V ≤ (T₁ : Subgroup K).map K.subtype) (hV : V ≠ ⊥)
    (hNV : K ⊓ Subgroup.normalizer (((T₁ : Subgroup K).map K.subtype : Subgroup Y) : Set Y) ≤
      Subgroup.normalizer (V : Set Y)) :
    Subgroup.centralizer (V : Set Y) ≤
        (T₁ : Subgroup K).map K.subtype ⊔ Subgroup.centralizer (K : Set Y) ∨
      (V = centerOf ((T₁ : Subgroup K).map K.subtype) ∧ IsUnitaryGroup p K) := by
  have hVK : V ≤ K := hVT.trans (Subgroup.map_subtype_le _)
  have hVmap : (V.subgroupOf K).map K.subtype = V := Subgroup.map_subgroupOf_eq_of_le hVK
  have hV'T : V.subgroupOf K ≤ T₁ := by
    intro v hv
    obtain ⟨t, ht, htv⟩ := hVT (Subgroup.mem_subgroupOf.mp hv)
    rwa [← Subtype.ext htv]
  have hV'1 : V.subgroupOf K ≠ ⊥ := by
    intro hbot
    apply hV
    rw [← hVmap, hbot, Subgroup.map_bot]
  have hNV' : Subgroup.normalizer ((T₁ : Subgroup K) : Set K) ≤
      Subgroup.normalizer ((V.subgroupOf K : Subgroup K) : Set K) := fun n hn =>
    Subgroup.le_normalizer_comap K.subtype (hNV (coe_mem_normalizer_map hn))
  rcases hF.centralizer _ hV'T hV'1 hNV' with hall | ⟨hcen, hU⟩
  · refine Or.inl fun y hy => ?_
    obtain ⟨t, ht, hyt⟩ := hall (MulAut.conjNormal y) fun v hv => by
      apply Subtype.ext
      rw [MulAut.conjNormal_apply,
        ← Subgroup.mem_centralizer_iff.mp hy (v : Y) (Subgroup.mem_subgroupOf.mp hv)]
      group
    have e : y = (t : Y) * ((t : Y)⁻¹ * y) := by group
    rw [e]
    exact Subgroup.mul_mem_sup ⟨t, ht, rfl⟩ (inv_mul_mem_centralizer_of_conjNormal_eq hyt)
  · refine Or.inr ⟨?_, hU⟩
    rw [← hVmap, hcen, map_subtype_centerOf]

theorem le_sup_of_oneLieFacts {K : Subgroup Y} [K.Normal] (_hZ : Subgroup.center K = ⊥)
    (T₁ : Sylow p K) (hT₁ : (T₁ : Subgroup K).map K.subtype = (Rb : Subgroup Y) ⊓ K)
    (hF : OneLieFacts p K T₁) {W : Subgroup Y} (hW : IsPGroup p W) (hWR : W ≤ Rb)
    (hWn : K ⊓ Subgroup.normalizer ((((Rb : Subgroup Y) ⊓ K : Subgroup Y)) : Set Y) ≤
      Subgroup.normalizer (W : Set Y)) :
    W ≤ ((Rb : Subgroup Y) ⊓ K) ⊔ ((Rb : Subgroup Y) ⊓ Subgroup.centralizer (K : Set Y)) := by
  have key : ∀ (f : MulAut K) (t : K), f * MulAut.conj t * f⁻¹ = MulAut.conj (f t) := by
    intro f t
    ext k
    simp [MulAut.mul_apply, MulAut.inv_def]
  have hmem : W.map (MulAut.conjNormal (H := K)) ≤
      (T₁ : Subgroup K).map (MulAut.conj : K →* MulAut K) := by
    refine hF.pSubgroup_le _ (hW.map _) ?_ ?_
    · refine le_normalizer_of_forall_mul_mul_inv_mem ?_
      rintro _ ⟨w, hw, rfl⟩ _ ⟨t, ht, rfl⟩
      rw [key]
      have htY : (t : Y) ∈ (Rb : Subgroup Y) ⊓ K := hT₁ ▸ ⟨t, ht, rfl⟩
      have hwt : w * t * w⁻¹ ∈ (T₁ : Subgroup K).map K.subtype := by
        rw [hT₁]
        exact ⟨Rb.mul_mem (Rb.mul_mem (hWR hw) htY.1) (Rb.inv_mem (hWR hw)),
          ‹K.Normal›.conj_mem _ htY.2 w⟩
      obtain ⟨s, hs, hsw⟩ := hwt
      refine ⟨s, hs, congrArg MulAut.conj (Subtype.ext ?_)⟩
      rw [MulAut.conjNormal_apply]
      exact hsw
    · rintro _ ⟨n, hn, rfl⟩
      have hnW : (n : Y) ∈ Subgroup.normalizer (W : Set Y) :=
        hWn (hT₁ ▸ coe_mem_normalizer_map hn)
      rw [← MulAut.conjNormal_val]
      exact Subgroup.le_normalizer_map _ ⟨n, hnW, rfl⟩
  intro w hw
  obtain ⟨t, ht, hwt⟩ := hmem ⟨w, hw, rfl⟩
  have htR : (t : Y) ∈ (Rb : Subgroup Y) ⊓ K := hT₁ ▸ ⟨t, ht, rfl⟩
  have e : w = (t : Y) * ((t : Y)⁻¹ * w) := by group
  rw [e]
  exact Subgroup.mul_mem_sup htR ⟨Rb.mul_mem (Rb.inv_mem htR.1) (hWR hw),
    inv_mul_mem_centralizer_of_conjNormal_eq hwt.symm⟩

end OneLieFacts

end CFSG.AGLEmbedding
