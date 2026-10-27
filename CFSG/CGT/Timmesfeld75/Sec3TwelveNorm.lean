module

public import CFSG.CGT.Timmesfeld75.Sec3TwelveCard

public section

namespace CFSG.CGT.Timmesfeld75

open scoped MatrixGroups
open CFSG.Open

section Induces

variable {G : Type} [Group G] [Finite G] {X M : Subgroup G} [hN : (M.subgroupOf X).Normal]
  {F : Type} [Field F] {a : G}

theorem InducesFieldAut.conj_X_eq {e : ↥X ⧸ M.subgroupOf X ≃* SL(2, F)} {σ : F ≃+* F}
    (h : InducesFieldAut X M a e σ) : conjSubgroup a X = X := by
  obtain ⟨ha, -⟩ := h
  refine conjSubgroup_eq_of_le fun y hy => ?_
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
  exact ha x hx

theorem InducesFieldAut.conj_M_eq {e : ↥X ⧸ M.subgroupOf X ≃* SL(2, F)}
    {σ : F ≃+* F} (h : InducesFieldAut X M a e σ) (hMX : M ≤ X) : conjSubgroup a M = M := by
  obtain ⟨ha, h⟩ := h
  refine conjSubgroup_eq_of_le fun y hy => ?_
  obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.1 hy
  have h1 := h ⟨m, hMX hm⟩
  have h2 : QuotientGroup.mk (⟨m, hMX hm⟩ : ↥X) = (1 : ↥X ⧸ M.subgroupOf X) :=
    (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 hm)
  rw [h2, map_one, map_one] at h1
  have h3 : QuotientGroup.mk (⟨a * m * a⁻¹, ha m (hMX hm)⟩ : ↥X) =
      (1 : ↥X ⧸ M.subgroupOf X) := e.injective (by rw [h1, map_one])
  exact Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 h3)

end Induces

section Normalize

variable {G : Type} [Group G] [Finite G]

theorem Sec3.conjSubgroup_eq_of_image_eq {T T₁ X M : Subgroup G} [hN : (M.subgroupOf X).Normal]
    (hS : Sec3 T T₁) (hX : T ⊔ T₁ = X) (hM : cfgM T T₁ = M) {a : G}
    (haX : conjSubgroup a X = X) (haM : conjSubgroup a M = M)
    (himage : ((conjSubgroup a T).subgroupOf X).map (QuotientGroup.mk' (M.subgroupOf X)) =
      (T.subgroupOf X).map (QuotientGroup.mk' (M.subgroupOf X))) :
    conjSubgroup a T = T := by
  subst hX
  subst hM
  obtain ⟨u, huT, huM⟩ := IsConcreteLE.not_le_iff_exists.1 hS.not_le_cfgM
  have huX : u ∈ T ⊔ T₁ := Subgroup.mem_sup_left huT
  have huu : u * u = 1 := elemAbelian_mul_self hS.cfg.wc.1 huT
  have hvX : a * u * a⁻¹ ∈ T ⊔ T₁ := by
    have h := conj_mem_conjSubgroup a huX
    rwa [haX] at h
  have hvv : (a * u * a⁻¹) * (a * u * a⁻¹) = 1 := by
    calc (a * u * a⁻¹) * (a * u * a⁻¹) = a * (u * u) * a⁻¹ := by group
      _ = 1 := by rw [huu]; group
  have hvM : a * u * a⁻¹ ∉ cfgM T T₁ := by
    intro h
    apply huM
    rw [← haM, mem_conjSubgroup] at h
    have e : a⁻¹ * (a * u * a⁻¹) * a = u := by group
    rwa [e] at h
  obtain ⟨w, hwX, hvw⟩ := hS.invol _ hvX hvv hvM
  have hv1 : a * u * a⁻¹ ≠ 1 := fun h => hvM (h ▸ (cfgM T T₁).one_mem)
  have hTw : conjSubgroup w T = conjSubgroup a T := by
    have hwc := hS.cfg.wc.conj a
    have h := hwc.conj_eq_of_inf_ne_bot (g := w * a⁻¹) (by
      intro hbot
      have hmem : a * u * a⁻¹ ∈
          conjSubgroup a T ⊓ conjSubgroup (w * a⁻¹) (conjSubgroup a T) := by
        refine ⟨conj_mem_conjSubgroup a huT, ?_⟩
        rw [conjSubgroup_conjSubgroup, show w * a⁻¹ * a = w by group]
        exact hvw
      rw [hbot, Subgroup.mem_bot] at hmem
      exact hv1 hmem)
    rw [conjSubgroup_conjSubgroup, show w * a⁻¹ * a = w by group] at h
    exact h
  have hle : ∀ y ∈ conjSubgroup w T, ∃ t ∈ T, ∃ m ∈ cfgM T T₁, y = t * m := by
    intro y hy
    rw [hTw] at hy
    have hyX : y ∈ T ⊔ T₁ := by
      obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 hy
      have h := conj_mem_conjSubgroup a (Subgroup.mem_sup_left hz : z ∈ T ⊔ T₁)
      rwa [haX] at h
    have hmem : QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)) ⟨y, hyX⟩ ∈
        ((conjSubgroup a T).subgroupOf (T ⊔ T₁)).map
          (QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁))) :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hy)
    rw [himage] at hmem
    obtain ⟨z, hz, hzy⟩ := hmem
    have h1 : (z : G)⁻¹ * y ∈ cfgM T T₁ := Subgroup.mem_subgroupOf.1 (QuotientGroup.eq.1 hzy)
    exact ⟨z, Subgroup.mem_subgroupOf.1 hz, _, h1, by group⟩
  exact hTw.symm.trans (hS.conjSubgroup_eq_of_le_mul_cfgM hwX hle)

theorem Sec3.conjSubgroup_conj_eq_of_image_eq {T T₁ X M : Subgroup G}
    [hN : (M.subgroupOf X).Normal] (hS : Sec3 T T₁) (hX : T ⊔ T₁ = X) (hM : cfgM T T₁ = M)
    {a w : G} (hw : w ∈ X) (haX : conjSubgroup a X = X)
    (haM : conjSubgroup a M = M)
    (himage : ((conjSubgroup a (conjSubgroup w T)).subgroupOf X).map
      (QuotientGroup.mk' (M.subgroupOf X)) =
      ((conjSubgroup w T).subgroupOf X).map (QuotientGroup.mk' (M.subgroupOf X))) :
    conjSubgroup a (conjSubgroup w T) = conjSubgroup w T := by
  have hw' : w ∈ T ⊔ T₁ := by rw [hX]; exact hw
  have hX' : conjSubgroup w T ⊔ conjSubgroup w T₁ = X := by
    rw [← conjSubgroup_sup_eq_sup, hX]
    exact mem_normalizer_iff_conjSubgroup_eq.1 (Subgroup.le_normalizer hw)
  have hM' : cfgM (conjSubgroup w T) (conjSubgroup w T₁) = M := by
    rw [cfgM_conj, hM]
    ext y
    rw [mem_conjSubgroup, ← hM]
    exact hS.cfg.inv_mul_mul_mem_cfgM_iff hw'
  exact Sec3.conjSubgroup_eq_of_image_eq (hS.conj_gen w) hX' hM' haX haM himage

theorem Sec3.exists_mem_conj_images {T T₁ X M : Subgroup G} [hN : (M.subgroupOf X).Normal]
    (hS : Sec3 T T₁) (hX : T ⊔ T₁ = X) (hM : cfgM T T₁ = M) {q : ℕ}
    (hpair : IsL2Pair (↥X ⧸ M.subgroupOf X)
      ((T.subgroupOf X).map (QuotientGroup.mk' (M.subgroupOf X))) q)
    {F : Type} [Field F] [Finite F] [CharP F 2] (e : ↥X ⧸ M.subgroupOf X ≃* SL(2, F)) :
    ∃ x ∈ X, (((conjSubgroup x T).subgroupOf X).map (QuotientGroup.mk' (M.subgroupOf X))).map
        e.toMonoidHom = utri F ∧
      (((conjSubgroup x T₁).subgroupOf X).map (QuotientGroup.mk' (M.subgroupOf X))).map
        e.toMonoidHom = ltri F := by
  subst hX
  subst hM
  let P₀ : Sylow 2 (↥(T ⊔ T₁) ⧸ (cfgM T T₁).subgroupOf (T ⊔ T₁)) :=
    Sylow.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective (utriSylow F)
  let Q : Sylow 2 SL(2, F) :=
    Sylow.mapSurjective (f := (MulAut.conj (wElt : SL(2, F))).toMonoidHom)
      (MulAut.conj (wElt : SL(2, F))).surjective (utriSylow F)
  let P₁ : Sylow 2 (↥(T ⊔ T₁) ⧸ (cfgM T T₁).subgroupOf (T ⊔ T₁)) :=
    Sylow.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective Q
  have hP₀ : (P₀ : Subgroup (↥(T ⊔ T₁) ⧸ (cfgM T T₁).subgroupOf (T ⊔ T₁))) =
      (utri F).map e.symm.toMonoidHom := rfl
  have hQ : (Q : Subgroup SL(2, F)) = ltri F := conjSubgroup_wElt_utri
  have hP₁ : (P₁ : Subgroup (↥(T ⊔ T₁) ⧸ (cfgM T T₁).subgroupOf (T ⊔ T₁))) =
      (ltri F).map e.symm.toMonoidHom := by
    rw [← hQ]
    rfl
  obtain ⟨c, hc⟩ := hpair.exists_conj_eq_sylow P₀
  obtain ⟨d, hd⟩ := hpair.exists_conj_eq_sylow P₁
  obtain ⟨x₀, hx₀, hT₁⟩ := hS.conj
  have hne1 : conjSubgroup (1 : ↥(T ⊔ T₁) ⧸ (cfgM T T₁).subgroupOf (T ⊔ T₁))
      ((T.subgroupOf (T ⊔ T₁)).map (QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)))) ≠
      conjSubgroup (QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)) ⟨x₀, hx₀⟩)
        ((T.subgroupOf (T ⊔ T₁)).map (QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)))) := by
    rw [conjSubgroup_one, ← map_subgroupOf_conjSubgroup_of_mem (T ⊔ T₁) (cfgM T T₁) T hx₀,
      ← hT₁]
    exact hS.map_ne_map.symm
  have hinj : Function.Injective e.symm.toMonoidHom := e.symm.injective
  have hne2 : conjSubgroup c
      ((T.subgroupOf (T ⊔ T₁)).map (QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)))) ≠
      conjSubgroup d
        ((T.subgroupOf (T ⊔ T₁)).map (QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)))) := by
    rw [hc, hd]
    intro h
    rw [hP₀, hP₁] at h
    have h' := Subgroup.map_injective hinj h
    have hmem : utriElt (1 : F) ∈ ltri F := by
      rw [← h']
      exact utriElt_mem_utri 1
    have h1 := (mem_ltri_entries.1 hmem).1
    rw [utriElt_apply_01] at h1
    exact one_ne_zero h1
  obtain ⟨g, hg1, hg2⟩ :=
    hpair.conjTwoTransitive 1 (QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)) ⟨x₀, hx₀⟩)
      c d hne1 hne2
  obtain ⟨x', rfl⟩ := QuotientGroup.mk_surjective g
  refine ⟨(x' : G), x'.2, ?_, ?_⟩
  · have h1 : ((conjSubgroup (x' : G) T).subgroupOf (T ⊔ T₁)).map
        (QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁))) =
        (utri F).map e.symm.toMonoidHom := by
      rw [map_subgroupOf_conjSubgroup_of_mem (T ⊔ T₁) (cfgM T T₁) T x'.2, ← hP₀, ← hc]
      rw [mul_one] at hg1
      exact hg1
    rw [h1]
    exact map_symm_map_mulEquiv e (utri F)
  · have hxx₀ : (x' : G) * x₀ ∈ T ⊔ T₁ := (T ⊔ T₁).mul_mem x'.2 hx₀
    have hcj : conjSubgroup (x' : G) T₁ = conjSubgroup ((x' : G) * x₀) T := by
      have h := conjSubgroup_conjSubgroup (x' : G) x₀ T
      rw [← hT₁] at h
      exact h
    have h1 : ((conjSubgroup (x' : G) T₁).subgroupOf (T ⊔ T₁)).map
        (QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁))) =
        (ltri F).map e.symm.toMonoidHom := by
      rw [hcj, map_subgroupOf_conjSubgroup_of_mem (T ⊔ T₁) (cfgM T T₁) T hxx₀, ← hP₁, ← hd]
      exact hg2
    rw [h1]
    exact map_symm_map_mulEquiv e (ltri F)

end Normalize

section Assemble

variable {G : Type} [Group G] [Finite G]

theorem Sec3.exists_data312 {T T₁ : Subgroup G}
    [hN : ((cfgM T T₁).subgroupOf (T ⊔ T₁)).Normal] (hS : Sec3 T T₁) {q : ℕ}
    (hpair : IsL2Pair (↥(T ⊔ T₁) ⧸ (cfgM T T₁).subgroupOf (T ⊔ T₁))
      ((T.subgroupOf (T ⊔ T₁)).map (QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)))) q)
    {F : Type} [Field F] [Finite F] [CharP F 2] {a : G} (haa : a * a = 1)
    (e : ↥(T ⊔ T₁) ⧸ (cfgM T T₁).subgroupOf (T ⊔ T₁) ≃* SL(2, F)) (σ : F ≃+* F)
    (hσ : σ ≠ RingEquiv.refl F) (hind : InducesFieldAut (T ⊔ T₁) (cfgM T T₁) a e σ) :
    ∃ x ∈ T ⊔ T₁, Nonempty
      (Data312 (conjSubgroup x T) (conjSubgroup x T₁) (T ⊔ T₁) (cfgM T T₁) F a) := by
  have haX : conjSubgroup a (T ⊔ T₁) = T ⊔ T₁ := hind.conj_X_eq
  have haM : conjSubgroup a (cfgM T T₁) = cfgM T T₁ := hind.conj_M_eq (cfgM_le_sup T T₁)
  obtain ⟨x, hxX, hx1, hx2⟩ := hS.exists_mem_conj_images rfl rfl hpair e
  obtain ⟨x₀, hx₀, hT₁⟩ := hS.conj
  have hXx : conjSubgroup x T ⊔ conjSubgroup x T₁ = T ⊔ T₁ := by
    rw [← conjSubgroup_sup_eq_sup]
    exact mem_normalizer_iff_conjSubgroup_eq.1 (Subgroup.le_normalizer hxX)
  have hMx : cfgM (conjSubgroup x T) (conjSubgroup x T₁) = cfgM T T₁ := by
    rw [cfgM_conj]
    ext y
    rw [mem_conjSubgroup]
    exact hS.cfg.inv_mul_mul_mem_cfgM_iff hxX
  have hφe : ∀ z, e (quotConjAut (T ⊔ T₁) (cfgM T T₁) a haX haM z) = sl2FieldAut σ (e z) := by
    intro z
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective z
    obtain ⟨ha, h⟩ := hind
    exact h y
  have hinv : ∀ (A : Subgroup (↥(T ⊔ T₁) ⧸ (cfgM T T₁).subgroupOf (T ⊔ T₁)))
      (B : Subgroup SL(2, F)), A.map e.toMonoidHom = B → (∀ g ∈ B, sl2FieldAut σ g ∈ B) →
      A.map (quotConjAut (T ⊔ T₁) (cfgM T T₁) a haX haM).toMonoidHom = A := by
    intro A B hAB hB
    have hle : A.map (quotConjAut (T ⊔ T₁) (cfgM T T₁) a haX haM).toMonoidHom ≤ A := by
      rintro _ ⟨z, hz, rfl⟩
      have hz' : e z ∈ B := hAB ▸ Subgroup.mem_map_of_mem e.toMonoidHom hz
      have h1 : e (quotConjAut (T ⊔ T₁) (cfgM T T₁) a haX haM z) ∈ B := by
        rw [hφe]
        exact hB _ hz'
      rw [← hAB] at h1
      exact (mem_map_mulEquiv_iff e).1 h1
    exact Subgroup.eq_of_le_of_card_ge hle
      (Subgroup.card_map_of_injective
        (quotConjAut (T ⊔ T₁) (cfgM T T₁) a haX haM).injective).symm.le
  have hU : ∀ g ∈ utri F, sl2FieldAut σ g ∈ utri F := fun g hg => by
    obtain ⟨s, rfl⟩ := mem_utri_iff.1 hg
    rw [sl2FieldAut_utriElt]
    exact utriElt_mem_utri _
  have hV : ∀ g ∈ ltri F, sl2FieldAut σ g ∈ ltri F := fun g hg => by
    obtain ⟨s, rfl⟩ := mem_ltri_iff.1 hg
    rw [sl2FieldAut_ltriElt]
    exact ltriElt_mem_ltri _
  have himT : ((conjSubgroup a (conjSubgroup x T)).subgroupOf (T ⊔ T₁)).map
      (QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁))) =
      ((conjSubgroup x T).subgroupOf (T ⊔ T₁)).map
        (QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁))) := by
    rw [map_subgroupOf_conjSubgroup_eq (T ⊔ T₁) (cfgM T T₁) a haX haM (conjSubgroup x T)]
    exact hinv _ _ hx1 hU
  have haT : conjSubgroup a (conjSubgroup x T) = conjSubgroup x T :=
    Sec3.conjSubgroup_conj_eq_of_image_eq hS rfl rfl hxX haX haM himT
  have hxx₀ : x * x₀ ∈ T ⊔ T₁ := (T ⊔ T₁).mul_mem hxX hx₀
  have hcj : conjSubgroup x T₁ = conjSubgroup (x * x₀) T := by
    have h := conjSubgroup_conjSubgroup x x₀ T
    rw [← hT₁] at h
    exact h
  have himT₁ : ((conjSubgroup a (conjSubgroup (x * x₀) T)).subgroupOf (T ⊔ T₁)).map
      (QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁))) =
      ((conjSubgroup (x * x₀) T).subgroupOf (T ⊔ T₁)).map
        (QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁))) := by
    rw [map_subgroupOf_conjSubgroup_eq (T ⊔ T₁) (cfgM T T₁) a haX haM
      (conjSubgroup (x * x₀) T), ← hcj]
    exact hinv _ _ hx2 hV
  have haT₁ : conjSubgroup a (conjSubgroup (x * x₀) T) = conjSubgroup (x * x₀) T :=
    Sec3.conjSubgroup_conj_eq_of_image_eq hS rfl rfl hxx₀ haX haM himT₁
  exact ⟨x, hxX, ⟨{ e := e
                    σ := σ
                    hX := hXx
                    hM := hMx
                    sec3 := hS.conj_gen x
                    aa := haa
                    aT := haT
                    aT₁ := by rw [hcj]; exact haT₁
                    eT := hx1
                    eT₁ := hx2
                    ind := hind
                    σ_ne := hσ }⟩⟩

end Assemble

end CFSG.CGT.Timmesfeld75
