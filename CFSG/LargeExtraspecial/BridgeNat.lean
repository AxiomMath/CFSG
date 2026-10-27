module

public import CFSG.Open.TimmesfeldLargeExtraspecialMilestoneDefs
public import CFSG.LargeExtraspecial.Transport

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.Bridge

open Subgroup

variable {H K : Type*} [Group H] [Group K]

theorem map_sSup_setOf (e : H ≃* K) {P : Subgroup H → Prop} {P' : Subgroup K → Prop}
    (h : ∀ N, P' (N.map e.toMonoidHom) ↔ P N) :
    (sSup {N | P N}).map e.toMonoidHom = sSup {N | P' N} := by
  apply le_antisymm
  · rw [map_le_iff_le_comap]
    refine sSup_le fun N hN => ?_
    rw [← map_le_iff_le_comap]
    exact le_sSup ((h N).mpr hN)
  · refine sSup_le fun N hN => ?_
    rw [← map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective N] at hN ⊢
    exact map_mono (le_sSup ((h _).mp hN))

@[expose] noncomputable def equivOfMapEq (e : H ≃* K) {N : Subgroup H} {N' : Subgroup K}
    (h : N.map e.toMonoidHom = N') : N ≃* N' :=
  (e.subgroupMap N).trans (MulEquiv.subgroupCongr h)

@[simp] theorem coe_equivOfMapEq (e : H ≃* K) {N : Subgroup H} {N' : Subgroup K}
    (h : N.map e.toMonoidHom = N') (x : N) : (equivOfMapEq e h x : K) = e x := rfl

@[expose] noncomputable def mapEquiv (e : H ≃* K) (N : Subgroup H) : N ≃* N.map e.toMonoidHom :=
  equivOfMapEq e rfl

@[simp] theorem coe_mapEquiv (e : H ≃* K) (N : Subgroup H) (x : N) :
    (mapEquiv e N x : K) = e x := rfl

theorem normal_map_iff (e : H ≃* K) (N : Subgroup H) :
    (N.map e.toMonoidHom).Normal ↔ N.Normal := by
  refine ⟨fun h => ?_, fun h => h.map _ e.surjective⟩
  have := h.comap e.toMonoidHom
  rwa [comap_map_eq_self_of_injective e.injective] at this

theorem commutator_map_mulEquiv (e : H ≃* K) :
    (commutator H).map e.toMonoidHom = commutator K := by
  rw [_root_.commutator_def, _root_.commutator_def, map_commutator,
    map_top_of_surjective _ e.surjective]

theorem frattini_map_mulEquiv (e : H ≃* K) : (frattini H).map e.toMonoidHom = frattini K :=
  OrderIso.map_radical (MulEquiv.mapSubgroup e)

theorem isQuasisimple_of_mulEquiv (e : H ≃* K) (h : CFSG.Open.IsQuasisimple H) :
    CFSG.Open.IsQuasisimple K := by
  obtain ⟨hc, hs⟩ := h
  refine ⟨?_, ?_⟩
  · rw [← commutator_map_mulEquiv e, hc, map_top_of_surjective _ e.surjective]
  · exact (MulEquiv.isSimpleGroup_congr
      (QuotientGroup.congr (center H) (center K) e (map_center_of_mulEquiv e))).mp hs

theorem isQuasisimple_congr (e : H ≃* K) :
    CFSG.Open.IsQuasisimple H ↔ CFSG.Open.IsQuasisimple K :=
  ⟨fun h => h.of_mulEquiv e.symm, fun h => h.of_mulEquiv e⟩

theorem timmesfeldIsExtraspecial_of_mulEquiv (e : H ≃* K)
    (h : CFSG.Open.timmesfeldIsExtraspecial H) : CFSG.Open.timmesfeldIsExtraspecial K := by
  obtain ⟨hp, hcomm, hfrat, hcard⟩ := h
  refine ⟨hp.of_equiv e, ?_, ?_, ?_⟩
  · rw [← commutator_map_mulEquiv e, hcomm, frattini_map_mulEquiv]
  · rw [← frattini_map_mulEquiv e, hfrat, map_center_of_mulEquiv]
  · rw [← map_center_of_mulEquiv e, card_map_of_injective e.injective, hcard]

theorem timmesfeldIsExtraspecial_congr (e : H ≃* K) :
    CFSG.Open.timmesfeldIsExtraspecial H ↔ CFSG.Open.timmesfeldIsExtraspecial K :=
  ⟨timmesfeldIsExtraspecial_of_mulEquiv e, timmesfeldIsExtraspecial_of_mulEquiv e.symm⟩

theorem timmesfeldIsExtraspecial_iff (P : Type*) [Group P] :
    CFSG.Open.timmesfeldIsExtraspecial P ↔ CFSG.IsExtraspecialPGroup 2 P :=
  ⟨fun h => ⟨h.1, h.2.1.trans h.2.2.1, h.2.2.1, h.2.2.2⟩,
    fun h => ⟨h.1, h.2.1.trans h.2.2.1.symm, h.2.2.1, h.2.2.2⟩⟩

theorem timmesfeldFitting_map (e : H ≃* K) :
    (CFSG.Open.timmesfeldFitting H).map e.toMonoidHom = CFSG.Open.timmesfeldFitting K := by
  simp only [CFSG.Open.timmesfeldFitting.eq_sSup]
  refine map_sSup_setOf e fun N => ?_
  rw [normal_map_iff]
  exact and_congr_right fun _ => (Group.isNilpotent_congr (mapEquiv e N)).symm

theorem timmesfeldLayer_map (e : H ≃* K) :
    (CFSG.Open.timmesfeldLayer H).map e.toMonoidHom = CFSG.Open.timmesfeldLayer K := by
  simp only [CFSG.Open.timmesfeldLayer.eq_sSup]
  exact map_sSup_setOf e fun L => CFSG.ComponentClassification.LocalComponents.equiv_iff e L

theorem timmesfeldFStar_map (e : H ≃* K) :
    (CFSG.Open.timmesfeldFStar H).map e.toMonoidHom = CFSG.Open.timmesfeldFStar K := by
  simp only [CFSG.Open.timmesfeldFStar.eq_sup]
  rw [Subgroup.map_sup, timmesfeldFitting_map, timmesfeldLayer_map]

theorem timmesfeldOddCore_map (e : H ≃* K) :
    (CFSG.Open.timmesfeldOddCore H).map e.toMonoidHom = CFSG.Open.timmesfeldOddCore K := by
  unfold CFSG.Open.timmesfeldOddCore
  refine map_sSup_setOf e fun N => ?_
  rw [normal_map_iff, card_map_of_injective e.injective]

theorem pCore_eq_sSup (p : ℕ) (H : Type*) [Group H] :
    CFSG.Open.pCore p H = sSup {N : Subgroup H | N.Normal ∧ IsPGroup p N} :=
  rfl

theorem pCore_map_mulEquiv (p : ℕ) (e : H ≃* K) :
    (CFSG.Open.pCore p H).map e.toMonoidHom = CFSG.Open.pCore p K := by
  rw [pCore_eq_sSup, pCore_eq_sSup]
  refine map_sSup_setOf e fun N => ?_
  rw [normal_map_iff]
  exact and_congr_right fun _ =>
    ⟨fun h => h.of_equiv (mapEquiv e N).symm, fun h => h.of_equiv (mapEquiv e N)⟩

theorem map_map_subtype (e : H ≃* K) (R : Subgroup H) (X : Subgroup R) :
    (X.map (mapEquiv e R).toMonoidHom).map (R.map e.toMonoidHom).subtype =
      (X.map R.subtype).map e.toMonoidHom := by
  rw [map_map, map_map]
  rfl

theorem pCoreOf_map (p : ℕ) (e : H ≃* K) (R : Subgroup H) :
    CFSG.Open.pCoreOf p (R.map e.toMonoidHom) = (CFSG.Open.pCoreOf p R).map e.toMonoidHom := by
  unfold CFSG.Open.pCoreOf
  rw [← pCore_map_mulEquiv p (mapEquiv e R), map_map_subtype]

theorem map_subtype_frattini_map (e : H ≃* K) (P : Subgroup H) :
    (frattini (P.map e.toMonoidHom)).map (P.map e.toMonoidHom).subtype =
      ((frattini P).map P.subtype).map e.toMonoidHom := by
  rw [← frattini_map_mulEquiv (mapEquiv e P), map_map_subtype]

theorem normal_subgroupOf_map (e : H ≃* K) {R C : Subgroup H} (hRC : R ≤ C)
    (h : (R.subgroupOf C).Normal) :
    ((R.map e.toMonoidHom).subgroupOf (C.map e.toMonoidHom)).Normal := by
  rw [normal_subgroupOf_iff (map_mono hRC)]
  rw [normal_subgroupOf_iff hRC] at h
  rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
  exact ⟨y * x * y⁻¹, h x y hx hy, by simp⟩

theorem quotientIso_congr_right {A X X' : Type*} [Group A] [Group X] [Group X']
    {N : Subgroup A} (h : CFSG.Open.timmesfeldQuotientIso N X) (f : X ≃* X') :
    CFSG.Open.timmesfeldQuotientIso N X' := by
  obtain ⟨φ, hφ, hker⟩ := h
  refine ⟨f.toMonoidHom.comp φ, f.surjective.comp hφ, ?_⟩
  rw [← hker]
  ext x
  simp [MonoidHom.mem_ker]

theorem quotientIso_map {A A' X : Type*} [Group A] [Group A'] [Group X] {N : Subgroup A}
    (h : CFSG.Open.timmesfeldQuotientIso N X) (e : A ≃* A') :
    CFSG.Open.timmesfeldQuotientIso (N.map e.toMonoidHom) X := by
  obtain ⟨φ, hφ, hker⟩ := h
  refine ⟨φ.comp e.symm.toMonoidHom, hφ.comp e.symm.surjective, ?_⟩
  rw [← hker]
  ext x
  simp [MonoidHom.mem_ker]

theorem quotientIso_iff {A X : Type*} [Group A] [Group X] (N : Subgroup A) [N.Normal] :
    CFSG.Open.timmesfeldQuotientIso N X ↔ Nonempty (A ⧸ N ≃* X) := by
  constructor
  · rintro ⟨φ, hφ, hker⟩
    exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hφ)⟩
  · rintro ⟨f⟩
    refine ⟨f.toMonoidHom.comp (QuotientGroup.mk' N),
      f.surjective.comp (QuotientGroup.mk'_surjective N), ?_⟩
    ext x
    simp

end CFSG.LargeExtraspecial.Bridge
