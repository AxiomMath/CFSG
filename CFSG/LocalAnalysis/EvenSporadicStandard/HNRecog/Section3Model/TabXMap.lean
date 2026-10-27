module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.HSide.MapShape
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3Model.TableMaps
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3Model.TwoFourAbstract
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.ShapeCongrK

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3Model

open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.Section3
open CFSG.EvenSporadicStandard.HNRecog.TwoHSData

private theorem isConj_map_iff {G G' : Type} [Group G] [Group G'] (e : G ≃* G') (x y : G) :
    IsConj (e x) (e y) ↔ IsConj x y :=
  ⟨isConj_of_map_mulEquiv e, isConj_map_mulEquiv e⟩

private theorem mem_Gx_map {H H' : Type} [Group H] [Group H'] (e : H ≃* H') (z x : H) :
    e x ∈ Gx (e z) ↔ x ∈ Gx z := by
  rw [mem_Gx, mem_Gx, ← map_mul, ← map_mul, e.injective.eq_iff]

private theorem isConj_congr_left {H : Type} [Group H] {b b' : H} (hb : IsConj b b') (c : H) :
    IsConj b' c ↔ IsConj b c :=
  ⟨fun h => hb.trans h, fun h => (isConj_comm.mp hb).trans h⟩

private theorem image_eq_of_mem_iff {H H' : Type} [Group H] [Group H'] (e : H ≃* H')
    {S : Set H} {T : Set H'} (h : ∀ x, e x ∈ T ↔ x ∈ S) : e.toMonoidHom '' S = T := by
  ext x
  constructor
  · rintro ⟨x0, hx0, rfl⟩
    exact (h x0).mpr hx0
  · intro hx
    exact ⟨e.symm x, (h (e.symm x)).mp (by simpa using hx), e.apply_symm_apply x⟩

theorem QuotShape.of_map_equiv {A G : Type} [Group A] [Group G] (e : A ≃* G) {M N : Subgroup A}
    {P : Type*} [Group P] (h : QuotShape (M.map e.toMonoidHom) (N.map e.toMonoidHom) P) :
    QuotShape M N P := by
  have h2 := QuotShape.map (f := e.symm.toMonoidHom) e.symm.injective h
  have hc : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id A := by
    ext x
    simp
  simpa only [Subgroup.map_map, hc, Subgroup.map_id] using h2

variable {H : Type} [Group H]

theorem tabXBase_congr {b b' : H} (hb : IsConj b b') (z : H) :
    {c | IsConj b' c ∧ c ∈ Gx z} = {c | IsConj b c ∧ c ∈ Gx z} := by
  ext c
  simp only [Set.mem_setOf_eq]
  rw [isConj_congr_left hb c]

theorem TableXData.congr {a z b b' z₁ z₁' : H} (ha : a ∈ Subgroup.center H) (hb : IsConj b b')
    (hz₁ : IsConj z₁ z₁') (h : TableXData a z b z₁) : TableXData a z b' z₁' := by
  have hs' : tabXSet a z b' z₁' = tabXSet a z b z₁ := tabXSet_congr ha hb hz₁
  refine
    { shape_K := h.shape_K
      partition := ?_
      card_stab := ?_
      o1_mem := fun c hc => ?_
      o1_card_R := fun c hc => ?_
      o1_card_R_X' := fun c hc => ?_
      o1_card_X' := fun c hc => ?_
      o1_quot := fun c hc => ?_
      o2_not_mem := fun c hc => ?_
      o2_R := fun c hc => ?_
      o2_R_X' := fun c hc => ?_
      o2_card_X' := fun c hc => ?_
      o2_quot := fun c hc => ?_
      quot_derived := h.quot_derived
      relIndex_X'R := h.relIndex_X'R
      K_ne := h.K_ne
      pCore_derived := h.pCore_derived
      center_derived := h.center_derived
      three_centralizer := ?_ }
  · rw [tabXBase_congr hb, hs']
    exact h.partition
  · rw [hs']
    exact h.card_stab
  · rw [hs'] at hc
    exact h.o1_mem c hc
  · rw [hs'] at hc
    exact h.o1_card_R c hc
  · rw [hs'] at hc
    exact h.o1_card_R_X' c hc
  · rw [hs'] at hc
    exact h.o1_card_X' c hc
  · rw [hs'] at hc
    exact h.o1_quot c hc
  · rw [hs'] at hc
    exact h.o2_not_mem c hc
  · rw [hs'] at hc
    exact h.o2_R c hc
  · rw [hs'] at hc
    exact h.o2_R_X' c hc
  · rw [hs'] at hc
    exact h.o2_card_X' c hc
  · rw [hs'] at hc
    exact h.o2_quot c hc
  · intro σ hσ hσo
    obtain ⟨c, hc, h1, h2⟩ := h.three_centralizer σ hσ hσo
    exact ⟨c, by rw [hs']; exact hc, h1, h2⟩

theorem TableXData.of_map {H' : Type} [Group H'] (e : H ≃* H') {a z b z₁ : H}
    (h : TableXData (e a) (e z) (e b) (e z₁)) : TableXData a z b z₁ := by
  have hinj : Function.Injective e.toMonoidHom := e.injective
  have hrange : e.toMonoidHom.range = ⊤ := MonoidHom.range_eq_top.mpr e.surjective
  have hG : ∀ x : H, (Gx x).map e.toMonoidHom = Gx (e x) := fun x => by
    rw [map_Gx_of_injective hinj, hrange, inf_top_eq]
    rfl
  have hR : (CFSG.Open.pCoreOf 2 (Gx z)).map e.toMonoidHom = CFSG.Open.pCoreOf 2 (Gx (e z)) := by
    rw [← hG z]
    exact (pCoreOf_map_of_injective hinj (Gx z)).symm
  have hD : (derivedOf (Gx z)).map e.toMonoidHom = derivedOf (Gx (e z)) := by
    rw [← hG z]
    exact (derivedOf_map_of_injective hinj (Gx z)).symm
  have hZ : (centerOf (derivedOf (Gx z))).map e.toMonoidHom = centerOf (derivedOf (Gx (e z))) := by
    rw [← centerOf_map_of_injective hinj, hD]
  have hS1 : ∀ c : H, (Gx z ⊓ Gx c ⊓ CFSG.Open.pCoreOf 2 (Gx z)).map e.toMonoidHom =
      Gx (e z) ⊓ Gx (e c) ⊓ CFSG.Open.pCoreOf 2 (Gx (e z)) := fun c => by
    rw [Subgroup.map_inf_eq _ _ _ hinj, Subgroup.map_inf_eq _ _ _ hinj, hG z, hG c, hR]
  have hS2 : ∀ c : H,
      (Gx z ⊓ Gx c ⊓ CFSG.Open.pCoreOf 2 (Gx z) ⊓ derivedOf (Gx z)).map e.toMonoidHom =
        Gx (e z) ⊓ Gx (e c) ⊓ CFSG.Open.pCoreOf 2 (Gx (e z)) ⊓ derivedOf (Gx (e z)) :=
    fun c => by rw [Subgroup.map_inf_eq _ _ _ hinj, hS1 c, hD]
  have hS3 : ∀ c : H, (Gx z ⊓ Gx c ⊓ derivedOf (Gx z)).map e.toMonoidHom =
      Gx (e z) ⊓ Gx (e c) ⊓ derivedOf (Gx (e z)) := fun c => by
    rw [Subgroup.map_inf_eq _ _ _ hinj, Subgroup.map_inf_eq _ _ _ hinj, hG z, hG c, hD]
  have hbase : e.toMonoidHom '' {c | IsConj b c ∧ c ∈ Gx z} =
      {c | IsConj (e b) c ∧ c ∈ Gx (e z)} :=
    image_eq_of_mem_iff e fun x => by
      simp only [Set.mem_setOf_eq, isConj_map_iff, mem_Gx_map]
  have hset : (fun i => e.toMonoidHom '' tabXSet a z b z₁ i) =
      tabXSet (e a) (e z) (e b) (e z₁) :=
    funext fun i => image_eq_of_mem_iff e fun x => mem_tabXSet_map e a z b z₁ x i
  have hmem : ∀ (i : Fin 2) (c : H), c ∈ tabXSet a z b z₁ i →
      e c ∈ tabXSet (e a) (e z) (e b) (e z₁) i :=
    fun i c hc => (mem_tabXSet_map e a z b z₁ c i).2 hc
  have hKe : (_root_.commutator H ⊓ Gx z).map e.toMonoidHom =
      _root_.commutator H' ⊓ Gx (e z) := map_K_eq e z
  refine
    { shape_K := ?_
      partition := ?_
      card_stab := ?_
      o1_mem := fun c hc => ?_
      o1_card_R := fun c hc => ?_
      o1_card_R_X' := fun c hc => ?_
      o1_card_X' := fun c hc => ?_
      o1_quot := fun c hc => ?_
      o2_not_mem := fun c hc => ?_
      o2_R := fun c hc => ?_
      o2_R_X' := fun c hc => ?_
      o2_card_X' := fun c hc => ?_
      o2_quot := fun c hc => ?_
      quot_derived := ?_
      relIndex_X'R := ?_
      K_ne := ?_
      pCore_derived := ⟨?_, ?_⟩
      center_derived := ⟨?_, ?_⟩
      three_centralizer := ?_ }
  · have h1 := h.shape_K
    rw [← hKe] at h1
    exact IsShapeK.of_mulEquiv (mapSubgroupMulEquiv e (_root_.commutator H ⊓ Gx z)).symm h1
  · have himg : IsOrbitPartition ((Gx z).map e.toMonoidHom)
        (e.toMonoidHom '' {c | IsConj b c ∧ c ∈ Gx z})
        (fun i => e.toMonoidHom '' tabXSet a z b z₁ i) := by
      rw [hG z, hbase, hset]
      exact h.partition
    exact (isOrbitPartition_map_iff (f := e.toMonoidHom) hinj (Gx z)
      {c | IsConj b c ∧ c ∈ Gx z} (tabXSet a z b z₁)).1 himg
  · have himg : StabCard ((Gx z).map e.toMonoidHom) (fun i => e.toMonoidHom '' tabXSet a z b z₁ i)
        ![768, 384] := by
      rw [hG z, hset]
      exact h.card_stab
    exact (stabCard_map_iff (f := e.toMonoidHom) hinj (Gx z) (tabXSet a z b z₁) ![768, 384]).1 himg
  · have h1 := h.o1_mem (e c) (hmem 0 c hc)
    rw [← hR] at h1
    exact (mem_map_iff e _ c).1 h1
  · have h1 := h.o1_card_R (e c) (hmem 0 c hc)
    rwa [← hS1 c, Subgroup.card_map_of_injective hinj] at h1
  · have h1 := h.o1_card_R_X' (e c) (hmem 0 c hc)
    rwa [← hS2 c, Subgroup.card_map_of_injective hinj] at h1
  · have h1 := h.o1_card_X' (e c) (hmem 0 c hc)
    rwa [← hS3 c, Subgroup.card_map_of_injective hinj] at h1
  · have h1 := h.o1_quot (e c) (hmem 0 c hc)
    rw [← hS3 c, ← hS2 c] at h1
    exact QuotShape.of_map_equiv e h1
  · intro hcR
    apply h.o2_not_mem (e c) (hmem 1 c hc)
    rw [← hR]
    exact (mem_map_iff e _ c).2 hcR
  · have h1 := h.o2_R (e c) (hmem 1 c hc)
    rw [← hS1 c] at h1
    exact isElemTwo_of_map hinj h1
  · have h1 := h.o2_R_X' (e c) (hmem 1 c hc)
    rw [← hS2 c] at h1
    exact isElemTwo_of_map hinj h1
  · have h1 := h.o2_card_X' (e c) (hmem 1 c hc)
    rwa [← hS3 c, Subgroup.card_map_of_injective hinj] at h1
  · have h1 := h.o2_quot (e c) (hmem 1 c hc)
    rw [← hS3 c, ← hS2 c] at h1
    exact QuotShape.of_map_equiv e h1
  · have h1 := h.quot_derived
    rw [← hD, ← hG z] at h1
    exact QuotShape.of_map_equiv e h1
  · have h1 := h.relIndex_X'R
    rw [← hD, ← hR, ← Subgroup.map_sup, ← hG z] at h1
    rwa [Subgroup.relIndex_map_map_of_injective _ _ hinj] at h1
  · intro hK
    apply h.K_ne
    have h1 := congrArg (Subgroup.map e.toMonoidHom) hK
    rwa [hKe, Subgroup.map_sup, hD, hR] at h1
  · apply Subgroup.map_injective hinj
    rw [← pCoreOf_map_of_injective hinj, hD, Subgroup.map_inf_eq _ _ _ hinj, hD, hR]
    exact h.pCore_derived.1
  · apply Subgroup.map_injective hinj
    rw [← pCoreOf_map_of_injective hinj, hKe, Subgroup.map_inf_eq _ _ _ hinj, hD, hR]
    exact h.pCore_derived.2
  · apply Subgroup.map_injective hinj
    rw [← centerOf_map_of_injective hinj, ← centerOf_map_of_injective hinj,
      ← pCoreOf_map_of_injective hinj, hD]
    exact h.center_derived.1
  · obtain ⟨φ⟩ := h.center_derived.2
    exact ⟨((mapSubgroupMulEquiv e (centerOf (derivedOf (Gx z)))).trans
      (MulEquiv.subgroupCongr hZ)).trans φ⟩
  · intro σ hσ hσo
    have hσ' : e σ ∈ Gx (e z) := (mem_Gx_map e z σ).2 hσ
    have hσo' : orderOf (e σ) = 3 := by rw [MulEquiv.orderOf_eq]; exact hσo
    obtain ⟨c', hc', h1, h2⟩ := h.three_centralizer (e σ) hσ' hσo'
    have hc : e.symm c' ∈ tabXSet a z b z₁ 0 := by
      refine (mem_tabXSet_map e a z b z₁ (e.symm c') 0).1 ?_
      rw [MulEquiv.apply_symm_apply]
      exact hc'
    have hcc : e.toMonoidHom (e.symm c') = c' := e.apply_symm_apply c'
    refine ⟨e.symm c', hc, ?_, ?_⟩
    · apply Subgroup.map_injective hinj
      rw [Subgroup.map_inf_eq _ _ _ hinj, hR, hG σ, MonoidHom.map_closure, Set.image_union,
        Set.image_singleton, ← Subgroup.coe_map, hZ, hcc]
      exact h1
    · apply Subgroup.map_injective hinj
      rw [Subgroup.map_inf_eq _ _ _ hinj, Subgroup.map_inf_eq _ _ _ hinj, hD, hR, hG σ, hZ]
      exact h2

end CFSG.EvenSporadicStandard.HNRecog.Section3Model
