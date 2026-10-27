module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.HSide.Map
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.HSide.ShapeCongr
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3Model.TableMaps

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3Model

open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.Section3
open CFSG.EvenSporadicStandard.HNRecog.TwoHSData

variable {H : Type} [Group H]

private theorem isConj_map_iff {G G' : Type} [Group G] [Group G'] (e : G ≃* G') (x y : G) :
    IsConj (e x) (e y) ↔ IsConj x y :=
  ⟨isConj_of_map_mulEquiv e, isConj_map_mulEquiv e⟩

private theorem map_ne_iff {G G' : Type} [Group G] [Group G'] (e : G ≃* G') (x y : G) :
    e x ≠ e y ↔ x ≠ y := by
  simp only [ne_eq, e.injective.eq_iff]

private theorem mem_tab4Base_map {H' : Type} [Group H'] (e : H ≃* H') (a b y x : H) :
    e x ∈ tab4Base (e a) (e b) (e y) ↔ x ∈ tab4Base a b y := by
  simp only [tab4Base, Set.mem_setOf_eq, ← map_mul, isConj_map_iff, map_ne_iff]

private theorem mem_tab6Base_map {H' : Type} [Group H'] (e : H ≃* H') (a z y x : H) :
    e x ∈ tab6Base (e a) (e z) (e y) ↔ x ∈ tab6Base a z y := by
  simp only [tab6Base, Set.mem_setOf_eq, ← map_mul, isConj_map_iff, map_ne_iff]

private theorem isConj_congr_left {b b' : H} (hb : IsConj b b') (c : H) :
    IsConj b' c ↔ IsConj b c :=
  ⟨fun h => hb.trans h, fun h => (isConj_comm.mp hb).trans h⟩

private theorem conj_center {a : H} (ha : a ∈ Subgroup.center H) (g : H) :
    g * a * g⁻¹ = a := by
  rw [Subgroup.mem_center_iff.mp ha g]
  simp

private theorem isConj_mul_center {a : H} (ha : a ∈ Subgroup.center H) {z z' : H}
    (hz : IsConj z z') : IsConj (a * z) (a * z') := by
  rw [isConj_iff] at hz ⊢
  obtain ⟨g, hg⟩ := hz
  refine ⟨g, ?_⟩
  rw [← conj_mul, conj_center ha g, hg]

theorem tab4Base_congr {a b b' : H} (hb : IsConj b b') (y : H) :
    tab4Base a b' y = tab4Base a b y := by
  ext c
  simp only [tab4Base, Set.mem_setOf_eq]
  rw [isConj_congr_left hb c]

theorem tab6Base_congr {a z z' : H} (ha : a ∈ Subgroup.center H) (hz : IsConj z z') (y : H) :
    tab6Base a z' y = tab6Base a z y := by
  ext c
  simp only [tab6Base, Set.mem_setOf_eq]
  rw [isConj_congr_left (isConj_mul_center ha hz) c]

theorem TableIVData.congr {a z z' b b' z₁ z₁' y : H} (ha : a ∈ Subgroup.center H)
    (hz : IsConj z z') (hb : IsConj b b') (hz₁ : IsConj z₁ z₁') (h : TableIVData a z b z₁ y) :
    TableIVData a z' b' z₁' y := by
  have hb' : tab4Base a b' y = tab4Base a b y := tab4Base_congr hb y
  have hs' : tab4Set a z' b' z₁' y = tab4Set a z b z₁ y := tab4Set_congr ha hz hb hz₁ y
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hb', hs']; exact h.partition
  · rw [hs']; exact h.card_stab
  · intro c hc; rw [hs'] at hc; exact h.shape_4B c hc
  · intro c hc; rw [hs'] at hc; exact h.shape_3A c hc
  · intro c hc; rw [hs'] at hc; exact h.shape_6A c hc

theorem TableVIData.congr {a z z' b b' z₁ z₁' y : H} (ha : a ∈ Subgroup.center H)
    (hz : IsConj z z') (hb : IsConj b b') (hz₁ : IsConj z₁ z₁') (h : TableVIData a z b z₁ y) :
    TableVIData a z' b' z₁' y := by
  have hb' : tab6Base a z' y = tab6Base a z y := tab6Base_congr ha hz y
  have hs' : tab6Set a z' b' z₁' y = tab6Set a z b z₁ y := tab6Set_congr ha hz hb hz₁ y
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hb', hs']; exact h.partition
  · rw [hs']; exact h.card_stab
  · intro c hc; rw [hs'] at hc; exact h.shape_3A c hc
  · intro c hc; rw [hs'] at hc; exact h.shape_4B c hc
  · intro c hc; rw [hs'] at hc; exact h.shape_5A c hc
  · intro c hc; rw [hs'] at hc; exact h.shape_5E c hc
  · intro c hc; rw [hs'] at hc; exact h.shape_6A c hc

private theorem image_eq_of_mem_iff {H' : Type} [Group H'] (e : H ≃* H')
    {S : Set H} {T : Set H'} (h : ∀ x, e x ∈ T ↔ x ∈ S) : e.toMonoidHom '' S = T := by
  ext x
  constructor
  · rintro ⟨x0, hx0, rfl⟩
    exact (h x0).mpr hx0
  · intro hx
    exact ⟨e.symm x, (h (e.symm x)).mp (by simpa using hx), e.apply_symm_apply x⟩

theorem TableIVData.of_map {H' : Type} [Group H'] (e : H ≃* H') {a z b z₁ y : H}
    (h : TableIVData (e a) (e z) (e b) (e z₁) (e y)) : TableIVData a z b z₁ y := by
  have hinj : Function.Injective e.toMonoidHom := e.injective
  have hrange : e.toMonoidHom.range = ⊤ := MonoidHom.range_eq_top.mpr e.surjective
  have hGx : (Gx y).map e.toMonoidHom = Gx (e y) := by
    rw [map_Gx_of_injective hinj, hrange, inf_top_eq]
    rfl
  have hbase : e.toMonoidHom '' tab4Base a b y = tab4Base (e a) (e b) (e y) :=
    image_eq_of_mem_iff e fun x => mem_tab4Base_map e a b y x
  have hset : (fun i => e.toMonoidHom '' tab4Set a z b z₁ y i)
      = tab4Set (e a) (e z) (e b) (e z₁) (e y) :=
    funext fun i => image_eq_of_mem_iff e fun x => mem_tab4Set_map e a z b z₁ y x i
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have himg : IsOrbitPartition ((Gx y).map e.toMonoidHom) (e.toMonoidHom '' tab4Base a b y)
        (fun i => e.toMonoidHom '' tab4Set a z b z₁ y i) := by
      rw [hGx, hbase, hset]
      exact h.partition
    exact (isOrbitPartition_map_iff (f := e.toMonoidHom) hinj (Gx y) (tab4Base a b y)
      (tab4Set a z b z₁ y)).1 himg
  · have himg : StabCard ((Gx y).map e.toMonoidHom)
        (fun i => e.toMonoidHom '' tab4Set a z b z₁ y i) ![768, 768, 1440, 64, 240, 240] := by
      rw [hGx, hset]
      exact h.card_stab
    exact (stabCard_map_iff (f := e.toMonoidHom) hinj (Gx y) (tab4Set a z b z₁ y)
      ![768, 768, 1440, 64, 240, 240]).1 himg
  · intro c hc
    have hc' : e c ∈ tab4Set (e a) (e z) (e b) (e z₁) (e y) 2 :=
      (mem_tab4Set_map e a z b z₁ y c 2).mpr hc
    obtain ⟨e'⟩ := nonempty_mulEquiv_inf_Gx_map e y c
    exact IsShapeZ2TimesSym.of_mulEquiv e'.symm (h.shape_4B (e c) hc')
  · intro c hc
    have hc' : e c ∈ tab4Set (e a) (e z) (e b) (e z₁) (e y) 4 :=
      (mem_tab4Set_map e a z b z₁ y c 4).mpr hc
    obtain ⟨e'⟩ := nonempty_mulEquiv_inf_Gx_map e y c
    exact IsShapeZ2TimesSym.of_mulEquiv e'.symm (h.shape_3A (e c) hc')
  · intro c hc
    have hc' : e c ∈ tab4Set (e a) (e z) (e b) (e z₁) (e y) 5 :=
      (mem_tab4Set_map e a z b z₁ y c 5).mpr hc
    obtain ⟨e'⟩ := nonempty_mulEquiv_inf_Gx_map e y c
    exact IsShapeZ2TimesSym.of_mulEquiv e'.symm (h.shape_6A (e c) hc')

theorem TableVIData.of_map {H' : Type} [Group H'] (e : H ≃* H') {a z b z₁ y : H}
    (h : TableVIData (e a) (e z) (e b) (e z₁) (e y)) : TableVIData a z b z₁ y := by
  have hinj : Function.Injective e.toMonoidHom := e.injective
  have hrange : e.toMonoidHom.range = ⊤ := MonoidHom.range_eq_top.mpr e.surjective
  have hGx : (Gx y).map e.toMonoidHom = Gx (e y) := by
    rw [map_Gx_of_injective hinj, hrange, inf_top_eq]
    rfl
  have hbase : e.toMonoidHom '' tab6Base a z y = tab6Base (e a) (e z) (e y) :=
    image_eq_of_mem_iff e fun x => mem_tab6Base_map e a z y x
  have hset : (fun i => e.toMonoidHom '' tab6Set a z b z₁ y i)
      = tab6Set (e a) (e z) (e b) (e z₁) (e y) :=
    funext fun i => image_eq_of_mem_iff e fun x => mem_tab6Set_map e a z b z₁ y x i
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have himg : IsOrbitPartition ((Gx y).map e.toMonoidHom) (e.toMonoidHom '' tab6Base a z y)
        (fun i => e.toMonoidHom '' tab6Set a z b z₁ y i) := by
      rw [hGx, hbase, hset]
      exact h.partition
    exact (isOrbitPartition_map_iff (f := e.toMonoidHom) hinj (Gx y) (tab6Base a z y)
      (tab6Set a z b z₁ y)).1 himg
  · have himg : StabCard ((Gx y).map e.toMonoidHom)
        (fun i => e.toMonoidHom '' tab6Set a z b z₁ y i) ![384, 1024, 48, 64, 32, 240, 20, 16] := by
      rw [hGx, hset]
      exact h.card_stab
    exact (stabCard_map_iff (f := e.toMonoidHom) hinj (Gx y) (tab6Set a z b z₁ y)
      ![384, 1024, 48, 64, 32, 240, 20, 16]).1 himg
  · intro c hc
    have hc' : e c ∈ tab6Set (e a) (e z) (e b) (e z₁) (e y) 2 :=
      (mem_tab6Set_map e a z b z₁ y c 2).mpr hc
    obtain ⟨e'⟩ := nonempty_mulEquiv_inf_Gx_map e y c
    exact IsShapeD8TimesS3.of_mulEquiv e'.symm (h.shape_3A (e c) hc')
  · intro c hc
    have hc' : e c ∈ tab6Set (e a) (e z) (e b) (e z₁) (e y) 4 :=
      (mem_tab6Set_map e a z b z₁ y c 4).mpr hc
    obtain ⟨e'⟩ := nonempty_mulEquiv_inf_Gx_map e y c
    exact IsShapeTwoTwoTimesD8.of_mulEquiv e'.symm (h.shape_4B (e c) hc')
  · intro c hc
    have hc' : e c ∈ tab6Set (e a) (e z) (e b) (e z₁) (e y) 5 :=
      (mem_tab6Set_map e a z b z₁ y c 5).mpr hc
    obtain ⟨e'⟩ := nonempty_mulEquiv_inf_Gx_map e y c
    exact IsNonsplitDoubleCoverOfS5.of_mulEquiv e'.symm (h.shape_5A (e c) hc')
  · intro c hc
    have hc' : e c ∈ tab6Set (e a) (e z) (e b) (e z₁) (e y) 6 :=
      (mem_tab6Set_map e a z b z₁ y c 6).mpr hc
    obtain ⟨e'⟩ := nonempty_mulEquiv_inf_Gx_map e y c
    exact IsShapeZ2TimesD10.of_mulEquiv e'.symm (h.shape_5E (e c) hc')
  · intro c hc
    have hc' : e c ∈ tab6Set (e a) (e z) (e b) (e z₁) (e y) 7 :=
      (mem_tab6Set_map e a z b z₁ y c 7).mpr hc
    obtain ⟨e'⟩ := nonempty_mulEquiv_inf_Gx_map e y c
    exact IsShapeZ2TimesD8.of_mulEquiv e'.symm (h.shape_6A (e c) hc')

end CFSG.EvenSporadicStandard.HNRecog.Section3Model
