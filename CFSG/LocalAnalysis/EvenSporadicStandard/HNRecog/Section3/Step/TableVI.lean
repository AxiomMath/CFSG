module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Five.GammaCount
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Five.Sylow
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.HSide.HData
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.HSide.SetsVI
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.HSide.Orders
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.HSide.ShapeCongr
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.StructGz
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Vert

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

private lemma orderOf_eq_of_isConj {G : Type} [Group G] {x y : G} (h : IsConj x y) :
    orderOf y = orderOf x := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  rw [← hc]
  simpa [MulAut.conj_apply] using MulEquiv.orderOf_eq (MulAut.conj c) x

private theorem tableVI_at (hI : TwoHSInterface) (hS : SuborbitFacts) {G : Type} [Group G] [Finite G]
    {a z b : G} (h : IsF5Type a z) (hb : b ∈ orb2B a z a)
    (hF1b : Fusion1Facts b z) (hF2b : Fusion2Facts b z) (hPicb : A8Pictures b z)
    (h3 : Fusion3Facts a z) :
    Nat.card ↥(tBase a z b) = 5774 ∧
    IsOrbitPartition (Gxy a b) (tBase a z b) (tSet a z b) ∧
    StabCard (Gxy a b) (tSet a z b) ![384, 1024, 48, 64, 32, 240, 20, 16] ∧
    (∀ c ∈ tSet a z b 2, IsShapeD8TimesS3 ↥(Gxyz a b c)) ∧
    (∀ c ∈ tSet a z b 4, IsShapeTwoTwoTimesD8 ↥(Gxyz a b c)) ∧
    (∀ c ∈ tSet a z b 5, IsNonsplitDoubleCoverOfS5 ↥(Gxyz a b c)) ∧
    (∀ c ∈ tSet a z b 6, IsShapeZ2TimesD10 ↥(Gxyz a b c)) ∧
    (∀ c ∈ tSet a z b 7, IsShapeZ2TimesD8 ↥(Gxyz a b c)) ∧
    (∀ c ∈ tSet a z b 6, padicValNat 2 (Nat.card ↥(Gxy a c)) = 2) := by
  have hbF : IsF5Type b z := isF5Type_of_isConj h hb.1 (IsConj.refl z)
  obtain ⟨E, z₀, b₀, u₀, hE, L, hD⟩ := exists_hSideData hI hbF hF1b hF2b hPicb
  have ha2 : a ^ 2 = 1 := by rw [← h.orderOf_a]; exact pow_orderOf_eq_one a
  have hb_ord : orderOf b = 2 := (orderOf_eq_of_isConj hb.1).trans h.orderOf_a
  have hb2 : b ^ 2 = 1 := by rw [← hb_ord]; exact pow_orderOf_eq_one b
  have hab_ord : orderOf (a * b) = 2 := (orderOf_eq_of_isConj hb.2).trans h.orderOf_z
  have hab2 : (a * b) ^ 2 = 1 := by rw [← hab_ord]; exact pow_orderOf_eq_one (a * b)
  have hab : a * b = b * a := comm_of_sq_mul ha2 hb2 hab2
  have ha : a ∈ Gx b := mem_Gx.mpr hab.symm
  let y : ↥(Gx b) := ⟨a, ha⟩
  have hy : IsConj (GxSelf b * z₀) y := by
    refine (L.isConj_bz₀_iff y).2 ⟨hb.1.symm, ?_⟩
    change IsConj z (b * a)
    rw [← hab]
    exact hb.2
  have hT : TableVIData (GxSelf b) z₀ b₀ u₀ y :=
    hS.tableVI ↥(Gx b) E hE (GxSelf b) z₀ b₀ u₀ L.facts hD y hy
  have e1 : tBase a z b = (Gx b).subtype '' tab6Base (GxSelf b) z₀ y := tBase_eq L hy
  have e2 : tSet a z b = fun i => (Gx b).subtype '' tab6Set (GxSelf b) z₀ b₀ u₀ y i :=
    funext fun i => tSet_eq L hy i
  have e3 : Gxy a b = (Gx y).map (Gx b).subtype := Gxy_eq_map_subtype y
  have hinj : Function.Injective (Gx b).subtype := Subgroup.subtype_injective _
  have hpart : IsOrbitPartition (Gxy a b) (tBase a z b) (tSet a z b) := by
    rw [e1, e2, e3]
    exact (isOrbitPartition_map_iff hinj _ _ _).2 hT.partition
  have hstab : StabCard (Gxy a b) (tSet a z b) ![384, 1024, 48, 64, 32, 240, 20, 16] := by
    rw [e2, e3]
    exact (stabCard_map_iff hinj _ _ _).2 hT.card_stab
  refine ⟨?_, hpart, hstab, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hK : Nat.card ↥(Gxy a b) = 30720 := card_of_isShapeTwoTwoSixS5 (h3.shape_2B b hb)
    have hlen : ∀ i : Fin 8, Nat.card ↥(tSet a z b i) =
        ![80, 30, 640, 480, 960, 128, 1536, 1920] i := by
      intro i
      have h := hpart.card_mul_eq hstab i
      rw [hK] at h
      fin_cases i <;> norm_num at h ⊢ <;> omega
    rw [hpart.card_eq_sum]
    simp only [hlen]
    rw [Fin.sum_univ_eight]
    norm_num
  · intro c hc
    rw [e2] at hc
    obtain ⟨c', hc', rfl⟩ := hc
    obtain ⟨e⟩ := nonempty_mulEquiv_Gxyz_subtype y c'
    exact IsShapeD8TimesS3.of_mulEquiv e.symm (hT.shape_3A c' hc')
  · intro c hc
    rw [e2] at hc
    obtain ⟨c', hc', rfl⟩ := hc
    obtain ⟨e⟩ := nonempty_mulEquiv_Gxyz_subtype y c'
    exact IsShapeTwoTwoTimesD8.of_mulEquiv e.symm (hT.shape_4B c' hc')
  · intro c hc
    rw [e2] at hc
    obtain ⟨c', hc', rfl⟩ := hc
    obtain ⟨e⟩ := nonempty_mulEquiv_Gxyz_subtype y c'
    exact IsNonsplitDoubleCoverOfS5.of_mulEquiv e.symm (hT.shape_5A c' hc')
  · intro c hc
    rw [e2] at hc
    obtain ⟨c', hc', rfl⟩ := hc
    obtain ⟨e⟩ := nonempty_mulEquiv_Gxyz_subtype y c'
    exact IsShapeZ2TimesD10.of_mulEquiv e.symm (hT.shape_5E c' hc')
  · intro c hc
    rw [e2] at hc
    obtain ⟨c', hc', rfl⟩ := hc
    obtain ⟨e⟩ := nonempty_mulEquiv_Gxyz_subtype y c'
    exact IsShapeZ2TimesD8.of_mulEquiv e.symm (hT.shape_6A c' hc')
  · intro c hc
    have hcG : c ∈ tSet a z b 6 := hc
    rw [e2] at hcG
    obtain ⟨c', _, hceq⟩ := hcG
    have hmem : c ∈ tBase a z b ∧ orderOf (a * c) = 5 ∧
        IsShapeCentralizerFiveB ↥(Gxy b (a * c)) := by
      have h : tSet a z b 6 = {d | d ∈ tBase a z b ∧ orderOf (a * d) = 5 ∧
          IsShapeCentralizerFiveB ↥(Gxy b (a * d))} := rfl
      rwa [h] at hc
    have h5 : orderOf (a * c) = 5 := hmem.2.1
    have hsh : IsShapeCentralizerFiveB ↥(Gxy b (a * c)) := hmem.2.2
    have hcb : c ∈ Gx b := hceq ▸ c'.2
    let ρ : G := a * c
    have hρ : ρ ∈ Gx b := (Gx b).mul_mem ha hcb
    obtain ⟨_, _, _, _, _, hpad⟩ :=
      (five_sylow hI hbF hF1b hF2b).sylow ρ hρ h5 hsh (default : Sylow 2 ↥(Gxy b ρ))
    have hne : Nat.card ↥(Gxy a c) ≠ 0 := by
      haveI : Nonempty ↥(Gxy a c) := ⟨1⟩
      exact (Nat.card_pos (α := ↥(Gxy a c))).ne'
    have hle_sub : Gxy a c ≤ Gx ρ := by
      intro g hg
      rw [mem_Gx]
      have hga : a * g = g * a := mem_Gx.mp (mem_Gxy.mp hg).1
      have hgc : c * g = g * c := mem_Gx.mp (mem_Gxy.mp hg).2
      change (a * c) * g = g * (a * c)
      calc (a * c) * g = a * (c * g) := by rw [mul_assoc]
        _ = a * (g * c) := by rw [hgc]
        _ = (a * g) * c := by rw [mul_assoc]
        _ = (g * a) * c := by rw [hga]
        _ = g * (a * c) := by rw [mul_assoc]
    have hcard_le : padicValNat 2 (Nat.card ↥(Gxy a c)) ≤ 2 := by
      by_contra hcon
      have hlt : 2 < padicValNat 2 (Nat.card ↥(Gxy a c)) := not_le.mp hcon
      have h3dvd : 2 ^ 3 ∣ Nat.card ↥(Gxy a c) :=
        (padicValNat_dvd_iff_le (p := 2) (a := Nat.card ↥(Gxy a c)) (n := 3) hne).2 (by omega)
      have h3dvd' : 2 ^ 3 ∣ Nat.card ↥(Gx ρ) := h3dvd.trans (Subgroup.card_dvd_of_le hle_sub)
      have hneρ : Nat.card ↥(Gx ρ) ≠ 0 := by
        haveI : Nonempty ↥(Gx ρ) := ⟨1⟩
        exact (Nat.card_pos (α := ↥(Gx ρ))).ne'
      have hge3 : 3 ≤ padicValNat 2 (Nat.card ↥(Gx ρ)) :=
        (padicValNat_dvd_iff_le (p := 2) (a := Nat.card ↥(Gx ρ)) (n := 3) hneρ).1 h3dvd'
      omega
    have h20 : Nat.card ↥(Gxy a b ⊓ Gx c) = 20 := by
      have h := hstab 6 c hc
      norm_num at h
      exact h
    have h20dvd : 20 ∣ Nat.card ↥(Gxy a c) := by
      rw [← h20]
      refine Subgroup.card_dvd_of_le ?_
      intro g hg
      exact mem_Gxy.mpr ⟨(mem_Gxy.mp hg.1).1, hg.2⟩
    have hcard_ge : 2 ≤ padicValNat 2 (Nat.card ↥(Gxy a c)) := by
      have h4 : 2 ^ 2 ∣ Nat.card ↥(Gxy a c) :=
        dvd_trans (by norm_num : 2 ^ 2 ∣ 20) h20dvd
      exact (padicValNat_dvd_iff_le (p := 2) (a := Nat.card ↥(Gxy a c)) (n := 2) hne).1 h4
    exact le_antisymm hcard_le hcard_ge

theorem tableVIInput_holds :
    ∀ (hI : TwoHSInterface) (hS : SuborbitFacts) (hM : M11Facts) {G : Type} [Group G] [Finite G]
      {a z : G} (h : IsF5Type a z) (hF1 : Vert Fusion1Facts a z) (hCube : Vert CubeFacts a z)
      (hF2 : Vert Fusion2Facts a z) (hF3 : Vert Fusion3Facts a z) (hPic : Vert A8Pictures a z)
      (hSGz : Vert StructGzFacts a z) (hT3 : Vert TableIIIFacts a z) (hT5 : Vert TableVFacts a z)
      (h4B : Vert FourBFacts a z) (hS7 : Vert S7Facts a z) (h6A : Vert SixAFacts a z),
      TableVIFacts a z := by
  intro hI hS hM G _ _ a z h hF1 hCube hF2 hF3 hPic hSGz hT3 hT5 h4B hS7 h6A
  have h3 : Fusion3Facts a z := hF3.self
  have key : ∀ b ∈ orb2B a z a,
      Nat.card ↥(tBase a z b) = 5774 ∧
      IsOrbitPartition (Gxy a b) (tBase a z b) (tSet a z b) ∧
      StabCard (Gxy a b) (tSet a z b) ![384, 1024, 48, 64, 32, 240, 20, 16] ∧
      (∀ c ∈ tSet a z b 2, IsShapeD8TimesS3 ↥(Gxyz a b c)) ∧
      (∀ c ∈ tSet a z b 4, IsShapeTwoTwoTimesD8 ↥(Gxyz a b c)) ∧
      (∀ c ∈ tSet a z b 5, IsNonsplitDoubleCoverOfS5 ↥(Gxyz a b c)) ∧
      (∀ c ∈ tSet a z b 6, IsShapeZ2TimesD10 ↥(Gxyz a b c)) ∧
      (∀ c ∈ tSet a z b 7, IsShapeZ2TimesD8 ↥(Gxyz a b c)) ∧
      (∀ c ∈ tSet a z b 6, padicValNat 2 (Nat.card ↥(Gxy a c)) = 2) :=
    fun b hb => tableVI_at hI hS h hb (hF1 b z hb.1 (IsConj.refl z))
      (hF2 b z hb.1 (IsConj.refl z)) (hPic b z hb.1 (IsConj.refl z)) h3
  exact ⟨fun b hb => (key b hb).1,
    fun b hb => (key b hb).2.1,
    fun b hb => (key b hb).2.2.1,
    fun b hb => (key b hb).2.2.2.1,
    fun b hb => (key b hb).2.2.2.2.1,
    fun b hb => (key b hb).2.2.2.2.2.1,
    fun b hb => (key b hb).2.2.2.2.2.2.1,
    fun b hb => (key b hb).2.2.2.2.2.2.2.1,
    fun b hb => (key b hb).2.2.2.2.2.2.2.2⟩

end CFSG.EvenSporadicStandard.HNRecog.Section3
