module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.TableVIIProof.FiveAInv
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.HSide.HData
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.HSide.SetsVI
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Vert

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G] {a z : G}

theorem tableVII_hSideData (h : IsF5Type a z) (hF1 : Vert Fusion1Facts a z)
    (hF2 : Vert Fusion2Facts a z) (hPic : Vert A8Pictures a z) (hT5 : TableVFacts a z) {t : G}
    (ht : IsConj a t) : HSideData t z := by
  have hnc : ¬ IsConj a z := by
    intro hac
    obtain ⟨c, hc⟩ := (hT5.partition.orbit 0).nonempty
    have hc' : c ∈ orb2A a a := hc
    exact Set.disjoint_left.mp (hT5.partition.disjoint 0 1 (by decide)) hc
      ⟨hc'.1, hac.symm.trans hc'.2⟩
  have htF : IsF5Type t z := isF5Type_of_isConj h ht (IsConj.refl z)
  obtain ⟨E, hE⟩ := htF.cent_a
  obtain ⟨z₀, b₀, u₀, hF, hz₀, hbz₀, -⟩ := (hF1 t z ht (IsConj.refl z)).rep_z
  obtain ⟨⟨hb, hbb, -, -⟩, ⟨hu, hbu, -⟩⟩ :=
    (hF2 t z ht (IsConj.refl z)).reps_bu z₀ b₀ u₀ hF hz₀
  have hL : HLab t z z₀ b₀ u₀ :=
    ⟨hF, fun htz => hnc (ht.trans htz), hz₀, hbz₀, hb, hbb, hu, hbu⟩
  exact ⟨E, z₀, b₀, u₀, hE, hL, a8Dict_of_pictures (hPic t z ht (IsConj.refl z)) hL⟩

theorem tableVII_exists_tOne (h5 : TableVIIFiveAInv) (h : IsF5Type a z)
    (hF1 : Vert Fusion1Facts a z) (hF2 : Vert Fusion2Facts a z) (hPic : Vert A8Pictures a z)
    (hT5 : TableVFacts a z) {c t : G} (ht : t ∈ orb2B a z a) (hc : c ∈ tSet a z t 5) :
    ∃ t₁ ∈ Gxyz a t c, IsConj a t₁ ∧ t₁ ≠ t := by
  obtain ⟨E, z₀, b₀, u₀, hE, L, hD⟩ := tableVII_hSideData h hF1 hF2 hPic hT5 ht.1
  have hc5 : c ∈ tBase a z t ∧ orderOf (a * c) = 5 ∧
      IsShapeCentralizerFiveC ↥(Gxy t (a * c)) := hc
  have hcBase : c ∈ tBase a z t := hc5.1
  have hca : IsConj a c := hcBase.1
  have hcz : IsConj z (t * c) := hcBase.2.1
  have ha2 : a ^ 2 = 1 := by rw [← h.orderOf_a]; exact pow_orderOf_eq_one a
  have hz2 : z ^ 2 = 1 := by rw [← h.orderOf_z]; exact pow_orderOf_eq_one z
  have htGx : t ∈ Gx a :=
    mem_Gx_of_isConj_mul (x := a) (y := z) (b := a) (c := t) ha2 hz2 (IsConj.refl a) ht.1
      (Or.inr ht.2)
  have hat : a * t = t * a := mem_Gx.1 htGx
  have haGx : a ∈ Gx t := by rw [mem_Gx]; exact hat.symm
  have hcGx : c ∈ Gx t :=
    mem_Gx_of_isConj_mul (x := a) (y := z) (b := t) (c := c) ha2 hz2 ht.1 hca (Or.inr hcz)
  let y : ↥(Gx t) := ⟨a, haGx⟩
  let c' : ↥(Gx t) := ⟨c, hcGx⟩
  have hy : IsConj (GxSelf t * z₀) y := by
    refine (L.isConj_bz₀_iff y).2 ⟨ht.1.symm, ?_⟩
    rw [← hat]
    exact ht.2
  have hc_mem : c ∈ Subtype.val '' tab6Set (GxSelf t) z₀ b₀ u₀ y 5 := by
    rw [← tSet_eq L hy 5]
    exact hc
  obtain ⟨c'', hc'', hc''val⟩ := hc_mem
  have hc''eq : c'' = c' := Subtype.ext hc''val
  have hc''mem : c' ∈ tab6Set (GxSelf t) z₀ b₀ u₀ y 5 := hc''eq ▸ hc''
  obtain ⟨s, hs, hsb₀⟩ :=
    h5 ↥(Gx t) E hE (GxSelf t) z₀ b₀ u₀ L.facts hD y hy c' hc''mem
  have hb0 := (L.isConj_b₀_iff s).1 hsb₀
  have hs1 : s ∈ Gx y := (Subgroup.mem_inf.mp hs).1
  have hs2 : s ∈ Gx c' := (Subgroup.mem_inf.mp hs).2
  have ht1_a : (s : G) ∈ Gx a := by
    rw [mem_Gx]
    have h := congrArg (fun z : ↥(Gx t) => (z : G)) (mem_Gx.1 hs1)
    simpa using h
  have ht1_c : (s : G) ∈ Gx c := by
    rw [mem_Gx]
    have h := congrArg (fun z : ↥(Gx t) => (z : G)) (mem_Gx.1 hs2)
    simpa using h
  have ht2 : orderOf t = 2 := by
    rw [← h.orderOf_a]
    obtain ⟨g, hg⟩ := isConj_iff.1 ht.1
    rw [← hg]
    simpa [MulAut.conj_apply] using (MulEquiv.orderOf_eq (MulAut.conj g) a)
  have ht_sq : t * t = 1 := by
    have hp := pow_orderOf_eq_one t
    rw [ht2] at hp
    simpa [pow_two] using hp
  refine ⟨(s : G), ?_, ht.1.trans hb0.1, ?_⟩
  · rw [mem_Gxyz]
    exact ⟨ht1_a, s.2, ht1_c⟩
  · intro hEq
    have h1 : t * (s : G) = 1 := by rw [hEq]; exact ht_sq
    have htne : t ≠ 1 := by
      intro hone
      rw [hone, orderOf_one] at ht2
      exact (by decide : (1 : ℕ) ≠ 2) ht2
    exact htne (isConj_one_left.mp (h1 ▸ hb0.2))

end CFSG.EvenSporadicStandard.HNRecog.Section3
