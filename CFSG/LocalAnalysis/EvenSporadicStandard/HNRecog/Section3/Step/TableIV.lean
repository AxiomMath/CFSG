module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Five.GammaCount
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.HSide.HData
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.HSide.SetsIV
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.HSide.S8Apply
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.HSide.Orders
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.HSide.ShapeCongr
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.StructGz
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Vert

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

private theorem tableIV_at (hI : TwoHSInterface) (hS : SuborbitFacts) {G : Type} [Group G]
    [Finite G] {a z : G} (h : IsF5Type a z) (hF1 : Vert Fusion1Facts a z)
    (hF2 : Vert Fusion2Facts a z) (hF3 : Vert Fusion3Facts a z)
    (hPic : Vert A8Pictures a z) {b : G} (hb : b ∈ orb2A a a) :
    Nat.card ↥(sBase a b) = 2198 ∧
      IsOrbitPartition (Gxy a b) (sBase a b) (sSet a z b) ∧
      StabCard (Gxy a b) (sSet a z b) ![768, 768, 1440, 64, 240, 240] ∧
      (∀ c ∈ sSet a z b 2, IsShapeZ2TimesSym 6 ↥(Gxyz a b c)) ∧
      (∀ c ∈ sSet a z b 4, IsShapeZ2TimesSym 5 ↥(Gxyz a b c)) ∧
      (∀ c ∈ sSet a z b 5, IsShapeZ2TimesSym 5 ↥(Gxyz a b c)) ∧
      (∀ c ∈ sSet a z b 2, Nonempty (↥(derivedOf (Gxy a b) ⊔ Subgroup.zpowers c) ≃* Sym 8)) := by
  have h3 : Fusion3Facts a z := hF3.self
  have hbF : IsF5Type b z := isF5Type_of_isConj h hb.1 (IsConj.refl z)
  have hF1b : Fusion1Facts b z := hF1 b z hb.1 (IsConj.refl z)
  have hF2b : Fusion2Facts b z := hF2 b z hb.1 (IsConj.refl z)
  have hPicb : A8Pictures b z := hPic b z hb.1 (IsConj.refl z)
  obtain ⟨E, z₀, b₀, u₀, hE, L, hD⟩ := exists_hSideData hI hbF hF1b hF2b hPicb
  have ha2 : a * a = 1 := by
    have hh := pow_orderOf_eq_one a
    rw [h.orderOf_a] at hh
    simpa [pow_two] using hh
  have hb2 : b * b = 1 := by
    have hbo : orderOf b = 2 := by
      obtain ⟨c, hc⟩ := isConj_iff.1 hb.1
      rw [← hc]
      simpa [MulAut.conj_apply] using
        (MulEquiv.orderOf_eq (MulAut.conj c) a).trans h.orderOf_a
    have hh := pow_orderOf_eq_one b
    rw [hbo] at hh
    simpa [pow_two] using hh
  have hab2 : (a * b) * (a * b) = 1 := by
    have habo : orderOf (a * b) = 2 := by
      obtain ⟨c, hc⟩ := isConj_iff.1 hb.2
      rw [← hc]
      simpa [MulAut.conj_apply] using
        (MulEquiv.orderOf_eq (MulAut.conj c) a).trans h.orderOf_a
    have hh := pow_orderOf_eq_one (a * b)
    rw [habo] at hh
    simpa [pow_two] using hh
  have hcomm : a * b = b * a :=
    comm_of_sq_mul (by simpa [pow_two] using ha2) (by simpa [pow_two] using hb2)
      (by simpa [pow_two] using hab2)
  let y : ↥(Gx b) := ⟨a, mem_Gx.2 hcomm.symm⟩
  have hba : IsConj b (b * a) := by
    rw [← hcomm]
    exact hb.1.symm.trans hb.2
  have hy : IsConj b₀ y := (HLab.isConj_b₀_iff L y).2
    ⟨by simpa using hb.1.symm, by simpa using hba⟩
  have hT : TableIVData (GxSelf b) z₀ b₀ u₀ y :=
    hS.tableIV ↥(Gx b) E hE (GxSelf b) z₀ b₀ u₀ L.facts hD y hy
  have hinj : Function.Injective (Gx b).subtype := (Gx b).subtype_injective
  have e1 : sBase a b = (Gx b).subtype '' tab4Base (GxSelf b) b₀ y := by
    simpa using sBase_eq L hy
  have e2 : sSet a z b =
      fun i => (Gx b).subtype '' tab4Set (GxSelf b) z₀ b₀ u₀ y i :=
    funext fun i => by simpa using sSet_eq L hy i
  have e3 : Gxy a b = (Gx y).map (Gx b).subtype := by
    simpa using Gxy_eq_map_subtype y
  have hpart : IsOrbitPartition (Gxy a b) (sBase a b) (sSet a z b) := by
    rw [e1, e2, e3]
    exact (isOrbitPartition_map_iff (f := (Gx b).subtype) hinj (Gx y)
      (tab4Base (GxSelf b) b₀ y) (tab4Set (GxSelf b) z₀ b₀ u₀ y)).2 hT.partition
  have hstab : StabCard (Gxy a b) (sSet a z b) ![768, 768, 1440, 64, 240, 240] := by
    rw [e2, e3]
    exact (stabCard_map_iff (f := (Gx b).subtype) hinj (Gx y)
      (tab4Set (GxSelf b) z₀ b₀ u₀ y) ![768, 768, 1440, 64, 240, 240]).2 hT.card_stab
  have hshape_4B : ∀ c ∈ sSet a z b 2, IsShapeZ2TimesSym 6 ↥(Gxyz a b c) := by
    intro c hc
    have hc' : c ∈ (Gx b).subtype '' tab4Set (GxSelf b) z₀ b₀ u₀ y 2 := by
      simpa [e2] using hc
    obtain ⟨c', hc', rfl⟩ := hc'
    obtain ⟨e⟩ := nonempty_mulEquiv_Gxyz_subtype y c'
    exact IsShapeZ2TimesSym.of_mulEquiv e.symm (hT.shape_4B c' hc')
  have hshape_3A : ∀ c ∈ sSet a z b 4, IsShapeZ2TimesSym 5 ↥(Gxyz a b c) := by
    intro c hc
    have hc' : c ∈ (Gx b).subtype '' tab4Set (GxSelf b) z₀ b₀ u₀ y 4 := by
      simpa [e2] using hc
    obtain ⟨c', hc', rfl⟩ := hc'
    obtain ⟨e⟩ := nonempty_mulEquiv_Gxyz_subtype y c'
    exact IsShapeZ2TimesSym.of_mulEquiv e.symm (hT.shape_3A c' hc')
  have hshape_6A : ∀ c ∈ sSet a z b 5, IsShapeZ2TimesSym 5 ↥(Gxyz a b c) := by
    intro c hc
    have hc' : c ∈ (Gx b).subtype '' tab4Set (GxSelf b) z₀ b₀ u₀ y 5 := by
      simpa [e2] using hc
    obtain ⟨c', hc', rfl⟩ := hc'
    obtain ⟨e⟩ := nonempty_mulEquiv_Gxyz_subtype y c'
    exact IsShapeZ2TimesSym.of_mulEquiv e.symm (hT.shape_6A c' hc')
  have hs8 : ∀ c ∈ sSet a z b 2,
      Nonempty (↥(derivedOf (Gxy a b) ⊔ Subgroup.zpowers c) ≃* Sym 8) :=
    fun c hc => nonempty_mulEquiv_sym_eight_of_sSet (a := a) L hb (h3.shape_2A b hb) hc
  have hK : Nat.card ↥(Gxy a b) = 80640 := card_of_isShapeTwoTwoTimesA8 (h3.shape_2A b hb)
  have hlen : ∀ i : Fin 6,
      Nat.card ↥(sSet a z b i) * ![768, 768, 1440, 64, 240, 240] i = 80640 := by
    intro i
    have h := hpart.card_mul_eq hstab i
    rw [hK] at h
    exact h
  have h0 : Nat.card ↥(sSet a z b 0) = 105 := by
    have h := hlen 0
    change Nat.card ↥(sSet a z b 0) * 768 = 80640 at h
    omega
  have h1 : Nat.card ↥(sSet a z b 1) = 105 := by
    have h := hlen 1
    change Nat.card ↥(sSet a z b 1) * 768 = 80640 at h
    omega
  have h2 : Nat.card ↥(sSet a z b 2) = 56 := by
    have h := hlen 2
    change Nat.card ↥(sSet a z b 2) * 1440 = 80640 at h
    omega
  have h4 : Nat.card ↥(sSet a z b 3) = 1260 := by
    have h := hlen 3
    change Nat.card ↥(sSet a z b 3) * 64 = 80640 at h
    omega
  have h5 : Nat.card ↥(sSet a z b 4) = 336 := by
    have h := hlen 4
    change Nat.card ↥(sSet a z b 4) * 240 = 80640 at h
    omega
  have h6 : Nat.card ↥(sSet a z b 5) = 336 := by
    have h := hlen 5
    change Nat.card ↥(sSet a z b 5) * 240 = 80640 at h
    omega
  have hcard : Nat.card ↥(sBase a b) = 2198 := by
    rw [hpart.card_eq_sum, Fin.sum_univ_six]
    simp only [h0, h1, h2, h4, h5, h6]
  exact ⟨hcard, hpart, hstab, hshape_4B, hshape_3A, hshape_6A, hs8⟩

theorem tableIVInput_holds :
    ∀ (hI : TwoHSInterface) (hS : SuborbitFacts) {G : Type} [Group G] [Finite G] {a z : G}
      (h : IsF5Type a z) (hF1 : Vert Fusion1Facts a z) (hF2 : Vert Fusion2Facts a z)
      (hF3 : Vert Fusion3Facts a z) (hPic : Vert A8Pictures a z) (hSGz : Vert StructGzFacts a z)
      (hSX : Vert StructXFacts a z) (hT3 : Vert TableIIIFacts a z) (hPar : Vert ParityFacts a z),
      TableIVFacts a z := by
  intro hI hS G _ _ a z h hF1 hF2 hF3 hPic hSGz hSX hT3 hPar
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro b hb
    exact (tableIV_at hI hS h hF1 hF2 hF3 hPic hb).1
  · intro b hb
    exact (tableIV_at hI hS h hF1 hF2 hF3 hPic hb).2.1
  · intro b hb
    exact (tableIV_at hI hS h hF1 hF2 hF3 hPic hb).2.2.1
  · intro b hb c hc
    exact (tableIV_at hI hS h hF1 hF2 hF3 hPic hb).2.2.2.1 c hc
  · intro b hb c hc
    exact (tableIV_at hI hS h hF1 hF2 hF3 hPic hb).2.2.2.2.1 c hc
  · intro b hb c hc
    exact (tableIV_at hI hS h hF1 hF2 hF3 hPic hb).2.2.2.2.2.1 c hc
  · intro b hb c hc
    exact (tableIV_at hI hS h hF1 hF2 hF3 hPic hb).2.2.2.2.2.2 c hc

end CFSG.EvenSporadicStandard.HNRecog.Section3
