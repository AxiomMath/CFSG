module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion1.Qz
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.HSide.XTransA
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.HSide.XTransB
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.HSide.XAt
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.StructGz
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Vert

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

private theorem Gxy_mul_comm_eq {G : Type} [Group G] {q z : G} (hqz : q * z = z * q) :
    Gxy (q * z) z = Gxy q z := by
  ext g
  simp only [mem_Gxy, mem_Gx]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    have h3 : q * g * z = g * q * z :=
      calc q * g * z = q * (g * z) := mul_assoc _ _ _
        _ = q * (z * g) := by rw [h2]
        _ = q * z * g := (mul_assoc _ _ _).symm
        _ = g * (q * z) := h1
        _ = g * q * z := (mul_assoc _ _ _).symm
    exact mul_right_cancel h3
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    calc q * z * g = q * (z * g) := mul_assoc _ _ _
      _ = q * (g * z) := by rw [h2]
      _ = q * g * z := (mul_assoc _ _ _).symm
      _ = g * q * z := by rw [h1]
      _ = g * (q * z) := mul_assoc _ _ _

theorem structXInput_holds :
    ∀ (hI : TwoHSInterface) (hS : SuborbitFacts) {G : Type} [Group G] [Finite G] {a z : G}
      (h : IsF5Type a z) (hF1 : Vert Fusion1Facts a z) (hF2 : Vert Fusion2Facts a z)
      (hF3 : Vert Fusion3Facts a z) (hPic : Vert A8Pictures a z) (hOrb : Vert GzOrbitFacts a z)
      (hY4a : Vert Y4aFacts a z) (hSGz : Vert StructGzFacts a z),
      StructXFacts a z := by
  intro hI hS G _ _ a z h hF1 hF2 hF3 hPic hOrb hY4a hSGz
  refine ⟨fun q hqQ hqA => ?_⟩
  have hOrb' : GzOrbitFacts a z := hOrb a z (IsConj.refl a) (IsConj.refl z)
  have hz2 : z ^ 2 = 1 := by
    have := h.orderOf_z
    rw [← this]
    exact pow_orderOf_eq_one z
  have hqord : orderOf q = 2 := by
    obtain ⟨c, rfl⟩ := isConj_iff.1 hqA
    rw [← h.orderOf_a]
    exact (congrArg orderOf (MulAut.conj_apply c a)).symm.trans
      (MulEquiv.orderOf_eq (MulAut.conj c) a)
  have hqz' : IsConj q (q * z) :=
    isConj_mul_of_mem_Qz h.cent_z h.orderOf_z hqord
      (fun hqz => not_isConj_of_isF5Type hI h (hqz ▸ hqA)) hqQ
  have hqz : IsConj a (q * z) := hqA.trans hqz'
  have hqzQ : q * z ∈ Qz z := (Qz z).mul_mem hqQ (self_mem_Qz hz2)
  have hqGz : q ∈ Gx z := (Subgroup.map_subtype_le (CFSG.pCore 2 ↥(Gx z))) hqQ
  have hzq : z ∈ Gx q := by
    rw [mem_Gx] at hqGz ⊢
    exact hqGz.symm
  obtain ⟨x, b₀, u₀, hx, hT, h1, h2, hR⟩ :=
    exists_tableX_at hI hS (isF5Type_of_isConj h hqA (IsConj.refl z)) (hF1 q z hqA (IsConj.refl z))
      (hF2 q z hqA (IsConj.refl z)) (hPic q z hqA (IsConj.refl z)) hqA hzq hqz'
  have hzp : z ∈ Gx (q * z) := by
    rw [mem_Gx] at hzq ⊢
    rw [← mul_assoc, ← hzq, mul_assoc]
  have hpz : IsConj (q * z) (q * z * z) := by
    have : q * z * z = q := by
      rw [mul_assoc]
      have : z * z = 1 := by rw [← pow_two]; exact hz2
      rw [this, mul_one]
    rw [this]
    exact hqz.symm.trans hqA
  obtain ⟨x', b₀', u₀', hx', hT', -, -, -⟩ :=
    exists_tableX_at hI hS (isF5Type_of_isConj h hqz (IsConj.refl z))
      (hF1 (q * z) z hqz (IsConj.refl z)) (hF2 (q * z) z hqz (IsConj.refl z))
      (hPic (q * z) z hqz (IsConj.refl z)) hqz hzp hpz
  have hK' := pCore_K_eq_of_tableX hx' hT'
  have hGxy : Gxy (q * z) z = Gxy q z := Gxy_mul_comm_eq (mem_Gx.1 hzq)
  rw [hGxy] at hK'
  have hshape : IsShapeTwoTwoSixS5 ↥(Gxy q z) := by
    have := hOrb'.shape_QA q hqQ hqA
    rwa [Gxy_comm] at this
  exact
    { shape := hshape
      pCore := hR
      pCore_derived := ⟨pCore_derived_of_tableX hx hT hR, pCore_K_eq_of_tableX hx hT, hK'⟩
      shape_O2 := shape_O2_of_tableX hx hT
      center := center_of_tableX hx hT
      o1 := o1_of_tableX hx hT h1
      o1_mem := o1_mem_of_tableX hx hT h1 hR
      o1_cards := o1_cards_of_tableX hx hT h1 hR
      three_cent := three_cent_of_tableX hx hT h1 hR
      o2 := o2_of_tableX hx hT h2
      o2_cards := o2_cards_of_tableX hx hT h2 hR }

end CFSG.EvenSporadicStandard.HNRecog.Section3
