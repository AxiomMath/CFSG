module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.SplitBGroup
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.SplitBMatGen
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.SplitBTransport
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.SplitBCent
public import Certificates.Certificate24856
public import Certificates.Certificate24858
public import Certificates.Certificate24859

public section

namespace CFSG.EvenSporadicStandard.M24Std

open SplitB Matrix

variable {G : Type} [Group G]

theorem splitDataB_of_type
    {L B : Subgroup G} (h : OctadType L B) : SplitDataB L B := by
  intro z W hzW hz2 hzB hzH hzU hBW hcentW hsq hHW hphi hphiS hker
  have hcentL := cent_of_octadType h
  obtain ⟨hBL, e, he⟩ := h
  obtain ⟨-, hinj, hadd, hmem, hsurj⟩ := Certificates.certificate24856
  have hlet := Certificates.certificate24858
  obtain ⟨hrel, hdual⟩ := Certificates.certificate24859
  have hE : SplitHyp B W z (fun c => iotaE e (ebasis4 fB c)) := by
    refine ⟨hzW, hz2, hzB, hzU, hBW, hcentW, hsq, hphi, hphiS, hker, ?_, ?_, ?_, ?_⟩
    · intro c d
      show iotaE e (ebasis4 fB (c + d)) = iotaE e (ebasis4 fB c) * iotaE e (ebasis4 fB d)
      rw [← hadd, map_mul]
    · intro c d hcd
      exact hinj c d (iotaE_injective e hcd)
    · intro c
      exact (iotaE_mem_B_iff he _).2 (hmem c)
    · intro u hu
      obtain ⟨y, rfl⟩ := exists_iotaE_eq e (hBL hu)
      obtain ⟨c, hc⟩ := hsurj y ((iotaE_mem_B_iff he y).1 hu)
      exact ⟨c, show iotaE e (ebasis4 fB c) = iotaE e y by rw [hc]⟩
  refine exists_split hE (H := egNL L B) (g := fun k => iotaE e (tvEl k)) (A := Atv)
    (fun x hx u hu => (Subgroup.mem_normalizer_iff.1 (Subgroup.mem_inf.1 hx).1 u).1 hu)
    hHW hzH (fun k => iotaE_mem_egNL hBL he (hlet k).1)
    (fun x hx hxc => hcentL x (Subgroup.mem_inf.1 hx).2 hxc) exists_word_of_mul_eq_one ?_
    (words := sbWordsF) hrel (Psi := sbPsi) (Cm := sbCm) hdual
  intro k c
  show iotaE e (tvEl k) * iotaE e (ebasis4 fB c) * (iotaE e (tvEl k))⁻¹ =
    iotaE e (ebasis4 fB (c ᵥ* Atv k))
  rw [← map_inv, ← map_mul, ← map_mul, (hlet k).2 c]

end CFSG.EvenSporadicStandard.M24Std
