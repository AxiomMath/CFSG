module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.SmallQ3CheckSound
public import CFSG.CGT.PushingUpLit.SolKNA.R4.SmallQ3Models
public import Certificates.Certificate9756
public import CFSG.GH74.Generic.S45.LEvSporM12Spec

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG.GH74.KGroups CFSG.Sporadic.Schreier CFSG.ComponentClassification.M12Cover
open CFSG.ClassicalInvolution.Q3.TA3

theorem m12_noQ16 :
    NoQ16 ↥autModel :=
  noQ16_of_noQ16Check (ι := autModel.subtype) Subtype.val_injective
    (L := elemsT m12D ++ (elemsT m12D).map (fun d => m12Sigma * d))
    (fun m => by
      rw [List.mem_append, List.mem_map, mem_elemsT m12D m12D_check.1 m]
      constructor
      · rintro (hm | ⟨d, hd', rfl⟩)
        · exact ⟨⟨m, mem_autModel.2 (Or.inl hm)⟩, rfl⟩
        · refine ⟨⟨m12Sigma * d, mem_autModel.2 (Or.inr ?_)⟩, rfl⟩
          rw [← mul_assoc, CFSG.ComponentClassification.M12Cover.sigma_mul_self, one_mul]
          exact (mem_elemsT m12D m12D_check.1 d).1 hd'
      · rintro ⟨⟨y, hy⟩, rfl⟩
        rcases mem_autModel.1 hy with hy' | hy'
        · exact Or.inl hy'
        · exact Or.inr ⟨m12Sigma * y, (mem_elemsT m12D m12D_check.1 _).2 hy',
            by rw [← mul_assoc, CFSG.ComponentClassification.M12Cover.sigma_mul_self, one_mul]
               rfl⟩)
    Certificates.certificate9756

theorem smallLeafR_m12
    {r : ℕ} (hr : 4 ≤ r) : SmallLeafR r SmallM12 :=
  smallLeafR_of_noQ16 hr fun F _ hF => by
    obtain ⟨e⟩ := hF
    exact ⟨↥autModel, inferInstance,
      embedsAut_of_exactModel GH74.Generic.S45.EvSpor.m12_smallAutModel (e.trans m12EquivD),
      m12_noQ16⟩

end CFSG.CGT.PushingUpLit.SolKNA.R4
