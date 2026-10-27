module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.SmallQ3CheckSound
public import CFSG.CGT.PushingUpLit.SolKNA.R4.SmallQ3Models
public import CFSG.GH74.KGroups.U33
public import Certificates.Certificate9754

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG.GH74.KGroups

theorem u33_noQ16 :
    NoQ16 ↥U33.QA.originalSubgroup :=
  noQ16_of_noQ16Check (ι := U33.QA.originalSubgroup.subtype) Subtype.val_injective
    (L := elemsT U33.QA)
    (fun m => by
      rw [mem_elemsT U33.QA U33.QA_ok m]
      exact ⟨fun hm => ⟨⟨m, hm⟩, rfl⟩, fun ⟨y, hy⟩ => hy ▸ y.2⟩)
    Certificates.certificate9754

theorem smallLeafR_u33
    {r : ℕ} (hr : 4 ≤ r) :
    SmallLeafR r fun F _ => CFSG.Blueprint.LieModel F .PSU 3 3 1 :=
  smallLeafR_of_noQ16 hr fun F _ hF => by
    obtain ⟨e⟩ := U33.equiv_of_lieModel hF
    obtain ⟨M, -, hA⟩ := U33.autModel e
    exact ⟨↥M.A, inferInstance, embedsAut_of_autModel M, by rw [hA]; exact u33_noQ16⟩

end CFSG.CGT.PushingUpLit.SolKNA.R4
