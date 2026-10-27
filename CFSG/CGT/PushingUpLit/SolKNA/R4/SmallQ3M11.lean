module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.SmallQ3CheckSound
public import CFSG.CGT.PushingUpLit.SolKNA.R4.SmallQ3Models
public import CFSG.GH74.KGroups.M11
public import Certificates.Certificate9752

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG.GH74.KGroups CFSG.ClassicalInvolution.Q3.TA3

theorem m11_noQ16 :
    NoQ16 ↥M11.Q.originalSubgroup :=
  noQ16_of_noQ16Check (ι := M11.Q.originalSubgroup.subtype) Subtype.val_injective
    (L := elemsT M11.Q)
    (fun m => by
      rw [mem_elemsT M11.Q M11.Q_ok m]
      exact ⟨fun hm => ⟨⟨m, hm⟩, rfl⟩, fun ⟨y, hy⟩ => hy ▸ y.2⟩)
    Certificates.certificate9752

theorem smallLeafR_m11 {r : ℕ}
    (hr : 4 ≤ r) : SmallLeafR r SmallM11 :=
  smallLeafR_of_noQ16 hr fun F _ hF => by
    obtain ⟨M, -, hA⟩ := M11.autModel hF
    exact ⟨↥M.A, inferInstance, embedsAut_of_autModel M, by rw [hA]; exact m11_noQ16⟩

end CFSG.CGT.PushingUpLit.SolKNA.R4
