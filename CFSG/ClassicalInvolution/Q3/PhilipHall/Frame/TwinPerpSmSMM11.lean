module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpSmSMBase
public import CFSG.CGT.PushingUpLit.SolKNA.R4.SmallQ3Models
public import Certificates.Certificate397508

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.Small.SM

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3.TA3 CFSG.GH74.KGroups
  CFSG.CGT.PushingUpLit.SolKNA.R4

set_option linter.unusedSectionVars false


theorem leaf_m11 {n : ℕ} :
    TwinLeafS n SmallM11 :=
  TwinLeafS.of_no fun Y _ _ R S t h _ hF => by
    haveI := h.core.simple
    haveI := genFittingFStar_normal Y
    obtain ⟨M, -, hA⟩ := M11.autModel hF
    obtain ⟨f, hf⟩ := embedsAut_of_autModel M Y (genFittingFStar Y) ⟨MulEquiv.refl _⟩
      (Nobq.centralizer_genFittingFStar_eq_bot h.core.nonab)
    exact false_of_nqCheck_top h (ι := M11.Q.originalSubgroup.subtype) Subtype.val_injective
      (L := elemsT M11.Q)
      (fun m => by
        rw [mem_elemsT M11.Q M11.Q_ok m]
        exact ⟨fun hm => ⟨⟨m, hm⟩, rfl⟩, fun ⟨y, hy⟩ => hy ▸ y.2⟩)
      Certificates.certificate397508.1
      (f := (MulEquiv.subgroupCongr hA).toMonoidHom.comp f)
      (fun x y hxy => hf ((MulEquiv.subgroupCongr hA).injective hxy))

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.Small.SM
