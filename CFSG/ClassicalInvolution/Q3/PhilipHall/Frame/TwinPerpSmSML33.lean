module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpSmSMBase
public import CFSG.CGT.PushingUpLit.SolKNA.R4.SmallQ3Models
public import CFSG.GH74.KGroups.L33
public import Certificates.Certificate397508

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.Small.SM

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3.TA3 CFSG.GH74.KGroups
  CFSG.CGT.PushingUpLit.SolKNA.R4

set_option linter.unusedSectionVars false


theorem leaf_l33 {n : ℕ} :
    TwinLeafS n fun F _ => CFSG.Blueprint.LieModel F .PSL 3 3 1 :=
  TwinLeafS.of_no fun Y _ _ R S t h _ hF => by
    haveI := h.core.simple
    haveI := genFittingFStar_normal Y
    obtain ⟨e⟩ := L33.equiv_of_lieModel hF
    obtain ⟨M, -, hA⟩ := L33.autModel e
    obtain ⟨f, hf⟩ := embedsAut_of_autModel M Y (genFittingFStar Y) ⟨MulEquiv.refl _⟩
      (Nobq.centralizer_genFittingFStar_eq_bot h.core.nonab)
    exact false_of_nqCheck_top h (ι := L33.QA.originalSubgroup.subtype) Subtype.val_injective
      (L := elemsT L33.QA)
      (fun m => by
        rw [mem_elemsT L33.QA L33.QA_ok m]
        exact ⟨fun hm => ⟨⟨m, hm⟩, rfl⟩, fun ⟨y, hy⟩ => hy ▸ y.2⟩)
      Certificates.certificate397508.2.1
      (f := (MulEquiv.subgroupCongr hA).toMonoidHom.comp f)
      (fun x y hxy => hf ((MulEquiv.subgroupCongr hA).injective hxy))

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.Small.SM
