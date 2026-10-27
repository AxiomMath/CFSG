module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ShultSporLocalZCHSVDefs
public import CFSG.Sporadic.Recognition.HSPinned

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal

open CFSG.Blueprint CFSG.Sporadic.Recognition.HSPinned CFSG.Sporadic.Recognition.HSPinned.Native

theorem toPermHom_hsGenA :
    MulAction.toPermHom JHS (Fin 100) hsGenA = hsVa := by
  refine Equiv.ext fun i => Fin.ext ?_
  have h := genA_smul_vtx i
  have hlt : vtxA[i.val]! < 100 := h ▸ (hsGenA • i).isLt
  show (hsGenA • i).val = vtxA[i.val]! % 100
  rw [h, Nat.mod_eq_of_lt hlt]

theorem toPermHom_hsGenB :
    MulAction.toPermHom JHS (Fin 100) hsGenB = hsVb := by
  refine Equiv.ext fun i => Fin.ext ?_
  have h := genB_smul_vtx i
  have hlt : vtxB[i.val]! < 100 := h ▸ (hsGenB • i).isLt
  show (hsGenB • i).val = vtxB[i.val]! % 100
  rw [h, Nat.mod_eq_of_lt hlt]

theorem hsPerm_eq_comp :
    hsPerm = (MulAction.toPermHom JHS (Fin 100)).comp (hsEquivJ : NativeSporadic.HS →* JHS) :=
  MonoidHom.ext fun _ => Equiv.ext fun _ => rfl

theorem hsPerm_range_eq :
    hsPerm.range = Subgroup.closure ({hsVa, hsVb} : Set (Equiv.Perm (Fin 100))) := by
  rw [hsPerm_eq_comp, MonoidHom.range_comp,
    MonoidHom.range_eq_top.2 (hsEquivJ : NativeSporadic.HS ≃* JHS).surjective,
    ← CFSG.Sporadic.SmallF2.closure_ab, MonoidHom.map_closure, Set.image_pair]
  exact congrArg Subgroup.closure (by rw [toPermHom_hsGenA, toPermHom_hsGenB])

noncomputable def closureHsVEquiv :
    ↥(Subgroup.closure ({hsVa, hsVb} : Set (Equiv.Perm (Fin 100)))) ≃* NativeSporadic.HS :=
  (MulEquiv.subgroupCongr hsPerm_range_eq.symm).trans (MonoidHom.ofInjective hsPerm_injective).symm

theorem card_closure_hsV :
    Nat.card ↥(Subgroup.closure ({hsVa, hsVb} : Set (Equiv.Perm (Fin 100)))) = 44352000 := by
  rw [← hsPerm_range_eq]
  exact card_hsPerm_range

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal
