module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Outside.OutGH23Clos
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Outside.OutInvGL32
public import Certificates.Data.GH23Data

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.Outside

open CFSG.OddStandard.SmallF3.HarrisU33.GH23Data

private def pt : Fin 8 → (Fin 3 → ZMod 2) :=
  ![![1, 0, 0], ![0, 1, 0], ![0, 0, 1], ![1, 1, 0], ![0, 1, 1], ![1, 1, 1], ![1, 0, 1],
    ![0, 0, 0]]

private def ptInv (v : Fin 3 → ZMod 2) : Fin 8 :=
  if v 0 = 1 then
    if v 1 = 1 then (if v 2 = 1 then 5 else 3) else if v 2 = 1 then 6 else 0
  else
    if v 1 = 1 then (if v 2 = 1 then 4 else 1) else if v 2 = 1 then 2 else 7

private theorem ptInv_pt : Function.LeftInverse ptInv pt := by decide +kernel

private theorem pt_ptInv : Function.RightInverse ptInv pt := by decide +kernel

private def ptEquiv : Fin 8 ≃ (Fin 3 → ZMod 2) where
  toFun := pt
  invFun := ptInv
  left_inv := ptInv_pt
  right_inv := pt_ptInv

private noncomputable def rho : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2) →*
    Equiv.Perm (Fin 8) :=
  (ptEquiv.symm.permCongrHom).toMonoidHom.comp
    (MulAction.toPermHom (Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) (Fin 3 → ZMod 2))

private theorem rho_injective : Function.Injective rho := by
  haveI hM : FaithfulSMul (Matrix (Fin 3) (Fin 3) (ZMod 2)) (Fin 3 → ZMod 2) :=
    ⟨fun h => Matrix.ext_iff_mulVec.mpr (fun v => by simpa using h v)⟩
  exact (Equiv.permCongrHom ptEquiv.symm).injective.comp MulAction.toPerm_injective

private def A : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![0, 0, 1; 1, 0, 1; 0, 1, 0]

private def B : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![1, 1, 0; 0, 1, 0; 0, 0, 1]

private theorem A_det_ne_zero : A.det ≠ 0 := by decide +kernel

private theorem B_det_ne_zero : B.det ≠ 0 := by decide +kernel

private def a : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero A A_det_ne_zero

private def b : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero B B_det_ne_zero

private theorem code_rho_a : gh23Code (rho a) = 14899409 := by decide +kernel

private theorem code_rho_b : gh23Code (rho b) = 16405144 := by decide +kernel

private theorem gen_mem_range (σ : Equiv.Perm (Fin 8)) (hσ : gh23Code σ ∈ q2gens) :
    σ ∈ rho.range := by
  have hmem : gh23Code σ = 14899409 ∨ gh23Code σ = 16405144 := by
    simpa [q2gens] using hσ
  rcases hmem with h | h
  · have hσ' : σ = rho a := gh23_code_injective (h.trans code_rho_a.symm)
    rw [hσ']
    exact MonoidHom.mem_range.mpr ⟨a, rfl⟩
  · have hσ' : σ = rho b := gh23_code_injective (h.trans code_rho_b.symm)
    rw [hσ']
    exact MonoidHom.mem_range.mpr ⟨b, rfl⟩

private theorem gh23Sub_le_range : gh23Sub q2gens ≤ rho.range := by
  unfold gh23Sub
  exact (Subgroup.closure_le rho.range).mpr (fun σ hσ => gen_mem_range σ hσ)

private theorem card_range : Nat.card rho.range = 168 := by
  have h := Nat.card_congr (MonoidHom.ofInjective rho_injective).toEquiv
  rw [card_GL32] at h
  exact h.symm

private theorem gh23Sub_eq_range (hcard : Nat.card (gh23Sub q2gens) = 168) :
    gh23Sub q2gens = rho.range :=
  Subgroup.eq_of_le_of_card_ge gh23Sub_le_range (by rw [card_range, hcard])

theorem gh23_q2_equiv_GL32 (hcard : Nat.card (gh23Sub q2gens) = 168) :
    Nonempty (↥(gh23Sub q2gens) ≃* Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) :=
  ⟨(MulEquiv.subgroupCongr (gh23Sub_eq_range hcard)).trans
    (MonoidHom.ofInjective rho_injective).symm⟩

end CFSG.OddStandard.SmallF3.HarrisU33.Outside
