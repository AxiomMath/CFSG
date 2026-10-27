module

public import CFSG.ClassicalInvolution.Q3.TL4MF163L3X
public import CFSG.ClassicalInvolution.Q3.TL4MF163L3Y

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4.L3

open CFSG CFSG.ClassicalInvolution Matrix
open CFSG.ClassicalInvolution.Q3.TA3 CFSG.ClassicalInvolution.Q3.TA3.Q5L3 CFSG.ClassicalInvolution.Q3.TA3.Q5GL2
open CFSG.ClassicalInvolution.Q3.TL4.MF163 CFSG.ClassicalInvolution.Q3.TL4.MF163.L3
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.GH74.GLS.IVK.Proofs2
open scoped MatrixGroups

variable {A : Type} [Group A]

structure L3Frame (T : Subgroup A) (z : A) (K : Type) [Field K] [Finite K]
    (e : ↥T ≃* projectiveSL 3 K) where
  Q : GL (Fin 3) K
  π : (⊤ : Subgroup (GL (Fin 2) K)) →* A
  hrange : π.range = T ⊓ Subgroup.centralizer ({z} : Set A)
  hk : CubeKer π
  hπ1 : π ⟨-1, Subgroup.mem_top _⟩ = z
  hπN : ∀ B, π B ∈ T
  hπ : ∀ B, π B = ((e.symm (proj 3 K (blkP Q B)) : T) : A)

namespace L3Frame

variable {T : Subgroup A} {z : A} {K : Type} [Field K] [Finite K] {e : ↥T ≃* projectiveSL 3 K}
  (F : L3Frame T z K e)

@[expose] noncomputable def e' : ↥T ≃* projectiveSL 3 K := e.trans (conjAut 3 K F.Q)⁻¹

theorem e'_π (B : (⊤ : Subgroup (GL (Fin 2) K))) :
    F.e' ⟨F.π B, F.hπN B⟩ = proj 3 K (blkP 1 (B : GL (Fin 2) K)) := by
  have h1 : (⟨F.π B, F.hπN B⟩ : T) = e.symm (proj 3 K (blkP F.Q B)) := Subtype.ext (F.hπ B)
  show (conjAut 3 K F.Q)⁻¹ (e ⟨F.π B, F.hπN B⟩) = _
  rw [h1, MulEquiv.apply_symm_apply, conjAut_inv_proj_blkP]

@[expose] noncomputable def ι [T.Normal] : A →* MulAut (projectiveSL 3 K) :=
  (MulAut.congr F.e').toMonoidHom.comp (MulAut.conjNormal (H := T))

theorem ι_apply [T.Normal] (x : A) : F.ι x = MulAut.congr F.e' (MulAut.conjNormal x) := rfl

theorem ι_π [T.Normal] (B : (⊤ : Subgroup (GL (Fin 2) K))) :
    F.ι (F.π B) = MulAut.conj (proj 3 K (blkP 1 (B : GL (Fin 2) K))) := by
  rw [ι_apply, congr_conjNormal_of_mem F.e' (F.hπN B), e'_π]

theorem ι_injective [T.Normal] (hC : Subgroup.centralizer (T : Set A) = ⊥) :
    Function.Injective F.ι :=
  congr_conjNormal_injective hC F.e'

theorem fix [T.Normal] {r : A}
    (hr : r ∈ Subgroup.centralizer (((slPart (⊤ : Subgroup (GL (Fin 2) K))).map F.π : Subgroup A) :
      Set A)) (B : SL(2, K)) :
    F.ι r (proj 3 K ((blkP 1).comp SpecialLinearGroup.toGL B)) =
      proj 3 K ((blkP 1).comp SpecialLinearGroup.toGL B) := by
  let C : (⊤ : Subgroup (GL (Fin 2) K)) := ⟨SpecialLinearGroup.toGL B, Subgroup.mem_top _⟩
  have hAJ : F.π C ∈ (slPart (⊤ : Subgroup (GL (Fin 2) K))).map F.π :=
    ⟨C, mem_slPart.mpr (SpecialLinearGroup.coeToGL_det B), rfl⟩
  have hcomm : F.π C * r = r * F.π C := Subgroup.mem_centralizer_iff.mp hr _ hAJ
  show F.ι r (proj 3 K (blkP 1 (C : GL (Fin 2) K))) = proj 3 K (blkP 1 (C : GL (Fin 2) K))
  rw [← e'_π F C, ι_apply]
  rw [show MulAut.congr F.e' (MulAut.conjNormal r) (F.e' ⟨F.π C, F.hπN C⟩) =
    F.e' (MulAut.conjNormal r ⟨F.π C, F.hπN C⟩) by simp [MulAut.congr_apply]]
  congr 1
  apply Subtype.ext
  rw [MulAut.conjNormal_apply, ← hcomm, mul_inv_cancel_right]

end L3Frame

theorem exists_l3Frame (T : Subgroup A) {z : A} {K : Type} [Field K] [Finite K]
    (hodd : Odd (Nat.card K)) (e : ↥T ≃* projectiveSL 3 K) (hzT : z ∈ T) (hz : orderOf z = 2) :
    Nonempty (L3Frame T z K e) := by
  obtain ⟨Q, π, hrange, hk, hπ1, hπ⟩ := exists_frame hodd e hzT hz
  exact ⟨⟨Q, π, hrange, hk, hπ1, fun B => by rw [hπ B]; exact (e.symm _).2, hπ⟩⟩

end CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4.L3
