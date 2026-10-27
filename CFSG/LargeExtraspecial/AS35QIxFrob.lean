module

public import CFSG.LargeExtraspecial.AS35QIxBasic
public import CFSG.LargeExtraspecial.AS35QIxTr
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.AS35QIx

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
  CFSG.Fischer.Classification.Unitary CFSG.ClassicalGroups.Unitary
open CFSG.Blueprint.Fischer (K)

variable {G : Type} [Group G] [Finite G] {S : Setting G}

namespace IxSetup

variable (T : IxSetup S)

@[expose] noncomputable def frobFun (v : S.Qt) : S.Qt := T.l (fun i => frob (T.hl.inv v i))

theorem frobFun_l (x : Fin 3 → K) : T.frobFun (T.l x) = T.l (fun i => frob (x i)) := by
  rw [frobFun, T.hl.inv_l]

theorem frobFun_add (u v : S.Qt) : T.frobFun (u + v) = T.frobFun u + T.frobFun v := by
  obtain ⟨x, rfl⟩ := T.l_surjective u
  obtain ⟨y, rfl⟩ := T.l_surjective v
  rw [← T.l_add, frobFun_l, frobFun_l, frobFun_l, ← T.l_add]
  congr 1
  funext i
  simp [map_add]

theorem frobFun_frobFun (v : S.Qt) : T.frobFun (T.frobFun v) = v := by
  obtain ⟨x, rfl⟩ := T.l_surjective v
  rw [frobFun_l, frobFun_l]
  congr 1
  funext i
  exact frob_frob (x i)

@[expose] noncomputable def frobLin : S.Qt →ₗ[ZMod 2] S.Qt :=
  (AddMonoidHom.mk' T.frobFun T.frobFun_add).toZModLinearMap 2

@[expose] noncomputable def frobEquiv : S.Qt ≃ₗ[ZMod 2] S.Qt :=
  LinearEquiv.ofInvolutive T.frobLin fun v => T.frobFun_frobFun v

theorem frobEquiv_apply (v : S.Qt) : T.frobEquiv v = T.frobFun v := rfl

theorem q_frobEquiv (v : S.Qt) : S.q (T.frobEquiv v) = S.q v := by
  obtain ⟨x, rfl⟩ := T.l_surjective v
  rw [frobEquiv_apply, frobFun_l, q_l, q_l, herm_self, herm_self]
  simp only [frob_frob]
  congr 2
  ring

@[expose] noncomputable def F : S.O :=
  ⟨T.frobEquiv, TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr T.q_frobEquiv⟩

theorem F_l (x : Fin 3 → K) :
    (T.F : S.Qt ≃ₗ[ZMod 2] S.Qt) (T.l x) = T.l (fun i => frob (x i)) :=
  T.frobFun_l x

theorem F_F (v : S.Qt) :
    (T.F : S.Qt ≃ₗ[ZMod 2] S.Qt) ((T.F : S.Qt ≃ₗ[ZMod 2] S.Qt) v) = v :=
  T.frobFun_frobFun v

theorem F_mul_self : T.F * T.F = 1 :=
  Subtype.ext (LinearEquiv.ext fun v => T.F_F v)

theorem F_inv : T.F⁻¹ = T.F := inv_eq_of_mul_eq_one_right T.F_mul_self

theorem F_zeta (v : S.Qt) : (T.F : S.Qt ≃ₗ[ZMod 2] S.Qt) ((T.ζ : S.Qt ≃ₗ[ZMod 2] S.Qt) v) =
    (T.ζ : S.Qt ≃ₗ[ZMod 2] S.Qt) ((T.ζ : S.Qt ≃ₗ[ZMod 2] S.Qt)
      ((T.F : S.Qt ≃ₗ[ZMod 2] S.Qt) v)) := by
  obtain ⟨x, rfl⟩ := T.l_surjective v
  rw [← T.l_omega, F_l, F_l]
  have e : (fun i => frob ((ω • x) i)) = frob ω • (fun i => frob (x i)) := by
    funext i
    simp [map_mul]
  rw [e, l_smul, AS35QTh.act_frob_omega]
  show _ = T.zL (T.zL _)
  rw [AS35QTh.zeta_zeta T.zeta_sq, add_comm]

theorem F_inv_zeta : T.F * T.ζ * T.F⁻¹ = T.ζ⁻¹ := by
  rw [T.F_inv]
  have e : T.ζ⁻¹ = T.ζ * T.ζ := inv_eq_of_mul_eq_one_right (by rw [← pow_three]; exact T.hζ3)
  rw [e]
  refine Subtype.ext (LinearEquiv.ext fun v => ?_)
  show (T.F : S.Qt ≃ₗ[ZMod 2] S.Qt) ((T.ζ : S.Qt ≃ₗ[ZMod 2] S.Qt)
    ((T.F : S.Qt ≃ₗ[ZMod 2] S.Qt) v)) = _
  rw [F_zeta, F_F]
  rfl

theorem F_not_comm : T.F * T.ζ ≠ T.ζ * T.F := by
  intro h
  apply T.zeta_ne_inv
  rw [← T.F_inv_zeta, h, mul_assoc, mul_inv_cancel, mul_one]

theorem F_comm_beta : T.F * T.β = T.β * T.F := by
  refine Subtype.ext (LinearEquiv.ext fun v => ?_)
  obtain ⟨x, rfl⟩ := T.l_surjective v
  show (T.F : S.Qt ≃ₗ[ZMod 2] S.Qt) ((T.β : S.Qt ≃ₗ[ZMod 2] S.Qt) (T.l x)) =
    (T.β : S.Qt ≃ₗ[ZMod 2] S.Qt) ((T.F : S.Qt ≃ₗ[ZMod 2] S.Qt) (T.l x))
  rw [T.hlβ, F_l, F_l, T.hlβ]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem F_comm_tb : T.F * T.tb = T.tb * T.F := by
  refine Subtype.ext (LinearEquiv.ext fun v => ?_)
  obtain ⟨x, rfl⟩ := T.l_surjective v
  show (T.F : S.Qt ≃ₗ[ZMod 2] S.Qt) ((T.tb : S.Qt ≃ₗ[ZMod 2] S.Qt) (T.l x)) =
    (T.tb : S.Qt ≃ₗ[ZMod 2] S.Qt) ((T.F : S.Qt ≃ₗ[ZMod 2] S.Qt) (T.l x))
  rw [tb_l, F_l, F_l, tb_l]
  congr 1
  funext i
  fin_cases i <;> rfl

end IxSetup

end CFSG.LargeExtraspecial.AS35QIx
