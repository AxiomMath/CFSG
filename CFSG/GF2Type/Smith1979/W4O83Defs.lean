module

public import CFSG.Open.TimmesfeldLargeExtraspecialMilestoneDefs
public import CFSG.LargeExtraspecial.Setting

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.W4O83

open Subgroup Module QuadraticMap CFSG.LargeExtraspecial CFSG.Open

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem q_apply_O (x : S.O) (v : S.Qt) : S.q ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) v) = S.q v :=
  TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp x.2 v

theorem polar_apply_O (x : S.O) (u v : S.Qt) :
    polar S.q ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) u) ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) v) = polar S.q u v := by
  simp only [polar, ← map_add, q_apply_O]

structure Omega83Pre {G : Type} [Group G] [Finite G] (S : Setting G) where
  plane : Fin 4 → Submodule (ZMod 2) S.Qt
  theta : Fin 4 → S.O
  iSup_plane : ⨆ i, plane i = ⊤
  finrank_plane : ∀ i, finrank (ZMod 2) (plane i) = 2
  polar_eq_zero : ∀ i j, i ≠ j → ∀ u ∈ plane i, ∀ v ∈ plane j, polar S.q u v = 0
  q_eq_one : ∀ i, ∀ v ∈ plane i, v ≠ 0 → S.q v = 1
  theta_mem_Mbar : ∀ i, theta i ∈ S.Mbar
  theta_pow_three : ∀ i, theta i ^ 3 = 1
  apply_theta_of_ne : ∀ i j, i ≠ j → ∀ v ∈ plane j, (theta i : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v
  apply_theta_mem : ∀ i, ∀ v ∈ plane i, (theta i : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ plane i
  eq_zero_of_apply_theta : ∀ i, ∀ v ∈ plane i,
    (theta i : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v → v = 0

structure Omega83Config {G : Type} [Group G] [Finite G] (S : Setting G) extends Omega83Pre S where
  theta_mem_oddCore : ∀ i, theta i ∈ (timmesfeldOddCore S.Mbar).map S.Mbar.subtype

namespace Omega83Pre

variable {G : Type} [Group G] [Finite G] {S : Setting G} (C : Omega83Pre S)

@[expose] def th (i : Fin 4) : S.Qt ≃ₗ[ZMod 2] S.Qt := (C.theta i : S.O)

theorem th_th_th (i : Fin 4) (v : S.Qt) : C.th i (C.th i (C.th i v)) = v := by
  have h := congrArg (fun x : S.O => ((x : S.Qt ≃ₗ[ZMod 2] S.Qt)) v) (C.theta_pow_three i)
  simpa [pow_succ, th] using h

theorem th_mem_plane {i : Fin 4} {v : S.Qt} (hv : v ∈ C.plane i) : C.th i v ∈ C.plane i :=
  C.apply_theta_mem i v hv

theorem th_eq_of_ne {i j : Fin 4} (hij : i ≠ j) {v : S.Qt} (hv : v ∈ C.plane j) :
    C.th i v = v :=
  C.apply_theta_of_ne i j hij v hv

theorem eq_zero_of_th_eq {i : Fin 4} {v : S.Qt} (hv : v ∈ C.plane i) (h : C.th i v = v) :
    v = 0 :=
  C.eq_zero_of_apply_theta i v hv h

theorem q_th (i : Fin 4) (v : S.Qt) : S.q (C.th i v) = S.q v :=
  q_apply_O (C.theta i) v

end Omega83Pre

end CFSG.GF2Type.Smith1979.W4O83
