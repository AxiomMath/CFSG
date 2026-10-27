module

public import CFSG.LinearAlgebra.DesarguesianPlanes.RootSubgroups

public section

namespace CFSG.DesarguesianPlanes

open Matrix
open scoped commutatorElement

variable {G : Type*} [Group G] {F : Type} [Field F] {Z : Subgroup (GL (Fin 2) F)} [Z.Normal]
  {J : G} (φ : Subgroup.centralizer ({J} : Set G) ≃* GL (Fin 2) F ⧸ Z) (Y : G)

structure BrauerRootRelations : Prop where
  commutes_X₁_X₂_one : Commutes (rootSub φ Y 0 1) (rootSub φ Y 2 1)
  commutes_X₁_X₂_two : Commutes (rootSub φ Y 0 1) (rootSub φ Y 0 2)
  commIn_X₂_one_X₂_two : CommIn (rootSub φ Y 2 1) (rootSub φ Y 0 2) (rootSub φ Y 0 1)
  nonTriv_X₂_one_X₂_two : NonTriv (rootSub φ Y 2 1) (rootSub φ Y 0 2)

variable {φ Y}

section Transport

variable (hZ : Z ≤ CFSG.Assembly.LowTwoRank.StatedScalars (Fin 2) F)
  (hZodd : Odd (Nat.card Z)) (h2 : (2 : F) ≠ 0) (hJ : orderOf J = 2)
  (hY₁ : Y⁻¹ * J * Y = invJ₁ φ) (hY₂ : Y⁻¹ * invJ₁ φ * Y = invJ₂ φ)

include hZ hZodd h2 hJ hY₁ hY₂

theorem commutes_succ {i j k l : Fin 3} (h : Commutes (rootSub φ Y i j) (rootSub φ Y k l)) :
    Commutes (rootSub φ Y (i + 1) (j + 1)) (rootSub φ Y (k + 1) (l + 1)) := by
  rw [← rootSub_map_inv_Y φ hZ hZodd h2 hJ hY₁ hY₂, ← rootSub_map_inv_Y φ hZ hZodd h2 hJ hY₁ hY₂]
  exact h.map _

theorem commIn_succ {i j k l m n : Fin 3}
    (h : CommIn (rootSub φ Y i j) (rootSub φ Y k l) (rootSub φ Y m n)) :
    CommIn (rootSub φ Y (i + 1) (j + 1)) (rootSub φ Y (k + 1) (l + 1))
      (rootSub φ Y (m + 1) (n + 1)) := by
  rw [← rootSub_map_inv_Y φ hZ hZodd h2 hJ hY₁ hY₂, ← rootSub_map_inv_Y φ hZ hZodd h2 hJ hY₁ hY₂,
    ← rootSub_map_inv_Y φ hZ hZodd h2 hJ hY₁ hY₂]
  exact h.map _

theorem nonTriv_succ {i j k l : Fin 3} (h : NonTriv (rootSub φ Y i j) (rootSub φ Y k l)) :
    NonTriv (rootSub φ Y (i + 1) (j + 1)) (rootSub φ Y (k + 1) (l + 1)) := by
  rw [← rootSub_map_inv_Y φ hZ hZodd h2 hJ hY₁ hY₂, ← rootSub_map_inv_Y φ hZ hZodd h2 hJ hY₁ hY₂]
  exact h.map _

theorem commIn_swap {i j k l m n : Fin 3}
    (h : CommIn (rootSub φ Y i j) (rootSub φ Y k l) (rootSub φ Y m n)) :
    CommIn (rootSub φ Y (swap01 i) (swap01 j)) (rootSub φ Y (swap01 k) (swap01 l))
      (rootSub φ Y (swap01 m) (swap01 n)) := by
  rw [← rootSub_map_W φ hZ hZodd h2 hJ hY₁ hY₂, ← rootSub_map_W φ hZ hZodd h2 hJ hY₁ hY₂,
    ← rootSub_map_W φ hZ hZodd h2 hJ hY₁ hY₂]
  exact h.map _

theorem nonTriv_swap {i j k l : Fin 3} (h : NonTriv (rootSub φ Y i j) (rootSub φ Y k l)) :
    NonTriv (rootSub φ Y (swap01 i) (swap01 j)) (rootSub φ Y (swap01 k) (swap01 l)) := by
  rw [← rootSub_map_W φ hZ hZodd h2 hJ hY₁ hY₂, ← rootSub_map_W φ hZ hZodd h2 hJ hY₁ hY₂]
  exact h.map _


variable (hR : BrauerRootRelations φ Y)
include hR

theorem BrauerRootRelations.commutes_12_02 : Commutes (rootSub φ Y 1 2) (rootSub φ Y 0 2) := by
  simpa using commutes_succ hZ hZodd h2 hJ hY₁ hY₂ hR.commutes_X₁_X₂_one

theorem BrauerRootRelations.commutes_20_10 : Commutes (rootSub φ Y 2 0) (rootSub φ Y 1 0) := by
  simpa using commutes_succ hZ hZodd h2 hJ hY₁ hY₂ (hR.commutes_12_02 hZ hZodd h2 hJ hY₁ hY₂)

theorem BrauerRootRelations.commutes_12_10 : Commutes (rootSub φ Y 1 2) (rootSub φ Y 1 0) := by
  simpa using commutes_succ hZ hZodd h2 hJ hY₁ hY₂ hR.commutes_X₁_X₂_two

theorem BrauerRootRelations.commutes_20_21 : Commutes (rootSub φ Y 2 0) (rootSub φ Y 2 1) := by
  simpa using commutes_succ hZ hZodd h2 hJ hY₁ hY₂ (hR.commutes_12_10 hZ hZodd h2 hJ hY₁ hY₂)

theorem BrauerRootRelations.commIn_02_10_12 :
    CommIn (rootSub φ Y 0 2) (rootSub φ Y 1 0) (rootSub φ Y 1 2) := by
  simpa using commIn_succ hZ hZodd h2 hJ hY₁ hY₂ hR.commIn_X₂_one_X₂_two

theorem BrauerRootRelations.commIn_10_21_20 :
    CommIn (rootSub φ Y 1 0) (rootSub φ Y 2 1) (rootSub φ Y 2 0) := by
  simpa using commIn_succ hZ hZodd h2 hJ hY₁ hY₂ (hR.commIn_02_10_12 hZ hZodd h2 hJ hY₁ hY₂)

theorem BrauerRootRelations.commIn_20_12_10 :
    CommIn (rootSub φ Y 2 0) (rootSub φ Y 1 2) (rootSub φ Y 1 0) := by
  simpa [swap01] using commIn_swap hZ hZodd h2 hJ hY₁ hY₂ hR.commIn_X₂_one_X₂_two

theorem BrauerRootRelations.commIn_12_01_02 :
    CommIn (rootSub φ Y 1 2) (rootSub φ Y 0 1) (rootSub φ Y 0 2) := by
  simpa [swap01] using
    commIn_swap hZ hZodd h2 hJ hY₁ hY₂ (hR.commIn_02_10_12 hZ hZodd h2 hJ hY₁ hY₂)

theorem BrauerRootRelations.commIn_01_20_21 :
    CommIn (rootSub φ Y 0 1) (rootSub φ Y 2 0) (rootSub φ Y 2 1) := by
  simpa [swap01] using
    commIn_swap hZ hZodd h2 hJ hY₁ hY₂ (hR.commIn_10_21_20 hZ hZodd h2 hJ hY₁ hY₂)

theorem BrauerRootRelations.nonTriv_02_10 : NonTriv (rootSub φ Y 0 2) (rootSub φ Y 1 0) := by
  simpa using nonTriv_succ hZ hZodd h2 hJ hY₁ hY₂ hR.nonTriv_X₂_one_X₂_two

theorem BrauerRootRelations.nonTriv_10_21 : NonTriv (rootSub φ Y 1 0) (rootSub φ Y 2 1) := by
  simpa using nonTriv_succ hZ hZodd h2 hJ hY₁ hY₂ (hR.nonTriv_02_10 hZ hZodd h2 hJ hY₁ hY₂)

theorem BrauerRootRelations.nonTriv_12_01 : NonTriv (rootSub φ Y 1 2) (rootSub φ Y 0 1) := by
  simpa [swap01] using nonTriv_swap hZ hZodd h2 hJ hY₁ hY₂ (hR.nonTriv_02_10 hZ hZodd h2 hJ hY₁ hY₂)

theorem BrauerRootRelations.nonTriv_01_20 : NonTriv (rootSub φ Y 0 1) (rootSub φ Y 2 0) := by
  simpa [swap01] using nonTriv_swap hZ hZodd h2 hJ hY₁ hY₂ (hR.nonTriv_10_21 hZ hZodd h2 hJ hY₁ hY₂)

end Transport

end CFSG.DesarguesianPlanes
