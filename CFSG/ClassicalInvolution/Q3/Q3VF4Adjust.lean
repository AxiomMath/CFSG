module

public import CFSG.ClassicalInvolution.Q3.Q3TWWEvalB
public import CFSG.ClassicalInvolution.Q3.Q3VF4Ext
public import CFSG.ClassicalInvolution.Q3.Q3ZAdjChain
public import CFSG.ClassicalInvolution.WeakCT.Main
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Contragredient
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ProjectiveSemilinear

public section

namespace CFSG.ClassicalInvolution.Q3.Q3V

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.ClassicalInvolution.Q3.Q3Z CFSG.ClassicalInvolution.Q3.Q3TW
open CFSG.ClassicalInvolution.WeakCT (blockSL)
open scoped MatrixGroups

section Adjust

variable {G : Type} [Group G]

local notation "bA0" => (blockSL (ZMod 3) 3 2 0 (by omega) : SL(2, ZMod 3) →* SL(3, ZMod 3))
local notation "bA1" => (blockSL (ZMod 3) 3 2 1 (by omega) : SL(2, ZMod 3) →* SL(3, ZMod 3))
local notation "sB" =>
  (shortBlock (ZMod 3) (zero_ne_one : (0 : Fin 2) ≠ 1) : SL(2, ZMod 3) →* StatedSp 2 (ZMod 3))
local notation "lB2" => (longBlock (ZMod 3) 2 1 : SL(2, ZMod 3) →* StatedSp 2 (ZMod 3))

theorem exists_adjustA_b3 (V0 V1 V2 : Subgroup G)
    (hcomm : ∀ a ∈ V0, ∀ b ∈ V2, a * b = b * a)
    (hC : ∀ k : Fin 24, gluingComplete k = false → ∀ g : Fin 12 → G,
      RelsHold g (b3aWords k) → ∀ i, g i = 1)
    (θA : SL(3, ZMod 3) →* G) (hθA : Function.Injective θA)
    (hA0 : (bA0).range.map θA = V0) (hA1 : (bA1).range.map θA = V1)
    (θB : StatedSp 2 (ZMod 3) →* G) (hιL : Function.Injective (θB.comp lB2))
    (hB1 : (lB2).range.map θB = V1) (hB2 : (sB).range.map θB = V2) :
    ∃ θA' : SL(3, ZMod 3) →* G, (∀ A, θA' (bA1 A) = θB (lB2 A)) ∧
      Function.Injective (θA'.comp bA0) ∧ (bA0).range.map θA' = V0 := by
  have hb0inj : Function.Injective bA0 :=
    CFSG.ClassicalInvolution.WeakCT.blockSL_injective (K := ZMod 3) (m := 3) (k := 2) (i := 0)
      (by omega)
  have hb1inj : Function.Injective bA1 :=
    CFSG.ClassicalInvolution.WeakCT.blockSL_injective (K := ZMod 3) (m := 3) (k := 2) (i := 1)
      (by omega)
  have hιA : Function.Injective (θA.comp bA1) := hθA.comp hb1inj
  have hrA : (θA.comp bA1).range = V1 := by rw [MonoidHom.range_comp]; exact hA1
  have hrB : (θB.comp lB2).range = V1 := by rw [MonoidHom.range_comp]; exact hB1
  obtain ⟨α, hα⟩ := exists_mulEquiv_of_range_eq hιA hιL (hrA.trans hrB.symm)
  have hα' : ∀ a, θA (bA1 (α a)) = θB (lB2 a) := hα
  have hrelA : RelsHold (fun j => θA (a2Mat j)) a2Words := relsHold_hom θA a2_relsHold
  have hrelC : RelsHold (fun j => θB (c2Mat j)) c2Words := relsHold_hom θB c2_relsHold
  rcases aut_dichotomy_unip α with ⟨h₁, h₂⟩ | ⟨k, hk, ha, hb⟩
  ·
    obtain ⟨β, hβ1, hβB⟩ := exists_extend_unip_one α h₁ h₂
    refine ⟨θA.comp β.toMonoidHom, fun A => ?_, ?_, ?_⟩
    · exact (congrArg θA (hβ1 A)).trans (hα' A)
    · intro x y h
      exact hb0inj (β.injective (hθA h))
    · rw [← Subgroup.map_map]
      have hβB' : (bA0).range.map β.toMonoidHom = (bA0).range := hβB
      rw [hβB']
      exact hA0
  ·
    exfalso
    have m0p : θA (a2Mat 0) ∈ V0 := by
      rw [a2Mat_zero, ← hA0]
      exact mem_map_range θA _ xpS
    have m0m : θA (a2Mat 1) ∈ V0 := by
      rw [a2Mat_one, ← hA0]
      exact mem_map_range θA _ xmS
    have m5 : θB (c2Mat 5) ∈ V2 := by
      rw [c2Mat_five, ← hB2]
      exact mem_map_range θB _ xpS
    have m6 : θB (c2Mat 6) ∈ V2 := by
      rw [c2Mat_six, ← hB2]
      exact mem_map_range θB _ xmS
    have hp : gOfB (fun j => θA (a2Mat j)) (fun j => θB (c2Mat j)) xPlus =
        (θA.comp bA1) autXp := by
      show θA (a2Mat 4) = θA (bA1 autXp)
      rw [a2Mat_four, adj_autXp_eq]
    have hm : gOfB (fun j => θA (a2Mat j)) (fun j => θB (c2Mat j)) xMinus =
        (θA.comp bA1) autXm := by
      show θA (a2Mat 5) = θA (bA1 autXm)
      rw [a2Mat_five, adj_autXm_eq]
    have hga : evalW (gOfB (fun j => θA (a2Mat j)) (fun j => θB (c2Mat j))) (gluingA k) =
        θB (c2Mat 2) := by
      rw [evalW_gluingA_map (θA.comp bA1) _ hp hm k, ← ha]
      show θA (bA1 (α autXp)) = θB (c2Mat 2)
      rw [hα' autXp, c2Mat_two, adj_autXp_eq]
    have hgb : evalW (gOfB (fun j => θA (a2Mat j)) (fun j => θB (c2Mat j))) (gluingB k) =
        θB (c2Mat 3) := by
      rw [evalW_gluingB_map (θA.comp bA1) _ hp hm k, ← hb]
      show θA (bA1 (α autXm)) = θB (c2Mat 3)
      rw [hα' autXm, c2Mat_three, adj_autXm_eq]
    have hrels : RelsHold (gOfB (fun j => θA (a2Mat j)) (fun j => θB (c2Mat j))) (b3aWords k) :=
      relsHold_b3Glued _ _ hrelA hrelC (gluingA k) (gluingB k) hga hgb (hcomm _ m0p _ m5)
        (hcomm _ m0p _ m6) (hcomm _ m0m _ m5) (hcomm _ m0m _ m6)
    have h9 := hC k hk _ hrels 9
    have h9' : θA (bA1 xpS) = θA (bA1 1) := by
      have e : gOfB (fun j => θA (a2Mat j)) (fun j => θB (c2Mat j)) 9 = θA (bA1 xpS) := by
        show θA (a2Mat 4) = _
        rw [a2Mat_four]
      rw [e] at h9
      rw [h9, map_one, map_one]
    exact adj_xpS_ne_one (hιA (a₁ := xpS) (a₂ := 1) h9')

end Adjust

end CFSG.ClassicalInvolution.Q3.Q3V
