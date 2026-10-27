module

public import CFSG.ClassicalInvolution.Q3.Q3ZAdjChain

public section

namespace CFSG.ClassicalInvolution.Q3.Q3V

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.ClassicalInvolution.Q3.Q3Z
open CFSG.ClassicalInvolution.WeakCT (blockSL)
open scoped MatrixGroups

section Adjust

variable {G : Type} [Group G]

local notation "bA0" => (blockSL (ZMod 3) 3 2 0 (by omega) : SL(2, ZMod 3) →* SL(3, ZMod 3))
local notation "bA1" => (blockSL (ZMod 3) 3 2 1 (by omega) : SL(2, ZMod 3) →* SL(3, ZMod 3))
local notation "sB" =>
  (shortBlock (ZMod 3) (zero_ne_one : (0 : Fin 2) ≠ 1) : SL(2, ZMod 3) →* StatedSp 2 (ZMod 3))
local notation "lB2" => (longBlock (ZMod 3) 2 1 : SL(2, ZMod 3) →* StatedSp 2 (ZMod 3))

theorem exists_adjust_sp3 (V0 V1 V2 : Subgroup G)
    (hcomm : ∀ a ∈ V0, ∀ b ∈ V2, a * b = b * a)
    (hC : ∀ k : Fin 24, gluingComplete k = false → ∀ g : Fin 12 → G,
      RelsHold g (v6aWords k) → ∀ i, g i = 1)
    (θA : SL(3, ZMod 3) →* G) (hιA : Function.Injective (θA.comp bA1))
    (hA0 : (bA0).range.map θA = V0) (hA1 : (bA1).range.map θA = V1)
    (θB : StatedSp 2 (ZMod 3) →* G) (hιB : Function.Injective (θB.comp sB))
    (hιL : Function.Injective (θB.comp lB2))
    (hB2 : (lB2).range.map θB = V2) (hB1 : (sB).range.map θB = V1) :
    ∃ θB' : StatedSp 2 (ZMod 3) →* G, (∀ A, θB' (sB A) = θA (bA1 A)) ∧
      Function.Injective (θB'.comp lB2) ∧ (lB2).range.map θB' = V2 := by
  have hrA : (θA.comp bA1).range = V1 := by rw [MonoidHom.range_comp]; exact hA1
  have hrB : (θB.comp sB).range = V1 := by rw [MonoidHom.range_comp]; exact hB1
  obtain ⟨α, hα⟩ := exists_mulEquiv_of_range_eq hιA hιB (hrA.trans hrB.symm)
  have hα' : ∀ a, θA (bA1 (α a)) = θB (sB a) := hα
  have hrelA : RelsHold (fun j => θA (a2Mat j)) a2Words := relsHold_hom θA a2_relsHold
  have m0p : θA (a2Mat 0) ∈ V0 := by
    rw [a2Mat_zero, ← hA0]
    exact mem_map_range θA _ xpS
  have m0m : θA (a2Mat 1) ∈ V0 := by
    rw [a2Mat_one, ← hA0]
    exact mem_map_range θA _ xmS
  rcases aut_dichotomy α with ⟨B, hBs, hBl⟩ | ⟨k, hk, ha, hb⟩
  ·
    let θB' : StatedSp 2 (ZMod 3) →* G := θB.comp (MulAut.conj B⁻¹).toMonoidHom
    have hθB' : ∀ x, θB' x = θB (B⁻¹ * x * B) := by
      intro x
      simp [θB']
    have hS : ∀ A, θB' (sB A) = θA (bA1 A) := by
      intro A
      have h1 := hBs (α.symm A)
      rw [α.apply_symm_apply] at h1
      have h2 : B⁻¹ * sB A * B = sB (α.symm A) := by
        rw [← h1]
        group
      rw [hθB', h2, ← hα' (α.symm A), α.apply_symm_apply]
    have hLconj : (lB2).range.map (MulAut.conj B⁻¹).toMonoidHom = (lB2).range := by
      ext x
      constructor
      · rintro ⟨y, ⟨A, rfl⟩, rfl⟩
        obtain ⟨A'', hA''⟩ := (hBl A).2
        exact ⟨A'', by
          show lB2 A'' = B⁻¹ * lB2 A * B⁻¹⁻¹
          rw [inv_inv, hA'']⟩
      · rintro ⟨A, rfl⟩
        obtain ⟨A', hA'⟩ := (hBl A).1
        refine ⟨lB2 A', ⟨A', rfl⟩, ?_⟩
        show B⁻¹ * lB2 A' * B⁻¹⁻¹ = lB2 A
        rw [← hA', inv_inv]
        group
    refine ⟨θB', hS, ?_, ?_⟩
    ·
      intro A₁ A₂ h
      obtain ⟨A₁', h₁⟩ := (hBl A₁).2
      obtain ⟨A₂', h₂⟩ := (hBl A₂).2
      have h' : θB (lB2 A₁') = θB (lB2 A₂') := by
        rw [← h₁, ← h₂, ← hθB', ← hθB']
        exact h
      have hA' : A₁' = A₂' := hιL h'
      have hl : lB2 A₁ = lB2 A₂ := by
        have e : B⁻¹ * lB2 A₁ * B = B⁻¹ * lB2 A₂ * B := by rw [h₁, h₂, hA']
        simpa using e
      exact longBlock_injective (K := ZMod 3) (n := 2) 1 hl
    · rw [← hB2]
      show (lB2).range.map (θB.comp (MulAut.conj B⁻¹).toMonoidHom) = _
      rw [← Subgroup.map_map, hLconj]
  ·
    exfalso
    have hrelC : RelsHold (fun j => θB (c2Mat j)) c2Words := relsHold_hom θB c2_relsHold
    have m2p : θB (c2Mat 2) ∈ V2 := by
      rw [c2Mat_two, ← hB2]
      exact mem_map_range θB _ xpS
    have m3p : θB (c2Mat 3) ∈ V2 := by
      rw [c2Mat_three, ← hB2]
      exact mem_map_range θB _ xmS
    have hp : gOf (fun j => θA (a2Mat j)) (fun j => θB (c2Mat j)) xPlus =
        (θA.comp bA1) autXp := by
      show θA (a2Mat 4) = θA (bA1 autXp)
      rw [a2Mat_four, adj_autXp_eq]
    have hm : gOf (fun j => θA (a2Mat j)) (fun j => θB (c2Mat j)) xMinus =
        (θA.comp bA1) autXm := by
      show θA (a2Mat 5) = θA (bA1 autXm)
      rw [a2Mat_five, adj_autXm_eq]
    have hga : evalW (gOf (fun j => θA (a2Mat j)) (fun j => θB (c2Mat j))) (gluingA k) =
        θB (c2Mat 5) := by
      rw [evalW_gluingA_map (θA.comp bA1) _ hp hm k, ← ha]
      show θA (bA1 (α autXp)) = θB (c2Mat 5)
      rw [hα' autXp, c2Mat_five, adj_autXp_eq]
    have hgb : evalW (gOf (fun j => θA (a2Mat j)) (fun j => θB (c2Mat j))) (gluingB k) =
        θB (c2Mat 6) := by
      rw [evalW_gluingB_map (θA.comp bA1) _ hp hm k, ← hb]
      show θA (bA1 (α autXm)) = θB (c2Mat 6)
      rw [hα' autXm, c2Mat_six, adj_autXm_eq]
    have hrels : RelsHold (gOf (fun j => θA (a2Mat j)) (fun j => θB (c2Mat j))) (v6aWords k) :=
      relsHold_v6Glued _ _ hrelA hrelC (gluingA k) (gluingB k) hga hgb (hcomm _ m0p _ m2p)
        (hcomm _ m0p _ m3p) (hcomm _ m0m _ m2p) (hcomm _ m0m _ m3p)
    have h9 := hC k hk _ hrels 9
    have h9' : θA (bA1 xpS) = θA (bA1 1) := by
      have e : gOf (fun j => θA (a2Mat j)) (fun j => θB (c2Mat j)) 9 = θA (bA1 xpS) := by
        show θA (a2Mat 4) = _
        rw [a2Mat_four]
      rw [e] at h9
      rw [h9, map_one, map_one]
    exact adj_xpS_ne_one (hιA (a₁ := xpS) (a₂ := 1) h9')

end Adjust

end CFSG.ClassicalInvolution.Q3.Q3V
