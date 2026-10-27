module

public import CFSG.ClassicalInvolution.Q3.Q3TWWAutB
public import CFSG.ClassicalInvolution.Q3.Q3TWWEvalB
public import CFSG.ClassicalInvolution.Q3.Q3ZAdjChain

public section

namespace CFSG.ClassicalInvolution.Q3.Q3TW

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

theorem exists_adjust_b3 (V0 V1 V2 : Subgroup G)
    (hcomm : ∀ a ∈ V0, ∀ b ∈ V2, a * b = b * a)
    (hC : ∀ k : Fin 24, gluingComplete k = false → ∀ g : Fin 12 → G,
      RelsHold g (b3aWords k) → ∀ i, g i = 1)
    (θA : SL(3, ZMod 3) →* G) (hιA : Function.Injective (θA.comp bA1))
    (hA0 : (bA0).range.map θA = V0) (hA1 : (bA1).range.map θA = V1)
    (θB : StatedSp 2 (ZMod 3) →* G) (hιL : Function.Injective (θB.comp lB2))
    (hιS : Function.Injective (θB.comp sB))
    (hB1 : (lB2).range.map θB = V1) (hB2 : (sB).range.map θB = V2) :
    ∃ (θA' : SL(3, ZMod 3) →* G) (θB' : StatedSp 2 (ZMod 3) →* G),
      θA'.comp bA0 = θA.comp bA0 ∧ (∀ A, θB' (lB2 A) = θA' (bA1 A)) ∧
      Function.Injective (θA'.comp bA1) ∧ (bA1).range.map θA' = V1 ∧
      Function.Injective (θB'.comp sB) ∧ (sB).range.map θB' = V2 := by
  have hrA : (θA.comp bA1).range = V1 := by rw [MonoidHom.range_comp]; exact hA1
  have hrB : (θB.comp lB2).range = V1 := by rw [MonoidHom.range_comp]; exact hB1
  obtain ⟨α, hα⟩ := exists_mulEquiv_of_range_eq hιA hιL (hrA.trans hrB.symm)
  have hα' : ∀ a, θA (bA1 (α a)) = θB (lB2 a) := hα
  have hrelA : RelsHold (fun j => θA (a2Mat j)) a2Words := relsHold_hom θA a2_relsHold
  have m0p : θA (a2Mat 0) ∈ V0 := by
    rw [a2Mat_zero, ← hA0]
    exact mem_map_range θA _ xpS
  have m0m : θA (a2Mat 1) ∈ V0 := by
    rw [a2Mat_one, ← hA0]
    exact mem_map_range θA _ xmS
  obtain ⟨k, hp, hm⟩ := aut_pair_cases α
  by_cases hk : k.val < 4
  ·
    obtain ⟨j, rfl⟩ : ∃ j : Fin 4, Fin.castLE (by norm_num) j = k :=
      ⟨⟨k.val, hk⟩, Fin.ext rfl⟩
    rw [evalW_gluingA_castLE] at hp
    rw [evalW_gluingB_castLE] at hm
    obtain ⟨t, B, ht0, htA, htA', htL, hBS, hBS'⟩ := absorb_b j α hp hm
    let θA' : SL(3, ZMod 3) →* G := θA.comp (MulAut.conj t).toMonoidHom
    let θB' : StatedSp 2 (ZMod 3) →* G := θB.comp (MulAut.conj B⁻¹).toMonoidHom
    have hθA' : ∀ x, θA' x = θA (t * x * t⁻¹) := fun x => rfl
    have hθB' : ∀ x, θB' x = θB (B⁻¹ * x * B) := by
      intro x
      simp [θB']
    have hLA : ∀ A A', t * bA1 A * t⁻¹ = bA1 A' → θA' (bA1 A) = θA (bA1 A') := by
      intro A A' h
      rw [hθA', h]
    refine ⟨θA', θB', ?_, ?_, ?_, ?_, ?_, ?_⟩
    · refine MonoidHom.ext fun A => ?_
      show θA (t * bA0 A * t⁻¹) = θA (bA0 A)
      rw [ht0]
    · intro A
      obtain ⟨A', hA'⟩ := htA A
      rw [hLA A A' hA', hθB', htL A A' hA', ← hα' (α.symm A'), α.apply_symm_apply]
    · intro A₁ A₂ h
      obtain ⟨A₁', h₁⟩ := htA A₁
      obtain ⟨A₂', h₂⟩ := htA A₂
      have h' : (θA.comp bA1) A₁' = (θA.comp bA1) A₂' := by
        have := h
        simp only [MonoidHom.comp_apply] at this ⊢
        rw [hLA A₁ A₁' h₁, hLA A₂ A₂' h₂] at this
        exact this
      have hA' : A₁' = A₂' := hιA h'
      subst hA'
      have : bA1 A₁ = bA1 A₂ := by
        have e : t * bA1 A₁ * t⁻¹ = t * bA1 A₂ * t⁻¹ := by rw [h₁, h₂]
        simpa using e
      exact blockSL_one_injective this
    · rw [← hA1]
      ext x
      constructor
      · rintro ⟨y, ⟨A, rfl⟩, rfl⟩
        obtain ⟨A', hA'⟩ := htA A
        rw [hLA A A' hA']
        exact mem_map_range θA _ A'
      · rintro ⟨y, ⟨A', rfl⟩, rfl⟩
        obtain ⟨A, hA⟩ := htA' A'
        exact ⟨bA1 A, ⟨A, rfl⟩, hLA A A' hA⟩
    · intro A₁ A₂ h
      obtain ⟨A₁', h₁⟩ := hBS' A₁
      obtain ⟨A₂', h₂⟩ := hBS' A₂
      have h' : θB (sB A₁') = θB (sB A₂') := by
        rw [← h₁, ← h₂, ← hθB', ← hθB']
        exact h
      have hA' : A₁' = A₂' := hιS h'
      subst hA'
      have : sB A₁ = sB A₂ := by
        have e : B⁻¹ * sB A₁ * B = B⁻¹ * sB A₂ * B := by rw [h₁, h₂]
        simpa using e
      exact shortBlock_injective (K := ZMod 3) _ this
    · rw [← hB2]
      ext x
      constructor
      · rintro ⟨y, ⟨A, rfl⟩, rfl⟩
        obtain ⟨A', hA'⟩ := hBS' A
        refine ⟨sB A', ⟨A', rfl⟩, ?_⟩
        show θB (sB A') = θB' (sB A)
        rw [hθB', hA']
      · rintro ⟨y, ⟨A', rfl⟩, rfl⟩
        obtain ⟨A'', hA''⟩ := hBS A'
        refine ⟨sB A'', ⟨A'', rfl⟩, ?_⟩
        show θB' (sB A'') = θB (sB A')
        rw [hθB']
        have : B⁻¹ * sB A'' * B = sB A' := by
          rw [← hA'']
          group
        rw [this]
  ·
    exfalso
    have hk' : gluingComplete k = false := decide_eq_false hk
    have hrelC : RelsHold (fun j => θB (c2Mat j)) c2Words := relsHold_hom θB c2_relsHold
    have m5p : θB (c2Mat 5) ∈ V2 := by
      rw [c2Mat_five, ← hB2]
      exact mem_map_range θB _ xpS
    have m6p : θB (c2Mat 6) ∈ V2 := by
      rw [c2Mat_six, ← hB2]
      exact mem_map_range θB _ xmS
    have hp' : gOfB (fun j => θA (a2Mat j)) (fun j => θB (c2Mat j)) xPlus =
        (θA.comp bA1) autXp := by
      show θA (a2Mat 4) = θA (bA1 autXp)
      rw [a2Mat_four, adj_autXp_eq]
    have hm' : gOfB (fun j => θA (a2Mat j)) (fun j => θB (c2Mat j)) xMinus =
        (θA.comp bA1) autXm := by
      show θA (a2Mat 5) = θA (bA1 autXm)
      rw [a2Mat_five, adj_autXm_eq]
    have hga : evalW (gOfB (fun j => θA (a2Mat j)) (fun j => θB (c2Mat j))) (gluingA k) =
        θB (c2Mat 2) := by
      rw [evalW_gluingA_map (θA.comp bA1) _ hp' hm' k, ← hp]
      show θA (bA1 (α autXp)) = θB (c2Mat 2)
      rw [hα' autXp, c2Mat_two, adj_autXp_eq]
    have hgb : evalW (gOfB (fun j => θA (a2Mat j)) (fun j => θB (c2Mat j))) (gluingB k) =
        θB (c2Mat 3) := by
      rw [evalW_gluingB_map (θA.comp bA1) _ hp' hm' k, ← hm]
      show θA (bA1 (α autXm)) = θB (c2Mat 3)
      rw [hα' autXm, c2Mat_three, adj_autXm_eq]
    have hrels : RelsHold (gOfB (fun j => θA (a2Mat j)) (fun j => θB (c2Mat j))) (b3aWords k) :=
      relsHold_b3Glued _ _ hrelA hrelC (gluingA k) (gluingB k) hga hgb (hcomm _ m0p _ m5p)
        (hcomm _ m0p _ m6p) (hcomm _ m0m _ m5p) (hcomm _ m0m _ m6p)
    have h9 := hC k hk' _ hrels 9
    have h9' : θA (bA1 xpS) = θA (bA1 1) := by
      have e : gOfB (fun j => θA (a2Mat j)) (fun j => θB (c2Mat j)) 9 = θA (bA1 xpS) := by
        show θA (a2Mat 4) = _
        rw [a2Mat_four]
      rw [e] at h9
      rw [h9, map_one, map_one]
    exact adj_xpS_ne_one (hιA (a₁ := xpS) (a₂ := 1) h9')

end Adjust

end CFSG.ClassicalInvolution.Q3.Q3TW
