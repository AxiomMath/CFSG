module

public import CFSG.ClassicalInvolution.Q3.Q3VF4Adjust
public import CFSG.ClassicalInvolution.Q3.Q3VCtFrMain
public import CFSG.ClassicalInvolution.Q3.Q3ZPres
public import CFSG.ClassicalInvolution.WeakCT.DLDiagrams
public import CFSG.ClassicalInvolution.WeakCT.DoublyLaced

public section

namespace CFSG.ClassicalInvolution.Q3.Q3V

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.ClassicalInvolution.Q3.Q3Z CFSG.ClassicalInvolution.Q3.Q3TW
open CFSG.ClassicalInvolution.WeakCT
  (blk blockSL spBlock LinearBlockStandardPair spBlock_one_eq_longBlock spBlock_zero_eq_shortBlock
    map_blk pair_normalize)
open scoped MatrixGroups

structure F4Frame (F : Type) [Field F] {X : Type} [Group X] (U : Fin 4 → Subgroup X) where
  ρ : Fin 4 → (SL(2, F) →* X)
  ρ_inj : ∀ k, Function.Injective (ρ k)
  ρ_range : ∀ k, (ρ k).range = U k
  ψL : SL(3, F) →* X
  ψL_zero : ψL.comp (blk F 0) = ρ 0
  ψL_one : ψL.comp (blk F 1) = ρ 1
  ψR : SL(3, F) →* X
  ψR_zero : ψR.comp (blk F 0) = ρ 3
  ψR_one : ψR.comp (blk F 1) = ρ 2
  ψ4 : StatedSp 2 F →* X
  ψ4_long : ψ4.comp (spBlock F 1) = ρ 1
  ψ4_short : ψ4.comp (spBlock F 0) = ρ 2

abbrev F4Frame3 {X : Type} [Group X] (U : Fin 4 → Subgroup X) : Type :=
  F4Frame (GaloisField 3 1) U

section Transport

variable {K K' : Type} [Field K] [Field K'] {X : Type} [Group X] {U : Fin 4 → Subgroup X}

private theorem f4_map_comp_blk (φ : K →+* K') (s : Fin 2) :
    (Matrix.SpecialLinearGroup.map φ : SL(3, K) →* SL(3, K')).comp (blk K s) =
      (blk K' s).comp (Matrix.SpecialLinearGroup.map φ : SL(2, K) →* SL(2, K')) :=
  MonoidHom.ext fun A => map_blk φ s A

private theorem f4_spMap_comp_spBlock_one (φ : K →+* K') :
    (spMap (n := 2) φ).comp (spBlock K 1) =
      (spBlock K' 1).comp (Matrix.SpecialLinearGroup.map φ : SL(2, K) →* SL(2, K')) := by
  rw [spBlock_one_eq_longBlock, spBlock_one_eq_longBlock]
  exact MonoidHom.ext fun A => spMap_longBlock φ 1 A

private theorem f4_spMap_comp_spBlock_zero (φ : K →+* K') :
    (spMap (n := 2) φ).comp (spBlock K 0) =
      (spBlock K' 0).comp (Matrix.SpecialLinearGroup.map φ : SL(2, K) →* SL(2, K')) := by
  rw [spBlock_zero_eq_shortBlock, spBlock_zero_eq_shortBlock]
  exact MonoidHom.ext fun A => spMap_shortBlock φ zero_ne_one A

@[expose] noncomputable def F4Frame.ofRingEquiv (e : K ≃+* K') (fr : F4Frame K U) :
    F4Frame K' U where
  ρ k := (fr.ρ k).comp (Matrix.SpecialLinearGroup.map e.symm.toRingHom : SL(2, K') →* SL(2, K))
  ρ_inj k := (fr.ρ_inj k).comp (slMap_injective e.symm 2)
  ρ_range k := by
    rw [range_comp_of_surjective _ (slMap_surjective e.symm 2), fr.ρ_range]
  ψL := fr.ψL.comp (Matrix.SpecialLinearGroup.map e.symm.toRingHom : SL(3, K') →* SL(3, K))
  ψL_zero := by
    rw [MonoidHom.comp_assoc, f4_map_comp_blk, ← MonoidHom.comp_assoc, fr.ψL_zero]
  ψL_one := by
    rw [MonoidHom.comp_assoc, f4_map_comp_blk, ← MonoidHom.comp_assoc, fr.ψL_one]
  ψR := fr.ψR.comp (Matrix.SpecialLinearGroup.map e.symm.toRingHom : SL(3, K') →* SL(3, K))
  ψR_zero := by
    rw [MonoidHom.comp_assoc, f4_map_comp_blk, ← MonoidHom.comp_assoc, fr.ψR_zero]
  ψR_one := by
    rw [MonoidHom.comp_assoc, f4_map_comp_blk, ← MonoidHom.comp_assoc, fr.ψR_one]
  ψ4 := fr.ψ4.comp (spMap e.symm.toRingHom)
  ψ4_long := by
    rw [MonoidHom.comp_assoc, f4_spMap_comp_spBlock_one, ← MonoidHom.comp_assoc, fr.ψ4_long]
  ψ4_short := by
    rw [MonoidHom.comp_assoc, f4_spMap_comp_spBlock_zero, ← MonoidHom.comp_assoc, fr.ψ4_short]

end Transport

section ZModFrame

variable {X : Type} [Group X]

local notation "bA0" => (blockSL (ZMod 3) 3 2 0 (by omega) : SL(2, ZMod 3) →* SL(3, ZMod 3))
local notation "bA1" => (blockSL (ZMod 3) 3 2 1 (by omega) : SL(2, ZMod 3) →* SL(3, ZMod 3))
local notation "sB" =>
  (shortBlock (ZMod 3) (zero_ne_one : (0 : Fin 2) ≠ 1) : SL(2, ZMod 3) →* StatedSp 2 (ZMod 3))
local notation "lB2" => (longBlock (ZMod 3) 2 1 : SL(2, ZMod 3) →* StatedSp 2 (ZMod 3))

private theorem injective_of_ker_le_center {θ : SL(3, ZMod 3) →* X}
    (h : θ.ker ≤ Subgroup.center SL(3, ZMod 3)) : Function.Injective θ := by
  rw [← MonoidHom.ker_eq_bot_iff]
  refine eq_bot_iff.2 (h.trans ?_)
  rw [Q3W.center_eq_bot]

theorem exists_f4Frame_zmod (U : Fin 4 → Subgroup X)
    (hcomm : ∀ i j : Fin 4, i.val + 1 < j.val → ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a)
    (hC6 : ∀ k : Fin 24, gluingComplete k = false → ∀ g : Fin 12 → X,
      RelsHold g (v6aWords k) → ∀ i, g i = 1)
    (hC3 : ∀ k : Fin 24, gluingComplete k = false → ∀ g : Fin 12 → X,
      RelsHold g (b3aWords k) → ∀ i, g i = 1)
    (hL : ∃ W, LinearBlockStandardPair (ZMod 3) W (U 0) (U 1))
    (hR : ∃ W, LinearBlockStandardPair (ZMod 3) W (U 2) (U 3))
    (hsp : ∃ θB : StatedSp 2 (ZMod 3) →* X,
      Function.Injective (θB.comp lB2) ∧
      Function.Injective (θB.comp sB) ∧
      (lB2).range.map θB = U 1 ∧ (sB).range.map θB = U 2) :
    Nonempty (F4Frame (ZMod 3) U) := by
  have hb0inj : Function.Injective bA0 :=
    CFSG.ClassicalInvolution.WeakCT.blockSL_injective (K := ZMod 3) (m := 3) (k := 2) (i := 0)
      (by omega)
  have hb1inj : Function.Injective bA1 :=
    CFSG.ClassicalInvolution.WeakCT.blockSL_injective (K := ZMod 3) (m := 3) (k := 2) (i := 1)
      (by omega)
  obtain ⟨WR, hWR⟩ := hR
  obtain ⟨θR, -, hkR, hR0, hR1⟩ := pair_normalize hWR.symm
  have hθR := injective_of_ker_le_center hkR
  obtain ⟨θB, hιL, hιS, hB1, hB2⟩ := hsp
  obtain ⟨θB', hS, hιL', hB1'⟩ := exists_adjust_sp3 (U 3) (U 2) (U 1)
    (fun a ha b hb => (hcomm 1 3 (by decide) b hb a ha).symm) hC6 θR (hθR.comp hb1inj) hR0 hR1
    θB hιS hιL hB1 hB2
  have hS' : θB'.comp sB = θR.comp bA1 := MonoidHom.ext hS
  have hB2' : (sB).range.map θB' = U 2 := by
    rw [← MonoidHom.range_comp, hS', MonoidHom.range_comp]
    exact hR1
  obtain ⟨WL, hWL⟩ := hL
  obtain ⟨θL, -, hkL, hL0, hL1⟩ := pair_normalize hWL
  have hθL := injective_of_ker_le_center hkL
  obtain ⟨θL', hL', hιL0, hrL0⟩ := exists_adjustA_b3 (U 0) (U 1) (U 2)
    (hcomm 0 2 (by decide)) hC3 θL hθL hL0 hL1 θB' hιL' hB1' hB2'
  refine ⟨{ ρ := ![θL'.comp bA0, θB'.comp lB2, θR.comp bA1, θR.comp bA0], ρ_inj := ?_,
            ρ_range := ?_, ψL := θL', ψL_zero := ?_, ψL_one := ?_, ψR := θR, ψR_zero := ?_,
            ψR_one := ?_, ψ4 := θB', ψ4_long := ?_, ψ4_short := ?_ }⟩
  · intro k
    fin_cases k
    · exact hιL0
    · exact hιL'
    · exact hθR.comp hb1inj
    · exact hθR.comp hb0inj
  · intro k
    fin_cases k
    · show (θL'.comp bA0).range = U 0
      rw [MonoidHom.range_comp]
      exact hrL0
    · show (θB'.comp lB2).range = U 1
      rw [MonoidHom.range_comp]
      exact hB1'
    · show (θR.comp bA1).range = U 2
      rw [MonoidHom.range_comp]
      exact hR1
    · show (θR.comp bA0).range = U 3
      rw [MonoidHom.range_comp]
      exact hR0
  · rfl
  · exact MonoidHom.ext hL'
  · rfl
  · rfl
  · rw [spBlock_one_eq_longBlock]
    rfl
  · rw [spBlock_zero_eq_shortBlock]
    exact hS'

end ZModFrame

theorem exists_f4Frame_of_ringEquiv {F : Type} [Field F] (e : ZMod 3 ≃+* F) {X : Type} [Group X]
    (U : Fin 4 → Subgroup X)
    (hcomm : ∀ i j : Fin 4, i.val + 1 < j.val → ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a)
    (hC6 : ∀ k : Fin 24, gluingComplete k = false → ∀ g : Fin 12 → X,
      RelsHold g (v6aWords k) → ∀ i, g i = 1)
    (hC3 : ∀ k : Fin 24, gluingComplete k = false → ∀ g : Fin 12 → X,
      RelsHold g (b3aWords k) → ∀ i, g i = 1)
    (hL : ∃ W, LinearBlockStandardPair F W (U 0) (U 1))
    (hR : ∃ W, LinearBlockStandardPair F W (U 2) (U 3))
    (hsp : ∃ W, SymplecticBlockStandardPair F W (U 1) (U 2)) :
    Nonempty (F4Frame F U) := by
  obtain ⟨fr⟩ := exists_f4Frame_zmod U hcomm hC6 hC3
    (hL.imp fun W hW => hW.of_ringEquiv e.symm) (hR.imp fun W hW => hW.of_ringEquiv e.symm)
    (by
      obtain ⟨W, hW⟩ := hsp
      exact exists_pairB_zmod e hW)
  exact ⟨fr.ofRingEquiv e⟩

theorem exists_f4Frame3 {X : Type} [Group X] (U : Fin 4 → Subgroup X)
    (hcomm : ∀ i j : Fin 4, i.val + 1 < j.val → ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a)
    (hC6 : V6Collapse) (hC3 : B3Collapse)
    (hL : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W (U 0) (U 1))
    (hR : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W (U 2) (U 3))
    (hsp : ∃ W, SymplecticBlockStandardPair (GaloisField 3 1) W (U 1) (U 2)) :
    Nonempty (F4Frame3 U) := by
  obtain ⟨e⟩ := nonempty_ringEquiv_galoisField_three
  exact exists_f4Frame_of_ringEquiv e U hcomm (fun k hk g hg i => hC6 k hk g hg i)
    (fun k hk g hg i => hC3 k hk g hg i) hL hR hsp

end CFSG.ClassicalInvolution.Q3.Q3V
