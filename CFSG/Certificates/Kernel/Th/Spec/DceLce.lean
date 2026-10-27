module

public import CFSG.Certificates.Kernel.LceSTabSound
public import CFSG.Certificates.Kernel.Th.Spec.DceCore
public import Mathlib.GroupTheory.FreeGroup.Basic

public section

namespace CFSG.KC.Th.Spec.Dce

open CFSG.KC CFSG.KC.LceS CFSG.Certificates.LCE

theorem lceRelsNorm_congr {RT RT' : ℕ → ℕ} :
    ∀ n, (∀ r < n, RT r = RT' r) →
      CFSG.Certificates.LCE.relsNorm RT n = CFSG.Certificates.LCE.relsNorm RT' n
  | 0, _ => rfl
  | n + 1, h => by
    change CFSG.KC.andB (Nat.blt (wWord (RT n)) (Nat.shiftLeft 1 (Nat.mul 8 (wLen (RT n)))))
        (CFSG.Certificates.LCE.relsNorm RT n) =
      CFSG.KC.andB (Nat.blt (wWord (RT' n)) (Nat.shiftLeft 1 (Nat.mul 8 (wLen (RT' n)))))
        (CFSG.Certificates.LCE.relsNorm RT' n)
    rw [h n (Nat.lt_succ_self n), lceRelsNorm_congr n fun r hr => h r (Nat.lt_succ_of_lt hr)]

theorem hsw_norm27 : CFSG.Certificates.LCE.relsNorm Hsw.sel 27 = true := by decide +kernel

theorem hsw_norm14 : CFSG.Certificates.LCE.relsNorm Hsw.sel 14 = true := by decide +kernel

theorem bval_subgen {H : Type*} [Group H] (y : ℕ → H) {j : ℕ} (hj : j < 100) :
    bval y (wWord (4 + 4096 * (2 * j))) (wLen (4 + 4096 * (2 * j))) = y j := by
  have h1 : wLen (4 + 4096 * (2 * j)) = 1 := by
    have : ∀ j < 100, wLen (4 + 4096 * (2 * j)) = 1 := by decide +kernel
    exact this j hj
  have h2 : wWord (4 + 4096 * (2 * j)) = 2 * j := by
    have : ∀ j < 100, wWord (4 + 4096 * (2 * j)) = 2 * j := by decide +kernel
    exact this j hj
  rw [h1, h2]
  have h3 : CFSG.KC.wLet (2 * j) 0 = 2 * j := by
    have : ∀ j < 100, CFSG.KC.wLet (2 * j) 0 = 2 * j := by decide +kernel
    exact this j hj
  simp only [bval, List.range_one, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one, h3, letV]
  have : ¬ (2 * j = 255) := by omega
  rw [if_neg this, if_pos (by omega)]
  congr 1
  omega

theorem kchain {H : Type*} [Group H] (y : ℕ → H)
    (hy : ∀ r < 27, bval y (wWord (Hsw.sel r)) (wLen (Hsw.sel r)) = 1)
    {blk1 WT1 RT1 ST1 LVs1 : ℕ → ℕ} {INV1 INV81 nC1 nCl1 mLV1 a1 m1 Hs1 nf1 : ℕ}
    {Cs1 CCs1 : List ℕ} {S01 S11 X01 X11 : ℕ}
    (h1 : lceOk blk1 WT1 RT1 ST1 LVs1 INV1 INV81 10 nC1 nCl1 mLV1 a1 m1 Hs1 14 0 nf1 Cs1 CCs1
      S01 S11 X01 X11 = true)
    (hR1 : ∀ r < 14, RT1 r = Hsw.sel r)
    {blk3 WT3 RT3 ST3 LVs3 : ℕ → ℕ} {INV3 INV83 nC3 nCl3 mLV3 a3 m3 Hs3 nf3 : ℕ}
    {Cs3 CCs3 : List ℕ} {S03 S13 X03 X13 : ℕ}
    (h3 : lceOk blk3 WT3 RT3 ST3 LVs3 INV3 INV83 14 nC3 nCl3 mLV3 a3 m3 Hs3 27 5 nf3 Cs3 CCs3
      S03 S13 X03 X13 = true)
    (hR3 : ∀ r < 27, RT3 r = Hsw.sel r) (hS3 : ∀ j < 5, ST3 j = 4 + 4096 * (2 * j)) :
    Finite (Subgroup.closure (y '' {g | g < 7})) ∧
      Nat.card (Subgroup.closure (y '' {g | g < 7})) ≤ a1 * a3 := by
  have hr1 : ∀ r < 14, bval y (wWord (RT1 r)) (wLen (RT1 r)) = 1 := fun r hr => by
    rw [hR1 r hr]
    exact hy r (by omega)
  have hr3 : ∀ r < 27, bval y (wWord (RT3 r)) (wLen (RT3 r)) = 1 := fun r hr => by
    rw [hR3 r hr]
    exact hy r hr
  obtain ⟨hne1, hle1⟩ := lceOk_sound h1 y hr1
  obtain ⟨hne3, hle3⟩ := lceOk_sound h3 y hr3
  have e0 : ((fun j => bval y (wWord (ST1 j)) (wLen (ST1 j))) '' {j | j < 0}) = ∅ := by
    ext z
    simp
  rw [e0, Subgroup.closure_empty, Subgroup.relIndex_bot_left] at hne1 hle1
  have e3 : ((fun j => bval y (wWord (ST3 j)) (wLen (ST3 j))) '' {j | j < 5}) =
      y '' {g | 2 * g < 10} := by
    ext z
    simp only [Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨j, hj, rfl⟩
      refine ⟨j, by omega, ?_⟩
      rw [hS3 j hj]
      exact (bval_subgen y (by omega)).symm
    · rintro ⟨j, hj, rfl⟩
      refine ⟨j, by omega, ?_⟩
      rw [hS3 j (by omega)]
      exact bval_subgen y (by omega)
  rw [e3] at hne3 hle3
  have hle : Subgroup.closure (y '' {g | 2 * g < 10}) ≤ Subgroup.closure (y '' {g | 2 * g < 14}) :=
    Subgroup.closure_mono (Set.image_mono fun g hg => by
      simp only [Set.mem_setOf_eq] at hg ⊢
      omega)
  have hchain := Subgroup.relIndex_mul_relIndex (⊥ : Subgroup H)
    (Subgroup.closure (y '' {g | 2 * g < 10})) (Subgroup.closure (y '' {g | 2 * g < 14}))
    bot_le hle
  rw [Subgroup.relIndex_bot_left, Subgroup.relIndex_bot_left] at hchain
  have hset : {g : ℕ | g < 7} = {g | 2 * g < 14} := by
    ext g
    simp only [Set.mem_setOf_eq]
    omega
  rw [hset]
  have hcard0 : Nat.card (Subgroup.closure (y '' {g | 2 * g < 14})) ≠ 0 := by
    rw [← hchain]
    exact Nat.mul_ne_zero hne1 hne3
  refine ⟨Nat.finite_of_card_ne_zero hcard0, ?_⟩
  rw [← hchain]
  exact Nat.mul_le_mul hle1 hle3

theorem lceOk_of_parts {blk WT RT ST LVs : ℕ → ℕ}
    {INV INV8 L nC nCl mLV a m Hs nR nS nf : ℕ} {Cs CCs : List ℕ} {S0 S1 X0 X1 : ℕ}
    (hinv : invOK INV INV8 L = true) (hwords : wordsOK WT RT ST INV INV8 m Hs = true)
    (hhints : CFSG.KC.Bind.hintsOK WT m nR nS Hs = true) (halive : aliveOK LVs mLV nCl a = true)
    (hnC : nC = nCl) (hle : nC ≤ 1048576) (hnf : nf < 4294967296) (hm : 0 < m)
    (hper : wtPer WT m = true) (hnorm : CFSG.Certificates.LCE.relsNorm RT nR = true)
    (hS0 : S0 = mkS 0 1) (hrun : runFacts blk WT INV nC L Cs S0 = S1) (hS1 : S1 = mkS nf nC)
    (hX0 : X0 = 1) (hcov : runCover blk LVs nf L CCs X0 = X1) (hX1 : X1 = nC + 1) :
    lceOk blk WT RT ST LVs INV INV8 L nC nCl mLV a m Hs nR nS nf Cs CCs S0 S1 X0 X1 = true := by
  unfold lceOk
  simp only [andBK_iff]
  refine ⟨hinv, hwords, hhints, halive, ?_, ?_, ?_, ?_, hper, hnorm, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hnC]
    exact Nat.beq_refl _
  · exact Nat.ble_eq.mpr hle
  · exact Nat.blt_eq.mpr hnf
  · exact Nat.blt_eq.mpr hm
  · rw [hS0]
    exact Nat.beq_refl _
  · rw [hrun]
    exact Nat.beq_refl _
  · rw [hS1]
    exact Nat.beq_refl _
  · rw [hX0]
    exact Nat.beq_refl _
  · rw [hcov]
    exact Nat.beq_refl _
  · rw [hX1]
    exact Nat.beq_refl _

@[expose] noncomputable def letF (c : ℕ) : FreeGroup ℕ :=
  if c = 255 then 1 else if c % 2 = 0 then FreeGroup.of (c / 2) else (FreeGroup.of (c / 2))⁻¹

@[expose] noncomputable def relWord (e : ℕ) : FreeGroup ℕ :=
  ((List.range (wLen e)).map fun i => letF (CFSG.KC.wLet (wWord e) i)).prod

theorem lift_letF {H : Type*} [Group H] (y : ℕ → H) (c : ℕ) :
    FreeGroup.lift y (letF c) = letV y c := by
  unfold letF letV
  split_ifs
  · exact map_one _
  · rw [FreeGroup.lift_apply_of]
  · rw [map_inv, FreeGroup.lift_apply_of]

theorem lift_relWord {H : Type*} [Group H] (y : ℕ → H) (e : ℕ) :
    FreeGroup.lift y (relWord e) = bval y (wWord e) (wLen e) := by
  unfold relWord bval
  rw [map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  exact lift_letF y _

@[expose] def RelSet : Set (FreeGroup ℕ) := {r | ∃ k < 27, r = relWord (Hsw.sel k)}

theorem relSet_iff {H : Type*} [Group H] (y : ℕ → H) :
    (∀ r ∈ RelSet, FreeGroup.lift y r = 1) ↔
      ∀ k < 27, bval y (wWord (Hsw.sel k)) (wLen (Hsw.sel k)) = 1 := by
  constructor
  · intro h k hk
    rw [← lift_relWord]
    exact h _ ⟨k, hk, rfl⟩
  · rintro h r ⟨k, hk, rfl⟩
    rw [lift_relWord]
    exact h k hk

end CFSG.KC.Th.Spec.Dce

end
