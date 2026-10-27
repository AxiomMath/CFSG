module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6B4F4
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6SM3

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

abbrev y63Q (c : Ctx6 G L) : Subgroup G := c.s.T ⊔ M3 c.s

structure Y63Hyps (c : Ctx6 G L) : Prop where
  S3_le : S3 c.s ≤ y63Q c
  card_Q : Nat.card ↥(y63Q c) = 2 ^ 10
  card : Nat.card ↥(y63Q c) = 2 * Nat.card ↥(S3 c.s)
  t_mem : c.s.t ∈ y63Q c
  t_not_mem : c.s.t ∉ S3 c.s
  M_le : M3 c.s ≤ S3 c.s
  M_norm : S3 c.s ≤ normalizer (M3 c.s : Set G)
  M_comm : IsMulCommutative ↥(M3 c.s)
  M_equiv : Nonempty (↥(M3 c.s) ≃* (Fin 3 → Multiplicative (ZMod 4)))
  S_le : c.s.fr.S ≤ S3 c.s
  S_card : Nat.card ↥c.s.fr.S = 64
  S_sup : c.s.fr.S ⊔ M3 c.s = S3 c.s
  omega_le : omega1 (M3 c.s) ≤ c.s.fr.S
  t_cent : ∀ x ∈ c.s.fr.S, c.s.t * x * c.s.t⁻¹ = x
  t_inv : ∀ m ∈ M3 c.s, c.s.t * m * c.s.t⁻¹ = m⁻¹
  Q_eq : y63Q c = S3 c.s ⊔ zpowers c.s.t

theorem y63_hyps (c : Ctx6 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5)
    (hRT : c.s.R = c.s.T) : Y63Hyps c := by
  have hQeq : y63Q c = S3 c.s ⊔ zpowers c.s.t := by
    show c.s.T ⊔ M3 c.s = S3 c.s ⊔ zpowers c.s.t
    rw [show S3 c.s = c.s.fr.S ⊔ M3 c.s from rfl, ← hRT, y5_R_eq hH, sup_right_comm]
  have hcardQ : Nat.card ↥(y63Q c) = 2 ^ 10 := by
    show Nat.card ↥(c.s.T ⊔ M3 c.s) = 2 ^ 10
    rw [y6_card_TM3 c hH hF, (y6_card_T hH).1 hRT]
    norm_num
  have hcardS3 : Nat.card ↥(S3 c.s) = 512 := y6e_card_S3 c.toCtx5 hH
  have hcardQ' : Nat.card ↥(y63Q c) = 2 * Nat.card ↥(S3 c.s) := by
    rw [hcardQ, hcardS3]
    norm_num
  refine ⟨?_, hcardQ, hcardQ', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, ?_, ?_, ?_, hQeq⟩
  · exact sup_le_sup_right (c.s.S_le_R.trans c.s.R_le_T) _
  · exact Subgroup.mem_sup_left (c.s.R_le_T (s3_t_mem_R c.s))
  · intro h
    have hsub : S3 c.s ⊔ zpowers c.s.t = S3 c.s :=
      sup_eq_left.mpr (Subgroup.zpowers_le.mpr h)
    have hEq : Nat.card ↥(y63Q c) = Nat.card ↥(S3 c.s) := by rw [hQeq, hsub]
    rw [hcardQ', hcardS3] at hEq
    omega
  · exact le_sup_right
  · exact (y6e_S3_le_X c.toCtx5 hH).trans
      (sup_le (y6e_NL_le_normalizer_M3 c.toCtx5 hH) Subgroup.le_normalizer)
  · exact y6e_M3_comm c.toCtx5 hF
  · exact y6e_M3_equiv c hH hF
  · exact le_sup_left
  · exact y54_card_S hH
  · show Subgroup.closure {y | y ∈ M3 c.s ∧ y ^ 2 = 1} ≤ c.s.fr.S
    rw [Subgroup.closure_le]
    rintro y ⟨hy, hy2⟩
    exact (s3_F_le_A c.s).trans (s3_A_le_S c.s) (y6b_M3_sqone c hH hF y hy hy2)
  · intro x hx
    have hcomm : c.s.t * x = x * c.s.t :=
      (Subgroup.mem_centralizer_iff.mp c.s.t_mem x (s3_S_le_L c.s hx)).symm
    rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
  · exact y6b_t_inv_M3 c hH hF

theorem y63_Q_pgroup {c : Ctx6 G L} (hY : Y63Hyps c) : IsPGroup 2 ↥(y63Q c) :=
  IsPGroup.of_card (n := 10) hY.card_Q

end CFSG.OddStandard.HigherRank.YamadaG23
