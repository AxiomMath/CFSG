module

public import CFSG.CGT.PushingUpLit.SolKNA.Prop18Sz

public section

namespace CFSG.CGT.PushingUpLit.SolKNA

set_option linter.unusedSectionVars false

open CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.GH74.Uniqueness.Bender CFSG.RankThree.GF2n
open scoped MatrixGroups

variable {X : Type} [Group X] [Finite X]

namespace Prop18Setup

variable {R Rb L Lb N : Subgroup X} (S : Prop18Setup R Rb L Lb N)
include S

theorem exists_fpf_five [N.Normal] {a : ℕ} (ha : 1 ≤ a)
    (e : X ⧸ N ≃* Sz a) :
    ∃ a₁ ∈ R, ∃ b₁ ∈ Rb, a₁ ∉ N ∧ b₁ ∉ N ∧
      orderOf (e (QuotientGroup.mk (a₁ * b₁))) = 5 ∧
      ∀ n ∈ N, (a₁ * b₁) * n = n * (a₁ * b₁) → n = 1 := by
  classical
  have hBT : BenderType (X ⧸ N) (2 * a + 1) 2 1 :=
    .suzuki a ha (e.trans (MulEquiv.subgroupCongr (szModel_eq_open_sz a).symm))
  have hP := S.ncPair
  have hwu : e.symm (SzExplicit.w a) * e.symm (SzExplicit.w a) = 1 := by
    rw [← map_mul, SzExplicit.w_mul_self, map_one]
  have huu : e.symm (SzExplicit.u a) * e.symm (SzExplicit.u a) = 1 := by
    rw [← map_mul, SzExplicit.u_mul_self, map_one]
  have hord5 : orderOf (e.symm (SzExplicit.w a) * e.symm (SzExplicit.u a)) = 5 := by
    rw [← map_mul, MulEquiv.orderOf_eq, SzExplicit.orderOf_w_mul_u]
  obtain ⟨t, ht, s', hs', hts⟩ := exists_mul_orderOf_eq hBT hP.strongWC hP.ne_bot
    hP.symm.strongWC hP.ne_bot' hP.ne hwu huu (by rw [hord5]; decide)
    (fun h => by rw [h, orderOf_one] at hord5; exact absurd hord5 (by decide))
  rw [hord5] at hts
  obtain ⟨a₁, ha₁, rfl⟩ := ht
  obtain ⟨b₁, hb₁, rfl⟩ := hs'
  have hsq1 : QuotientGroup.mk' N a₁ * QuotientGroup.mk' N a₁ = 1 := by
    rw [← map_mul, mk_eq_one_iff]
    exact S.L_le_N (S.sq_R a₁ ha₁)
  have hsq2 : QuotientGroup.mk' N b₁ * QuotientGroup.mk' N b₁ = 1 := by
    rw [← map_mul, mk_eq_one_iff]
    exact S.Lb_le_N (S.sq_Rb b₁ hb₁)
  have hnot5 : ∀ y : X ⧸ N, y * y = 1 → orderOf y ≠ 5 := by
    intro y hy h5
    have := orderOf_dvd_of_pow_eq_one (show y ^ 2 = 1 by rw [sq]; exact hy)
    rw [h5] at this
    exact absurd this (by decide)
  have ha₁N : a₁ ∉ N := fun h => hnot5 _ hsq2 (by
    rwa [(mk_eq_one_iff a₁).mpr h, one_mul] at hts)
  have hb₁N : b₁ ∉ N := fun h => hnot5 _ hsq1 (by
    rwa [(mk_eq_one_iff b₁).mpr h, mul_one] at hts)
  refine ⟨a₁, ha₁, b₁, hb₁, ha₁N, hb₁N, ?_, fun n hn h2 =>
    S.eq_one_of_commute_mul ha₁ ha₁N hb₁ hb₁N hn h2⟩
  rw [MulEquiv.orderOf_eq]
  simpa [map_mul] using hts

end Prop18Setup

end CFSG.CGT.PushingUpLit.SolKNA
