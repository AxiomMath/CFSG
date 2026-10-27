module

public import CFSG.GH74.GLS.Stage1.Thm4.L96Act
public import CFSG.GH74.GLS.Stage1.Thm2.Recip.Hat

public section

namespace CFSG.GH74.GLS.Stage1.Thm4.L96

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm4
  CFSG.GH74.Uniqueness.SU.SU13.TA CFSG.GH74.GLS.IVK.Lifted
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {Lh : Type} [Group Lh] {z t : G} {S K : Subgroup G}

theorem t_ne_z (h : Ctx98 G Lh z t S K) : t ≠ z := by
  intro htz
  apply h.std.comm_nle
  rw [Subgroup.commutator_le]
  intro k hk y hy
  have hkz : Commute k z := Subgroup.mem_centralizer_singleton_iff.1 (h.K_le hk)
  rw [htz] at hy
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  have hk1 : ⁅k, z ^ j⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.2 ((hkz.zpow_right j).eq)
  rw [hk1]
  exact one_mem _

theorem inner_case (h : Ctx98 G Lh z t S K) {n : ℕ} (hn8 : 8 ≤ n) (hn11 : n ≤ 11)
    (hcov : IsDoubleCoverOfAlt Lh n) (A : Act h n)
    (hsign : Equiv.Perm.sign (A.ρ ⟨t, h.std.t_cen⟩) = 1) :
    ∃ k : ↥K, t * (k : G)⁻¹ ∈ cSec K ∧ IsFourTransp (HatT K) n (QuotientGroup.mk k) := by
  have ht2 : t ^ (2 ^ 1) = 1 := by
    rw [pow_one, ← h.std.t_ord]
    exact pow_orderOf_eq_one t
  have htK : t ∈ K := A.mem_K_of_sign hsign ht2
  refine ⟨⟨t, htK⟩, ?_, ?_⟩
  · simp only [mul_inv_cancel]
    exact one_mem _
  · set k : ↥K := ⟨t, htK⟩ with hk
    have hS : IsPGroup 2 ↥(zpowers t) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h.std.t_ord]; norm_num)
    have hSK : zpowers t ≤ K := (Subgroup.zpowers_le).2 htK
    have hord : orderOf (QuotientGroup.mk k : HatT K) = 2 := by
      have := orderOf_hatMk (K := K) hSK hS (a := t) (Subgroup.mem_zpowers t)
      rw [h.std.t_ord] at this
      exact this
    have hnk : (QuotientGroup.mk k : HatT K) ∉ A.π.ker := by
      intro hker
      have hπ : A.π (QuotientGroup.mk k) = 1 := hker
      have hρ : A.ρ ⟨t, h.std.t_cen⟩ = 1 := by
        have := A.ρ_K k
        rw [hπ] at this
        exact this
      have hz := A.mem_zpowers_of_ker hρ (m := 1) ht2
      have : t = z := eq_of_mem_zpowers_of_orderOf_two h.z_ord hz h.std.t_ord
      exact t_ne_z h this
    have hct := A.cover.cycleType_of_orderOf_eq_two hn8 hn11 hord hnk
    refine ⟨(QuotientGroup.quotientMulEquivOfEq (A.ker_eq_center hcov).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective A.π A.cover.surj), ?_⟩
    exact hct

end CFSG.GH74.GLS.Stage1.Thm4.L96
