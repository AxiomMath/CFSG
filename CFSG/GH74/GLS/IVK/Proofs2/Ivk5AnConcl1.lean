module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk5AnC
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk5AnStmt
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk5AnUT3

public section

namespace CFSG.GH74.GLS.IVK.Proofs2.Ivk5An

open Subgroup Equiv CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm4 CFSG.GH74.GLS.IVK.Lifted
  CFSG.GH74.GLS.Bg.TwoGroups CFSG.GH74.GLS.Bg.TwoGroups.L23
open scoped commutatorElement

section Basic

variable {H : Type} [Group H] {K : Subgroup H} {m : ℕ}

theorem ZK_eq_zpowers [Finite H] {n : ℕ} (hH : Hyp5B H K n) {R : PermRep K n} {z : H}
    (hz : R.KerData z) (hzK : z ∈ ZK K) : ZK K = zpowers z := by
  have hcard : Nat.card ↥(ZK K) = 2 := by
    have h1 : Nat.card ↥(ZK K) = Nat.card ↥(center ↥K) :=
      Subgroup.card_map_of_injective K.subtype_injective
    rw [h1]
    exact hH.cover.2.1
  have hord : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz.sq) hz.ne_one
  have hle : zpowers z ≤ ZK K := (zpowers_le).mpr hzK
  have hcz : Nat.card ↥(zpowers z) = 2 := by rw [Nat.card_zpowers, hord]
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hcz])).symm

namespace Cfg

variable {R : PermRep K (m + 1)} {z : H} (Γ : Cfg R z)

include Γ

@[expose] noncomputable def QEquiv : UT3 F4c ≃* ↥Γ.Q :=
  MonoidHom.ofInjective (Γ.L.psi_injective Γ.hz Γ.h7 Γ.h10)

theorem QEquiv_apply (x : UT3 F4c) :
    ((Γ.QEquiv x : ↥Γ.Q) : H) = Γ.L.psi Γ.hz Γ.h7 Γ.h10 x := rfl

@[expose] def ZQ : Subgroup H := (center ↥Γ.Q).map Γ.Q.subtype

theorem psi_central (c : F4c) :
    Γ.L.psi Γ.hz Γ.h7 Γ.h10 ⟨0, 0, c⟩ = zpow2 Γ.t c.a * zpow2 z c.b := by
  rw [Lifts.psi_apply]
  show pairp Γ.L.x1 Γ.L.x2 (0 : F4c) * pairp Γ.L.u Γ.L.v (0 : F4c) * pairp Γ.L.t z c = _
  rw [pairp_zero, pairp_zero, one_mul, one_mul]
  rfl

theorem center_Q : Γ.ZQ = zpowers Γ.t ⊔ zpowers z := by
  apply le_antisymm
  · rintro _ ⟨g, hg, rfl⟩
    have hg' := (mem_center_of_equiv_UT3_iff Γ.QEquiv.symm g).mp hg
    obtain ⟨x, rfl⟩ := Γ.QEquiv.surjective g
    rw [MulEquiv.symm_apply_apply] at hg'
    have hx : x = ⟨0, 0, x.c⟩ := UT3.ext hg'.1 hg'.2 rfl
    show ((Γ.QEquiv x : ↥Γ.Q) : H) ∈ _
    rw [QEquiv_apply, hx, Γ.psi_central]
    refine mul_mem (Subgroup.mem_sup_left ?_) (Subgroup.mem_sup_right ?_)
    · exact zpow2_mem' (mem_zpowers _) _
    · exact zpow2_mem' (mem_zpowers _) _
  · refine sup_le ?_ ?_
    · rw [zpowers_le]
      refine ⟨Γ.QEquiv ⟨0, 0, 1⟩, ?_, ?_⟩
      · rw [SetLike.mem_coe, mem_center_of_equiv_UT3_iff Γ.QEquiv.symm, MulEquiv.symm_apply_apply]
        exact ⟨rfl, rfl⟩
      · show ((Γ.QEquiv ⟨0, 0, 1⟩ : ↥Γ.Q) : H) = Γ.t
        rw [QEquiv_apply, Γ.psi_central]
        show zpow2 Γ.t (1 : ZMod 2) * zpow2 z (0 : ZMod 2) = _
        rw [zpow2_one, zpow2_zero, mul_one]
    · rw [zpowers_le]
      refine ⟨Γ.QEquiv ⟨0, 0, omegaC⟩, ?_, ?_⟩
      · rw [SetLike.mem_coe, mem_center_of_equiv_UT3_iff Γ.QEquiv.symm, MulEquiv.symm_apply_apply]
        exact ⟨rfl, rfl⟩
      · show ((Γ.QEquiv ⟨0, 0, omegaC⟩ : ↥Γ.Q) : H) = z
        rw [QEquiv_apply, Γ.psi_central]
        show zpow2 Γ.t (0 : ZMod 2) * zpow2 z (1 : ZMod 2) = _
        rw [zpow2_one, zpow2_zero, one_mul]

theorem card_center_Q : Nat.card ↥Γ.ZQ = 4 := by
  unfold ZQ
  rw [Subgroup.card_map_of_injective Γ.Q.subtype_injective]
  exact card_center_of_equiv_UT3 Γ.QEquiv.symm

end Cfg

end Basic

end CFSG.GH74.GLS.IVK.Proofs2.Ivk5An
