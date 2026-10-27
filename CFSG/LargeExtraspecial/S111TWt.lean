module

public import CFSG.LargeExtraspecial.S111ABasic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S11

open Subgroup Module QuadraticMap CFSG.LargeExtraspecial.S4

variable {G : Type*} [Group G] [Finite G] {S : Setting G}

variable (S) in
noncomputable abbrev Wt (k : G) : Submodule (ZMod 2) S.Qt := S.clSub (S.QG ⊓ S.Qa k)

theorem polar_Wt {k : G} (hkz : k * S.z * k⁻¹ ≠ S.z) {u v : S.Qt} (hu : u ∈ Wt S k)
    (hv : v ∈ Wt S k) : polar S.q u v = 0 := by
  obtain ⟨x, hx, hxQ, rfl⟩ := S.mem_clSub_iff.mp hu
  obtain ⟨y, hy, hyQ, rfl⟩ := S.mem_clSub_iff.mp hv
  rw [S.polar_cl_eq_zero_iff hxQ hyQ]
  rcases S.mul_comm_or hxQ hyQ with h1 | h1
  · exact h1
  rcases (S.conjBy k).mul_comm_or (mem_inf.mp hx).2 (mem_inf.mp hy).2 with h2 | h2
  · exact h2
  exfalso
  apply hkz
  have h3 := h1.symm.trans h2
  exact (mul_right_cancel h3).symm

omit [Finite G] in
theorem IncClosed.clSub_le_Wt {A : Subgroup G} (hA : IncClosed S A) {k : G}
    (hk : k * S.z * k⁻¹ ∈ A) : S.clSub A ≤ Wt S k := fun v hv => by
  obtain ⟨x, hx, hxQ, rfl⟩ := S.mem_clSub_iff.mp hv
  exact S.cl_mem_clSub (mem_inf.mpr ⟨hxQ, hA.le_Qa k hk hx⟩) hxQ

theorem Wt_eq_of_cl_eq {j k : G} (hkQ : k * S.z * k⁻¹ ∈ S.QG) (hkz : k * S.z * k⁻¹ ≠ S.z)
    (hjQ : j * S.z * j⁻¹ ∈ S.QG)
    (h : S.cl (j * S.z * j⁻¹) = S.cl (k * S.z * k⁻¹)) : Wt S j = Wt S k := by
  rcases (S.cl_eq_cl_iff hkQ hjQ).mp h.symm with e | e
  · rw [Wt, Wt, S.Qa_eq_of_conj_eq e]
  · rw [Wt, Wt, QG_inf_Qa_eq_of_mul_z hkQ hkz e]

theorem apply_mem_Wt (m : S.M) {k : G} {v : S.Qt} (hv : v ∈ Wt S k) :
    ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ Wt S ((m : G) * k) := by
  obtain ⟨x, hx, hxQ, rfl⟩ := S.mem_clSub_iff.mp hv
  rw [S.ρ_cl m hxQ]
  exact S.cl_mem_clSub (mem_inf.mpr ⟨S.conj_mem_QG m.2 hxQ, conj_mem_Qa_mul S (mem_inf.mp hx).2⟩)
    (S.conj_mem_QG m.2 hxQ)

theorem Wt_inf_clSub_eq_bot {X : Subgroup G} {k : G}
    (hk : k * S.z * k⁻¹ ∈ S.QG) (hkz : k * S.z * k⁻¹ ≠ S.z) (hXk : X ⊓ S.Qa k ≤ zpowers S.z) :
    Wt S k ⊓ S.clSub X = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  obtain ⟨x, hx, hxQ, rfl⟩ := S.mem_clSub_iff.mp (Submodule.mem_inf.mp hv).1
  obtain ⟨y, hy, hyQ, hyx⟩ := S.mem_clSub_iff.mp (Submodule.mem_inf.mp hv).2
  have hzk : S.z ∈ S.Qa k := S.z_mem_Qa hk hkz
  have hyk : y ∈ S.Qa k := by
    rcases (S.cl_eq_cl_iff hxQ hyQ).mp hyx.symm with e | e
    · rw [e]; exact (mem_inf.mp hx).2
    · rw [e]; exact mul_mem (mem_inf.mp hx).2 hzk
  have hy' := hXk (mem_inf.mpr ⟨hy, hyk⟩)
  rw [Setting.mem_zpowers_iff_of_mul_self S.z_mul_z] at hy'
  rw [Submodule.mem_bot, ← hyx]
  rcases hy' with rfl | rfl
  · exact S.cl_one
  · exact S.cl_z

theorem card_Wt {k : G} (C : Cons311 S k) (hk : k * S.z * k⁻¹ ∈ S.QG)
    (hkz : k * S.z * k⁻¹ ≠ S.z) : Nat.card (Wt S k) = 2 ^ S.width := by
  have h1 := S.card_clPre (Wt S k)
  rw [S.clPre_clSub inf_le_left (mem_inf.mpr ⟨S.z_mem_QG, S.z_mem_Qa hk hkz⟩),
    C.card_QG_inf_Qa, pow_succ, mul_comm] at h1
  exact (Nat.eq_of_mul_eq_mul_left (by norm_num) h1).symm

theorem finrank_Wt {k : G} (C : Cons311 S k) (hk : k * S.z * k⁻¹ ∈ S.QG)
    (hkz : k * S.z * k⁻¹ ≠ S.z) : finrank (ZMod 2) (Wt S k) = S.width := by
  have h1 := card_Wt C hk hkz
  rw [S.card_submodule] at h1
  exact Nat.pow_right_injective le_rfl h1

end CFSG.LargeExtraspecial.S11
