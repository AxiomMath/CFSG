module

public import CFSG.LargeExtraspecial.AS35QIxBad1
public import CFSG.LargeExtraspecial.AS35QIxFus

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.AS35QIx

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.Blueprint.Fischer (K)

variable {G : Type} [Group G] [Finite G] {S : Setting G}

namespace IxLift

variable (T : IxLift S)

theorem z_InN : T.InN S.z := Or.inl (by rw [← S.z_comm T.hZhM]; group)

theorem t_InN : T.InN T.t := Or.inl (by
  calc T.t * T.Zh * T.t⁻¹ = T.Zh * T.t * T.t⁻¹ := by rw [← T.Zh_t]
    _ = T.Zh := by group)

theorem exists_lift_N {σ : S.O} (hσ : σ ∈ S.Mbar) :
    ∃ n : G, ∃ hn : n ∈ S.M, T.InN n ∧ S.ρ ⟨n, hn⟩ = σ := by
  obtain ⟨⟨m, hmM⟩, hm⟩ := hσ
  obtain ⟨q, hq, hqN⟩ := T.exists_mem_N hmM
  have hqM := S.QG_le_M hq
  refine ⟨q⁻¹ * m, S.M.mul_mem (S.M.inv_mem hqM) hmM, hqN, ?_⟩
  rw [show (⟨q⁻¹ * m, S.M.mul_mem (S.M.inv_mem hqM) hmM⟩ : S.M) = (⟨q, hqM⟩ : S.M)⁻¹ * ⟨m, hmM⟩
    from rfl, map_mul, map_inv, (S.ρ_eq_one_iff _).mpr hq, inv_one, one_mul, hm]

theorem exists_lift_N_three {σ : S.O} (hσ : σ ∈ S.Mbar) (hσ3 : σ ^ 3 = 1) :
    ∃ n : G, ∃ hn : n ∈ S.M, T.InN n ∧ S.ρ ⟨n, hn⟩ = σ ∧ n ^ 3 = 1 := by
  obtain ⟨n, hn, hnN, hρ⟩ := T.exists_lift_N hσ
  have h3M : n ^ 3 ∈ S.M := S.M.pow_mem hn 3
  have h3Q : n ^ 3 ∈ S.QG := by
    refine (S.ρ_eq_one_iff ⟨_, h3M⟩).mp ?_
    rw [show (⟨n ^ 3, h3M⟩ : S.M) = ⟨n, hn⟩ ^ 3 from rfl, map_pow, hρ, hσ3]
  have h3N : T.InN (n ^ 3) := by
    rw [pow_three]
    exact hnN.mul T (hnN.mul T hnN)
  rcases T.eq_one_or_z_of_mem_N h3Q h3N with h | h
  · exact ⟨n, hn, hnN, hρ, h⟩
  · refine ⟨n * S.z, S.M.mul_mem hn S.z_mem_M, hnN.mul T T.z_InN, ?_, ?_⟩
    · rw [show (⟨n * S.z, S.M.mul_mem hn S.z_mem_M⟩ : S.M) = ⟨n, hn⟩ * ⟨S.z, S.z_mem_M⟩ from rfl,
        map_mul, hρ, (S.ρ_eq_one_iff _).mpr S.z_mem_QG, mul_one]
    · rw [Commute.mul_pow (S.z_comm hn) 3, h, pow_three, S.z_mul_z, mul_one, S.z_mul_z]

end IxLift

structure IxBad (S : Setting G) extends IxLift S where
  m₁ : S.O
  hm₁ : m₁ ∈ S.Mbar
  hm₁ζ : m₁ * ζ ≠ ζ * m₁
  xh : G
  hxhM : xh ∈ S.M
  hxhN : xh * Zh * xh⁻¹ = Zh ∨ xh * Zh * xh⁻¹ = Zh⁻¹
  hxhρ : S.ρ ⟨xh, hxhM⟩ = β
  hxh3 : xh ^ 3 = 1
  a0 : G
  ha0M : a0 ∈ S.M
  ha0N : a0 * Zh * a0⁻¹ = Zh ∨ a0 * Zh * a0⁻¹ = Zh⁻¹
  ha0ρ : S.ρ ⟨a0, ha0M⟩ = toIxSetup.F

theorem IxLift.exists_bad (T : IxLift S) (hS : S.SixHyp) {m₁ : S.O} (hm₁ : m₁ ∈ S.Mbar)
    (hm₁ζ : m₁ * T.ζ ≠ T.ζ * m₁) : ∃ B : IxBad S, B.toIxLift = T := by
  obtain ⟨xh, hxhM, hxhN, hxhρ, hxh3⟩ := T.exists_lift_N_three (T.hXM T.hβX) T.hβ3
  obtain ⟨a0, ha0M, ha0N, ha0ρ⟩ := T.exists_lift_N (T.F_mem_Mbar hS hm₁ hm₁ζ)
  exact ⟨{ T with
    m₁ := m₁, hm₁ := hm₁, hm₁ζ := hm₁ζ
    xh := xh, hxhM := hxhM, hxhN := hxhN, hxhρ := hxhρ, hxh3 := hxh3
    a0 := a0, ha0M := ha0M, ha0N := ha0N, ha0ρ := ha0ρ }, rfl⟩

namespace IxBad

variable (T : IxBad S)

theorem a0_comm_t : T.a0 * T.t = T.t * T.a0 := by
  have hρ : S.ρ ⟨T.a0, T.ha0M⟩ * S.ρ ⟨T.t, T.t_mem_M⟩ =
      S.ρ ⟨T.t, T.t_mem_M⟩ * S.ρ ⟨T.a0, T.ha0M⟩ := by
    rw [T.ha0ρ, ← IxSetup.tb_eq]
    exact T.F_comm_tb
  rcases T.toIxLift.comm_or_of_mem_N T.ha0M T.t_mem_M T.ha0N T.toIxLift.t_InN hρ with h | h
  · calc T.a0 * T.t = (T.a0 * T.t * T.a0⁻¹ * T.t⁻¹) * (T.t * T.a0) := by group
      _ = T.t * T.a0 := by rw [h, one_mul]
  · exfalso
    apply T.not_isConj_zt
    refine T.isConj_t.trans (isConj_iff.mpr ⟨T.a0, ?_⟩)
    calc T.a0 * T.t * T.a0⁻¹ = (T.a0 * T.t * T.a0⁻¹ * T.t⁻¹) * T.t := by group
      _ = S.z * T.t := by rw [h]

theorem a0_comm_xh : T.a0 * T.xh = T.xh * T.a0 := by
  have hρ : S.ρ ⟨T.a0, T.ha0M⟩ * S.ρ ⟨T.xh, T.hxhM⟩ =
      S.ρ ⟨T.xh, T.hxhM⟩ * S.ρ ⟨T.a0, T.ha0M⟩ := by
    rw [T.ha0ρ, T.hxhρ]
    exact T.F_comm_beta
  rcases T.toIxLift.comm_or_of_mem_N T.ha0M T.hxhM T.ha0N T.hxhN hρ with h | h
  · calc T.a0 * T.xh = (T.a0 * T.xh * T.a0⁻¹ * T.xh⁻¹) * (T.xh * T.a0) := by group
      _ = T.xh * T.a0 := by rw [h, one_mul]
  · exfalso
    have h1 : T.a0 * T.xh * T.a0⁻¹ = S.z * T.xh := by
      calc T.a0 * T.xh * T.a0⁻¹ = (T.a0 * T.xh * T.a0⁻¹ * T.xh⁻¹) * T.xh := by group
        _ = S.z * T.xh := by rw [h]
    have h2 : (T.a0 * T.xh * T.a0⁻¹) ^ 3 = 1 := by
      rw [← MulAut.conj_apply, ← map_pow, T.hxh3, map_one]
    rw [h1, Commute.mul_pow (S.z_comm T.hxhM).symm 3, T.hxh3, mul_one, pow_three, S.z_mul_z,
      mul_one] at h2
    exact S.z_ne_one h2

theorem a0_sq : T.a0 * T.a0 = 1 ∨ T.a0 * T.a0 = S.z := by
  have hM := S.M.mul_mem T.ha0M T.ha0M
  have hQ : T.a0 * T.a0 ∈ S.QG := by
    refine (S.ρ_eq_one_iff ⟨_, hM⟩).mp ?_
    rw [show (⟨T.a0 * T.a0, hM⟩ : S.M) = ⟨T.a0, T.ha0M⟩ * ⟨T.a0, T.ha0M⟩ from rfl, map_mul,
      T.ha0ρ, T.F_mul_self]
  exact T.toIxLift.eq_one_or_z_of_mem_N hQ (IxLift.InN.mul T.toIxLift T.ha0N T.ha0N)

@[expose] noncomputable def CQ : Subgroup G := S.QG ⊓ centralizer {T.xh}

theorem mem_CQ {u : G} : u ∈ T.CQ ↔ u ∈ S.QG ∧ u * T.xh = T.xh * u := by
  rw [CQ, mem_inf, mem_centralizer_singleton_iff]

theorem mem_CQ_iff {u : G} (hu : u ∈ S.QG) :
    u ∈ T.CQ ↔ (T.β : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl u) = S.cl u := by
  have hcl : (T.β : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl u) = S.cl (T.xh * u * T.xh⁻¹) := by
    rw [← S.rhoL_cl T.hxhM hu, Setting.rhoL, T.hxhρ]
  rw [mem_CQ, hcl]
  constructor
  · rintro ⟨-, h⟩
    rw [← h, mul_inv_cancel_right]
  · intro h
    refine ⟨hu, ?_⟩
    rcases (S.cl_eq_cl_iff (S.conj_mem_QG T.hxhM hu) hu).mp h with h1 | h1
    · calc u * T.xh = T.xh * u * T.xh⁻¹ * T.xh := by rw [← h1]
        _ = T.xh * u := by group
    · exfalso
      have h1' : T.xh * u * T.xh⁻¹ = u * S.z := by
        calc T.xh * u * T.xh⁻¹ = (T.xh * u * T.xh⁻¹ * S.z) * S.z := by
              rw [mul_assoc _ S.z, S.z_mul_z, mul_one]
          _ = u * S.z := by rw [← h1]
      have hzx : T.xh * S.z * T.xh⁻¹ = S.z := by rw [S.z_comm T.hxhM]; group
      have hz : T.xh * (u * S.z) * T.xh⁻¹ = u := by
        calc T.xh * (u * S.z) * T.xh⁻¹ = (T.xh * u * T.xh⁻¹) * (T.xh * S.z * T.xh⁻¹) := by group
          _ = u * S.z * S.z := by rw [h1', hzx]
          _ = u := by rw [mul_assoc, S.z_mul_z, mul_one]
      have h3 : (T.xh * (T.xh * T.xh)) * u * (T.xh * (T.xh * T.xh))⁻¹ = u * S.z := by
        calc (T.xh * (T.xh * T.xh)) * u * (T.xh * (T.xh * T.xh))⁻¹ =
            T.xh * (T.xh * (T.xh * u * T.xh⁻¹) * T.xh⁻¹) * T.xh⁻¹ := by group
          _ = T.xh * (T.xh * (u * S.z) * T.xh⁻¹) * T.xh⁻¹ := by rw [h1']
          _ = T.xh * u * T.xh⁻¹ := by rw [hz]
          _ = u * S.z := h1'
      rw [← pow_three, T.hxh3, one_mul, inv_one, mul_one] at h3
      apply S.z_ne_one
      calc S.z = u⁻¹ * (u * S.z) := by group
        _ = 1 := by rw [← h3, inv_mul_cancel]

theorem CQ_le_QG : T.CQ ≤ S.QG := inf_le_left

theorem CQ_comm_xh {u : G} (hu : u ∈ T.CQ) : u * T.xh = T.xh * u := (T.mem_CQ.mp hu).2

theorem CQ_comm_t (hS : S.SixHyp) {u : G} (hu : u ∈ T.CQ) : u * T.t = T.t * u := by
  have huQ := T.CQ_le_QG hu
  have hβ := (T.mem_CQ_iff huQ).mp hu
  have htb := T.tb_fix_of_beta_fix hβ
  have h := S.conj_eq_of_cl_conj_eq hS.sixFour hS.weak T.t_mem_DSet T.t_mem_M huQ (by
    rw [← S.rhoL_cl T.t_mem_M huQ]
    exact htb)
  calc u * T.t = T.t * u * T.t⁻¹ * T.t := by rw [h]
    _ = T.t * u := by group

theorem eq_one_of_mem_CQ_Qa (hS : S.SixHyp) {u : G} (hu : u ∈ T.CQ) (huQt : u ∈ S.Qa T.g) :
    u = 1 := by
  have huQ := T.CQ_le_QG hu
  have hβ := (T.mem_CQ_iff huQ).mp hu
  have hcomm := S.cl_mem_commSpace_of_commute hS.sixFour hS.weak T.hgD T.hgM huQ
    (S.commute_of_mem_inf_Qa_J hS T.hgD rfl (mem_inf.mpr ⟨huQ, huQt⟩))
  have h0 := T.eq_zero_of_beta_fix_of_mem_commSpace hβ hcomm
  rcases (S.cl_eq_zero_iff huQ).mp h0 with h | h
  · exact h
  · exfalso
    rw [h] at huQt
    exact S.z_not_mem_Qa hS.weak (S.ne_z_of_mem_ESet T.hgD.1) huQt

end IxBad

end CFSG.LargeExtraspecial.AS35QIx
