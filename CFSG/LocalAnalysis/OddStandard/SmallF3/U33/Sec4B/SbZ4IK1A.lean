module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4IK1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4IS0
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4IK0A

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped commutatorElement

variable {H : Type*} [Group H] [Finite H]

namespace ZIKData

variable {Q Y V V' B K : Subgroup H} {ρ : H}

private lemma z4ik1a_rho_conj_rho (ρ x : H) :
    ρ * (ρ * x * ρ⁻¹) * ρ⁻¹ = ρ ^ 2 * x * (ρ ^ 2)⁻¹ := by
  rw [pow_two, mul_inv_rev]; group

private lemma z4ik1a_rho_conj_rho_sq (h : ZIKData Q Y V V' B K ρ) (x : H) :
    ρ * (ρ ^ 2 * x * (ρ ^ 2)⁻¹) * ρ⁻¹ = x := by
  have h3 : ρ * ρ * ρ = 1 := by rw [← pow_three']; exact h.rho_pow_three
  have h3i : ρ⁻¹ * ρ⁻¹ * ρ⁻¹ = 1 := by
    rw [← pow_three', inv_pow, h.rho_pow_three, inv_one]
  rw [pow_two, mul_inv_rev]
  calc ρ * (ρ * ρ * x * (ρ⁻¹ * ρ⁻¹)) * ρ⁻¹
      = (ρ * ρ * ρ) * x * (ρ⁻¹ * ρ⁻¹ * ρ⁻¹) := by group
    _ = x := by rw [h3, h3i]; group

private lemma z4ik1a_rho_sq_conj_rho (h : ZIKData Q Y V V' B K ρ) (x : H) :
    ρ ^ 2 * (ρ * x * ρ⁻¹) * (ρ ^ 2)⁻¹ = x := by
  have h3 : ρ * ρ * ρ = 1 := by rw [← pow_three']; exact h.rho_pow_three
  have h3i : ρ⁻¹ * ρ⁻¹ * ρ⁻¹ = 1 := by
    rw [← pow_three', inv_pow, h.rho_pow_three, inv_one]
  rw [pow_two, mul_inv_rev]
  calc (ρ * ρ) * (ρ * x * ρ⁻¹) * (ρ⁻¹ * ρ⁻¹)
      = (ρ * ρ * ρ) * x * (ρ⁻¹ * ρ⁻¹ * ρ⁻¹) := by group
    _ = x := by rw [h3, h3i]; group

theorem nondeg (h : ZIKData Q Y V V' B K ρ) {β q : H} (hβ : β ∈ K) (hβQ : β ∉ Q) (hq : q ∈ Q)
    (hc : β * q = q * β) : q ∈ Y := by
  by_contra hqY
  set q1 : H := ρ * q * ρ⁻¹ with hq1
  set q2 : H := ρ ^ 2 * q * (ρ ^ 2)⁻¹ with hq2
  set β1 : H := ρ * β * ρ⁻¹ with hβ1
  set β2 : H := ρ ^ 2 * β * (ρ ^ 2)⁻¹ with hβ2
  have hq1Q : q1 ∈ Q := by rw [hq1]; exact h.rho_norm_Q q hq
  have hq2Q : q2 ∈ Q := by
    rw [hq2]
    have h' := h.rho_norm_Q q1 hq1Q
    rwa [hq1, z4ik1a_rho_conj_rho] at h'
  have hβ1K : β1 ∈ K := by rw [hβ1]; exact h.rho_norm_K β hβ
  have hβ2K : β2 ∈ K := by
    rw [hβ2]
    have h' := h.rho_norm_K β1 hβ1K
    rwa [hβ1, z4ik1a_rho_conj_rho] at h'
  have hy0 : q * q1 * q2 ∈ Y := by
    rw [hq1, hq2]
    refine z4i_norm3_mem h.rho_pow_three h.Y_le_Q ?_ h.rho_norm_Y h.rho_norm_Q h.fpf_QY hq
    intro x hx y hy
    rw [← commutatorElement_def, commutatorElement_eq_one_iff_mul_comm.mpr (h.Q_comm x hx y hy)]
    exact Y.one_mem
  have hβy0 : β * (q * q1 * q2) = (q * q1 * q2) * β := h.K_cent_Y β hβ _ hy0
  have ha0 : ⁅β, q⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr hc
  have hkey : ⁅β, q⁆ * (⁅β, q1⁆ * ⁅β, q2⁆) = 1 := by
    have h1 : ⁅β, q * q1 * q2⁆ = ⁅β, q⁆ * (⁅β, q1⁆ * ⁅β, q2⁆) := by
      rw [show q * q1 * q2 = q * (q1 * q2) by group,
        h.comm_mul_right hβ hq (Q.mul_mem hq1Q hq2Q),
        h.comm_mul_right hβ hq1Q hq2Q]
    have h2 : ⁅β, q * q1 * q2⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr hβy0
    rw [h1] at h2
    exact h2
  have h12 : ⁅β, q1⁆ * ⁅β, q2⁆ = 1 := by simpa [ha0] using hkey
  have ha2 : ⁅β, q2⁆ = ⁅β, q1⁆⁻¹ := eq_inv_of_mul_eq_one_right h12
  have hbQ : β * β1 * β2 ∈ Q := by
    rw [hβ1, hβ2]
    refine z4i_norm3_mem h.rho_pow_three h.Q_le_K ?_ h.rho_norm_Q h.rho_norm_K
      h.rho_fpf_KQ hβ
    intro x hx y hy
    exact h.V_le_Q (h.comm_mem_V x hx y hy)
  have hbq : ⁅β * β1 * β2, q⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr (h.Q_comm _ hbQ q hq)
  have hβ1conj : ⁅β1, q⁆ = ρ * ⁅β, q2⁆ * ρ⁻¹ := by
    rw [hβ1, hq2, conjugate_commutatorElement,
      show ρ * (ρ ^ 2 * q * (ρ ^ 2)⁻¹) * ρ⁻¹ = q from z4ik1a_rho_conj_rho_sq h q]
  have hβ2conj : ⁅β2, q⁆ = ρ ^ 2 * ⁅β, q1⁆ * (ρ ^ 2)⁻¹ := by
    rw [hβ2, hq1, conjugate_commutatorElement,
      show ρ ^ 2 * (ρ * q * ρ⁻¹) * (ρ ^ 2)⁻¹ = q from z4ik1a_rho_sq_conj_rho h q]
  have hmm : ⁅β * β1 * β2, q⁆ = ⁅β2, q⁆ * (⁅β1, q⁆ * ⁅β, q⁆) := by
    rw [show β * β1 * β2 = (β * β1) * β2 by group]
    rw [h.comm_mul_left (K.mul_mem hβ hβ1K) hβ2K hq, h.comm_mul_left hβ hβ1K hq]
  have h31 : (ρ ^ 2 * ⁅β, q1⁆ * (ρ ^ 2)⁻¹) * (ρ * ⁅β, q2⁆ * ρ⁻¹) = 1 := by
    have h' := hbq
    rw [hmm] at h'
    simpa [hβ1conj, hβ2conj, ha0] using h'
  have hβ2inv : ρ * ⁅β, q2⁆ * ρ⁻¹ = (ρ * ⁅β, q1⁆ * ρ⁻¹)⁻¹ := by
    rw [ha2]; group
  have hXeqW : ρ ^ 2 * ⁅β, q1⁆ * (ρ ^ 2)⁻¹ = ρ * ⁅β, q1⁆ * ρ⁻¹ := by
    have h' := h31
    rw [hβ2inv] at h'
    exact mul_inv_eq_one.mp h'
  have hXa1 : ρ ^ 2 * ⁅β, q1⁆ * (ρ ^ 2)⁻¹ = ⁅β, q1⁆ := by
    have h' := z4ik1a_rho_conj_rho_sq h ⁅β, q1⁆
    rw [hXeqW] at h'
    exact (z4ik1a_rho_conj_rho ρ ⁅β, q1⁆).symm.trans h'
  have ha1fix : ρ * ⁅β, q1⁆ * ρ⁻¹ = ⁅β, q1⁆ := hXeqW.symm.trans hXa1
  have ha1V : ⁅β, q1⁆ ∈ V := h.comm_KQ β hβ q1 hq1Q
  have ha1 : ⁅β, q1⁆ = 1 := h.rho_fpf_Q _ (h.V_le_Q ha1V) ha1fix
  have ha2one : ⁅β, q2⁆ = 1 := by rw [ha2, ha1, inv_one]
  have ha1comm : β * q1 = q1 * β := commutatorElement_eq_one_iff_mul_comm.mp ha1
  have ha2comm : β * q2 = q2 * β := commutatorElement_eq_one_iff_mul_comm.mp ha2one
  have hNn : ∀ m ∈ Q, ∀ n ∈ Y, m * n * m⁻¹ ∈ Y := by
    intro m hm n hn
    have hmul : m * n = n * m := h.Q_comm m hm n (h.Y_le_Q hn)
    have heq : m * n * m⁻¹ = n := by rw [hmul]; group
    rw [heq]; exact hn
  have hcent : ∀ c ∈ Q, β * c = c * β := by
    intro c hcQ
    obtain ⟨n, hnY, hn | hn | hn | hn⟩ :=
      z4i_cover_mod h.rho_pow_three h.Y_le_Q hNn h.rho_norm_Y h.rho_norm_Q
        h.relIndex_YQ h.fpf_QY hq hqY hcQ
    · rw [hn]; exact h.K_cent_Y β hβ n hnY
    · rw [hn]
      have hnβ : β * n = n * β := h.K_cent_Y β hβ n hnY
      calc β * (q * n) = (β * q) * n := by group
        _ = (q * β) * n := by rw [hc]
        _ = q * (β * n) := by group
        _ = q * (n * β) := by rw [hnβ]
        _ = (q * n) * β := by group
    · rw [hn]
      have hnβ : β * n = n * β := h.K_cent_Y β hβ n hnY
      have hq1β : β * (ρ * q * ρ⁻¹) = (ρ * q * ρ⁻¹) * β := by
        rw [← hq1]; exact ha1comm
      calc β * ((ρ * q * ρ⁻¹) * n) = (β * (ρ * q * ρ⁻¹)) * n := by group
        _ = ((ρ * q * ρ⁻¹) * β) * n := by rw [hq1β]
        _ = (ρ * q * ρ⁻¹) * (β * n) := by group
        _ = (ρ * q * ρ⁻¹) * (n * β) := by rw [hnβ]
        _ = ((ρ * q * ρ⁻¹) * n) * β := by group
    · rw [hn]
      have hnβ : β * n = n * β := h.K_cent_Y β hβ n hnY
      have hq2β : β * (ρ ^ 2 * q * (ρ ^ 2)⁻¹) = (ρ ^ 2 * q * (ρ ^ 2)⁻¹) * β := by
        rw [← hq2]; exact ha2comm
      calc β * ((ρ ^ 2 * q * (ρ ^ 2)⁻¹) * n)
            = (β * (ρ ^ 2 * q * (ρ ^ 2)⁻¹)) * n := by group
        _ = ((ρ ^ 2 * q * (ρ ^ 2)⁻¹) * β) * n := by rw [hq2β]
        _ = (ρ ^ 2 * q * (ρ ^ 2)⁻¹) * (β * n) := by group
        _ = (ρ ^ 2 * q * (ρ ^ 2)⁻¹) * (n * β) := by rw [hnβ]
        _ = ((ρ ^ 2 * q * (ρ ^ 2)⁻¹) * n) * β := by group
  exact hβQ (h.cent_Q β hcent)

theorem sq_mem_Y (h : ZIKData Q Y V V' B K ρ) : ∀ k ∈ K, k ^ 2 ∈ Y := by
  intro k hk
  by_cases hkQ : k ∈ Q
  · exact h.V_le_Y (h.sq_mem_V k hkQ)
  · exact nondeg h hk hkQ (h.K_sq_mem_Q k hk) (by group)

theorem cent_iff (h : ZIKData Q Y V V' B K ρ) {β q : H} (hβ : β ∈ K) (hβQ : β ∉ Q)
    (hq : q ∈ Q) : β * q = q * β ↔ q ∈ Y :=
  ⟨fun hc => nondeg h hβ hβQ hq hc, fun hy => h.K_cent_Y β hβ q hy⟩

theorem comm_surj (h : ZIKData Q Y V V' B K ρ) {β : H} (hβ : β ∈ K) (hβQ : β ∉ Q) {v : H}
    (hv : v ∈ V) : ∃ q ∈ Q, ⁅β, q⁆ = v := by
  classical
  let f : Q →* V :=
    { toFun := fun q => ⟨⁅β, (q : H)⁆, h.comm_KQ β hβ (q : H) q.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun q q' => Subtype.ext (h.comm_mul_right hβ q.2 q'.2) }
  have hker : f.ker = Y.subgroupOf Q := by
    ext q
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hq
      have h1 : ⁅β, (q : H)⁆ = 1 := congrArg Subtype.val hq
      exact (h.cent_iff hβ hβQ q.2).mp (commutatorElement_eq_one_iff_mul_comm.mp h1)
    · intro hqY
      apply Subtype.ext
      exact commutatorElement_eq_one_iff_mul_comm.mpr (h.K_cent_Y β hβ (q : H) hqY)
  have hcardker : Nat.card f.ker = 16 := by
    rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.Y_le_Q).toEquiv]
    exact h.card_Y
  have hcardrange : Nat.card f.range = 4 := by
    have hck := Subgroup.card_ker_mul_card_range f
    rw [hcardker, h.card_Q] at hck
    omega
  have hrange_top : f.range = ⊤ :=
    Subgroup.eq_top_of_card_eq f.range (by rw [hcardrange, h.card_V])
  have hvrange : (⟨v, hv⟩ : V) ∈ f.range := by rw [hrange_top]; exact Subgroup.mem_top _
  obtain ⟨q, hq⟩ := hvrange
  exact ⟨(q : H), q.2, congrArg Subtype.val hq⟩

end ZIKData

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
