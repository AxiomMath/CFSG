module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.KD8abAS3

public noncomputable section

namespace CFSG.OddStandard.SmallF3.L33.KD
open CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace KD8ab
open CFSG.ComponentClassification.HSFLit.KD8ab

open Sec8

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : SDData t L}

namespace SPkg

variable {P : SPkg A}

namespace SEl

variable (E : P.SEl) (hw : E.s * P.w * E.s⁻¹ = P.w)

include hw in
theorem conj_t (ht2 : t * t = 1) {h : X} (hh : h ∈ normalizer (E.T₃ : Set X)) :
    ∃ g ∈ E.T₃, h * t * h⁻¹ = g * t * g⁻¹ := by
  have hzh := E.h_z ht2 hh
  set y := h * t * h⁻¹ with hy
  have hyT : y ∈ E.T₃ := Sec7.conj_mem_of_mem_normalizer hh (E.T₂_le_T₃ P.t_mem)
  have hy2 : y * y = 1 := by
    rw [hy, show h * t * h⁻¹ * (h * t * h⁻¹) = h * (t * t) * h⁻¹ by group, ht2]; group
  have hyw : y * P.w * y⁻¹ = P.z * P.w := by
    have hhi : h⁻¹ ∈ normalizer (E.T₃ : Set X) := inv_mem hh
    have e : y * P.w * y⁻¹ = h * (t * (h⁻¹ * P.w * h) * t⁻¹) * h⁻¹ := by rw [hy]; group
    rcases E.h_w ht2 hw hhi with h1 | h1 <;> rw [inv_inv] at h1
    · have h2 : h * P.w * h⁻¹ = P.w := by
        calc h * P.w * h⁻¹ = h * (h⁻¹ * P.w * h) * h⁻¹ := by rw [h1]
          _ = P.w := by group
      rw [e, h1, P.t_w, show h * (P.z * P.w) * h⁻¹ = (h * P.z * h⁻¹) * (h * P.w * h⁻¹) by group,
        hzh, h2]
    · have h2 : P.w = P.z * (h * P.w * h⁻¹) := by
        calc P.w = h * (h⁻¹ * P.w * h) * h⁻¹ := by group
          _ = h * (P.z * P.w) * h⁻¹ := by rw [h1]
          _ = (h * P.z * h⁻¹) * (h * P.w * h⁻¹) := by group
          _ = P.z * (h * P.w * h⁻¹) := by rw [hzh]
      have h3 : h * P.w * h⁻¹ = P.z * P.w := by
        calc h * P.w * h⁻¹ = P.z * (P.z * (h * P.w * h⁻¹)) := by
              rw [← mul_assoc, P.zz, one_mul]
          _ = P.z * P.w := by rw [← h2]
      rw [e, h1, P.flip_mul_z P.t_flip_w_z P.t_w, h3]
  rcases E.mem_T₃ hyT with hyT₂ | hyT₂
  · rcases P.fus y hyT₂ ⟨h, rfl⟩ with ⟨g, hg, hgy⟩ | ⟨hyk, -⟩
    · exact ⟨g, E.T₂_le_T₃ hg, hgy⟩
    ·
      have hy' : E.s⁻¹ * y * E.s ∈ P.T₂ := E.conj_inv_mem hyT₂
      have hyz : y * P.z * y⁻¹ = P.z := P.conj_z hyT₂
      have hfix : y * (E.s * P.k * E.s⁻¹) * y⁻¹ = E.s * P.k * E.s⁻¹ := by
        have hkw := P.flip_kw hyk hyw
        rcases E.s_k with h1 | h1 <;> rw [h1]
        · exact hkw
        · rw [show P.z * P.k * P.w = P.z * (P.k * P.w) by group]
          exact P.fix_mul_z hyz hkw
      have hk' : (E.s⁻¹ * y * E.s) * P.k * (E.s⁻¹ * y * E.s)⁻¹ = P.k := by
        rw [show (E.s⁻¹ * y * E.s) * P.k * (E.s⁻¹ * y * E.s)⁻¹ =
          E.s⁻¹ * (y * (E.s * P.k * E.s⁻¹) * y⁻¹) * E.s by group, hfix]
        group
      rcases P.fus _ hy' ⟨E.s⁻¹ * h, by rw [hy]; group⟩ with ⟨g, hg, hgy⟩ | ⟨hk'', -⟩
      · refine ⟨E.s * g, mul_mem E.s_mem_T₃ (E.T₂_le_T₃ hg), ?_⟩
        calc h * t * h⁻¹ = E.s * (E.s⁻¹ * y * E.s) * E.s⁻¹ := by rw [hy]; group
          _ = E.s * g * t * (E.s * g)⁻¹ := by rw [hgy]; group
      · exact absurd (hk'.symm.trans hk'') P.k_ne_zk
  · exfalso
    set a := y * E.s⁻¹ with ha
    have hye : y = a * E.s := by rw [ha]; group
    have haw : a * P.w * a⁻¹ = P.z * P.w := by
      rw [← hyw, hye, show a * E.s * P.w * (a * E.s)⁻¹ = a * (E.s * P.w * E.s⁻¹) * a⁻¹ by group,
        hw]
    exact E.sq_ne_one hw hyT₂ haw (by rw [← hye]; exact hy2)

include hw in
theorem max_T₃ (ht2 : t * t = 1) {R : Subgroup X} (hR : IsPGroup 2 R) (hle : E.T₃ ≤ R) :
    R = E.T₃ :=
  eq_of_conj A (P.Tp_le.trans E.T₂_le_T₃) P.Tp_le_C P.card_T_le
    (fun _ _ _ _ _ hh => E.conj_t hw ht2 hh) hR hle

include hw in
theorem ts_mem_normalizer_U₁ : t * E.s ∈ normalizer (P.U₁ : Set X) := by
  refine mul_mem P.t_mem_normalizer_U₁ (mem_normalizer_of_conj_le fun g hg => ?_)
  obtain ⟨hgT, hgw⟩ := P.mem_U₁.mp hg
  refine P.mem_U₁.mpr ⟨E.conj_mem hgT, ?_⟩
  have hwi : E.s⁻¹ * P.w * E.s = P.w := inv_fix hw
  calc E.s * g * E.s⁻¹ * P.w = E.s * (g * (E.s⁻¹ * P.w * E.s)) * E.s⁻¹ := by group
    _ = E.s * (P.w * g) * E.s⁻¹ := by rw [hwi, hgw]
    _ = (E.s * P.w * E.s⁻¹) * (E.s * g * E.s⁻¹) := by group
    _ = P.w * (E.s * g * E.s⁻¹) := by rw [hw]

omit [Finite X] in
include hw in
theorem ts_sq_mem_U₁ : t * E.s * (t * E.s) ∈ P.U₁ := by
  refine P.mem_U₁.mpr ⟨?_, ?_⟩
  · rw [show t * E.s * (t * E.s) = t * (E.s * t * E.s⁻¹) * (E.s * E.s) by group]
    exact mul_mem (mul_mem P.t_mem E.x_mem) E.hs2
  · have h1 : (t * E.s) * P.w * (t * E.s)⁻¹ = P.z * P.w := by
      rw [show (t * E.s) * P.w * (t * E.s)⁻¹ = t * (E.s * P.w * E.s⁻¹) * t⁻¹ by group, hw, P.t_w]
    have hz : (t * E.s) * P.z * (t * E.s)⁻¹ = P.z := by
      rw [show (t * E.s) * P.z * (t * E.s)⁻¹ = t * (E.s * P.z * E.s⁻¹) * t⁻¹ by group, E.s_z,
        P.t_flip_w_z]
    have h2 : (t * E.s * (t * E.s)) * P.w * (t * E.s * (t * E.s))⁻¹ = P.w := by
      rw [show (t * E.s * (t * E.s)) * P.w * (t * E.s * (t * E.s))⁻¹ =
        (t * E.s) * ((t * E.s) * P.w * (t * E.s)⁻¹) * (t * E.s)⁻¹ by group, h1,
        P.flip_mul_z hz h1]
    exact comm_of_conj h2

omit [Finite X] in
theorem ts_not_mem_U₁ : t * E.s ∉ P.U₁ := fun h => E.hsT (by
  have := mul_mem (inv_mem P.t_mem) (P.mem_U₁.mp h).1
  rwa [inv_mul_cancel_left] at this)

@[expose] noncomputable def Ustar : Subgroup X := P.U₁ ⊔ zpowers (t * E.s)

omit [Finite X] in
theorem Ustar_le : E.Ustar ≤ E.T₃ :=
  sup_le (inf_le_left.trans E.T₂_le_T₃)
    (zpowers_le.mpr (mul_mem (E.T₂_le_T₃ P.t_mem) E.s_mem_T₃))

include hw in
theorem not_conjTo_Ustar (ht2 : t * t = 1) {m : X} (hm : m ∈ E.Ustar) : ¬ ConjTo t m := by
  rcases Sec7.mem_or_of_mem_sup_zpowers (E.ts_mem_normalizer_U₁ hw)
    (by rw [pow_two]; exact E.ts_sq_mem_U₁ hw) hm with h | h
  · exact P.noconj m (P.mem_U₁.mp h).1 (P.mem_U₁.mp h).2
  · intro hc
    obtain ⟨huT, huw⟩ := P.mem_U₁.mp h
    set u := m * (t * E.s)⁻¹ with hu
    have hme : m = (u * t) * E.s := by rw [hu]; group
    have haw : (u * t) * P.w * (u * t)⁻¹ = P.z * P.w := by
      rw [show (u * t) * P.w * (u * t)⁻¹ = u * (t * P.w * t⁻¹) * u⁻¹ by group, P.t_w,
        show u * (P.z * P.w) * u⁻¹ = (u * P.z * u⁻¹) * (u * P.w * u⁻¹) by group,
        P.conj_z huT, show u * P.w * u⁻¹ = P.w by rw [huw, mul_inv_cancel_right]]
    refine E.sq_ne_one hw (mul_mem huT P.t_mem) haw ?_
    rw [← hme]
    exact sq_of_conjTo hc ht2

include hw in
theorem relIndex_Ustar (ht2 : t * t = 1) : E.Ustar.relIndex E.T₃ = 2 := by
  have h1 := card_mul_index (E.Ustar.subgroupOf E.T₃)
  rw [show Nat.card (E.Ustar.subgroupOf E.T₃) = Nat.card E.Ustar from
    Nat.card_congr (subgroupOfEquivOfLe E.Ustar_le).toEquiv] at h1
  have h2 : Nat.card E.Ustar = 2 * Nat.card P.U₁ :=
    card_sup_zpowers (E.ts_mem_normalizer_U₁ hw) (E.ts_sq_mem_U₁ hw) E.ts_not_mem_U₁
  rw [E.card_T₃, P.card_T₂ ht2, h2] at h1
  have hpos : 0 < Nat.card P.U₁ := Nat.card_pos
  rw [relIndex]
  nlinarith

end SEl

theorem false_of_simple (P : SPkg A) [IsSimpleGroup X] (hX : ∃ a b : X, a * b ≠ b * a)
    (ht : orderOf t = 2) : False := by
  have ht2 : t * t = 1 := by rw [← pow_two, ← ht]; exact pow_orderOf_eq_one t
  by_cases hmax : ∀ R : Subgroup X, IsPGroup 2 R → P.T₂ ≤ R → R = P.T₂
  · exact P.false_of_max hX ht hmax
  · obtain ⟨E₀⟩ := P.nonempty_SEl hmax
    obtain ⟨E, hw⟩ := P.exists_SEl_fix E₀
    exact false_of_transfer' hX ht E.isPGroup_T₃ (fun R hR hle => E.max_T₃ hw ht2 hR hle)
      E.Ustar_le (E.relIndex_Ustar hw ht2) fun m hm => E.not_conjTo_Ustar hw ht2 hm

end SPkg

end KD8ab

end CFSG.OddStandard.SmallF3.L33.KD
