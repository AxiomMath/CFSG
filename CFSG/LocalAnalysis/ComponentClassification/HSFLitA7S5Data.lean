module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7S5Q0

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup Equiv CFSG.ComponentClassification.UnbalancedLayer

theorem sig_decomp5 : ∀ σ₁ ∈ three, ∀ σ₂ ∈ three, σ₁ = σ₂ ∨
    ∃ i : Fin 3, ∃ j : Fin 2, comp (pw3 dCols i) (pw xCols j) = sigCols σ₁ σ₂ := by decide

namespace A7Base

variable {X : Type} [Group X] [Finite X] {S : A7Base X}

namespace Sec5Hyp

variable {T₁ : Subgroup X} (H : S.Sec5Hyp T₁)
include H

theorem normalizer_eq_sup (I : S.Inst) {R : Subgroup X} (hRN : R ≤ normalizer (I.E : Set X))
    (hR : Nat.card R = 128) (hRC : R ⊓ centralizer (I.E : Set X) = I.E) (hxR : S.x ∈ R)
    {d : X} (hdM : I.Mat d dCols) :
    normalizer (I.E : Set X) = centralizer (I.E : Set X) ⊔ R ⊔ zpowers d := by
  apply le_antisymm
  · intro n hn
    obtain ⟨a, b, σ₁, h₁, σ₂, h₂, h12, hM⟩ := H.classify I hn
    obtain ⟨q, hq, hqM⟩ := H.exists_transl_Q I hRN hR hRC a b
    obtain ⟨i, j, hij⟩ := (sig_decomp5 σ₁ h₁ σ₂ h₂).resolve_left h12
    have hxM : I.Mat S.x xCols := ⟨hRN hxR, I.x_cols (hRN hxR)⟩
    have hmM : I.Mat (q * (d ^ (i : ℕ) * S.x ^ (j : ℕ))) (cls5 a b σ₁ σ₂) := by
      have := hqM.mul ((hdM.pw3 i).mul (hxM.pw j))
      rwa [hij] at this
    have hc := hmM.inv_mul_mem_centralizer hM
    have e : n = q * (d ^ (i : ℕ) * S.x ^ (j : ℕ)) *
        ((q * (d ^ (i : ℕ) * S.x ^ (j : ℕ)))⁻¹ * n) := by
      group
    rw [e]
    refine mul_mem (mul_mem (mem_sup_left (mem_sup_right (mem_inf.mp hq).1))
      (mul_mem (mem_sup_right (pow_mem (mem_zpowers d) _))
        (mem_sup_left (mem_sup_right (pow_mem hxR _))))) (mem_sup_left (mem_sup_left hc))
  · exact sup_le (sup_le I.centralizer_le_normalizer hRN) (zpowers_le.mpr hdM.1)

theorem T₂of_eq_sup {w : X} (hw : w ∈ S.T₂of T₁) (hwT : w ∉ S.data.T) (hw2 : w ^ 2 = 1) :
    S.T₂of T₁ = S.data.T ⊔ zpowers w := by
  have hN : w ∈ normalizer (S.data.T : Set X) := H.le_normalizer (T₂of_le hw)
  refine (Subgroup.eq_of_le_of_card_ge (sup_le H.T_le_T₂of (zpowers_le.mpr hw)) ?_).symm
  rw [card_sup_zpowers hN (by rw [hw2]; exact one_mem _) hwT, H.card_T₂of, S.card_T]

theorem R_eq_sup {R : Subgroup X} (hR : Nat.card R = 128) (hT₂R : S.T₂of T₁ ≤ R)
    {w₂ : X} (hw₂R : w₂ ∈ R)
    (hw₂M : S.inst₁.Mat w₂ (transCols 0 1)) : R = S.T₂of T₁ ⊔ zpowers w₂ := by
  obtain ⟨w₀, hw₀, hw₀T⟩ := H.exists_w₀
  have hidx : ((S.T₂of T₁).subgroupOf R).index = 2 := by
    have h := Subgroup.card_mul_index ((S.T₂of T₁).subgroupOf R)
    rw [Nat.card_congr (subgroupOfEquivOfLe hT₂R).toEquiv, H.card_T₂of, hR] at h
    omega
  have hnorm := Subgroup.normal_of_index_eq_two hidx
  have hN : w₂ ∈ normalizer (S.T₂of T₁ : Set X) := by
    refine mem_normalizer_of_conj_mem fun h hh => ?_
    have := hnorm.conj_mem ⟨h, hT₂R hh⟩ (by rw [mem_subgroupOf]; exact hh) ⟨w₂, hw₂R⟩
    rw [mem_subgroupOf] at this
    simpa using this
  have hsq : w₂ ^ 2 ∈ S.T₂of T₁ := by
    have := Subgroup.sq_mem_of_index_two hidx ⟨w₂, hw₂R⟩
    rw [mem_subgroupOf] at this
    simpa using this
  have hnot : w₂ ∉ S.T₂of T₁ := by
    intro h
    have hwt : w₂ * S.t * w₂⁻¹ = S.t * S.inst₁.yi := by
      rw [hw₂M.conj_t]
      simp [transCols, Inst.wV, S.data.commute_t S.inst₁.yi_mem.1]
    rcases (H.mem_T₂_iff hw₀ hw₀T (T₂of_le h)).mp h with h' | h' <;> rw [hwt] at h'
    · apply S.inst₁.yi_not_mem_B
      rw [show S.inst₁.yi = S.t⁻¹ * (S.t * S.inst₁.yi) by group, h', inv_mul_cancel]
      exact one_mem _
    · rw [H.conj_w₀_t hw₀ hw₀T] at h'
      have : S.inst₁.yi = S.z := mul_left_cancel h'
      exact absurd (S.inst₁.wV_injective ((show S.inst₁.wV (0, 1, 0, 0) = S.inst₁.yi by
        simp [Inst.wV]).trans (this.trans (show S.z = S.inst₁.wV (1, 0, 0, 0) by
        simp [Inst.wV])))) (by decide)
  refine (Subgroup.eq_of_le_of_card_ge (sup_le hT₂R (zpowers_le.mpr hw₂R)) ?_).symm
  rw [card_sup_zpowers hN hsq hnot, H.card_T₂of, hR]

omit H in
theorem Q_eq_sup (I : S.Inst) {Q : Subgroup X} (hQ : Nat.card Q = 64) (hEQ : I.E ≤ Q)
    {w₁ w₂ : X} (hw₁Q : w₁ ∈ Q) (hw₂Q : w₂ ∈ Q) (hw₁M : I.Mat w₁ (transCols 1 0))
    (hw₂M : I.Mat w₂ (transCols 0 1)) (hc : w₂ * w₁ = w₁ * w₂) (hs₁ : w₁ ^ 2 ∈ I.E)
    (hs₂ : w₂ ^ 2 ∈ I.E) : Q = I.E ⊔ zpowers w₁ ⊔ zpowers w₂ := by
  have hE16 : Nat.card I.E = 16 := by
    rw [Inst.E, S.card_E I.yi_mem I.yi_sq I.yi_not_mem_B]
  have hN₁ : w₁ ∈ normalizer (I.E : Set X) := hw₁M.1
  have hw₁E : w₁ ∉ I.E := fun h => by
    have hM := Inst.Mat.of_mem_centralizer (I.E_le_centralizer h)
    have := hw₁M.unique hM
    exact absurd (congrFun this 2) (by decide)
  have hc₁ := card_sup_zpowers hN₁ hs₁ hw₁E
  have hmem : ∀ g ∈ I.E ⊔ zpowers w₁, g ∈ I.E ∨ w₁⁻¹ * g ∈ I.E := fun g hg =>
    (mem_sup_zpowers_iff hN₁ hs₁).mp hg
  have hN₂ : w₂ ∈ normalizer ((I.E ⊔ zpowers w₁ : Subgroup X) : Set X) := by
    refine mem_normalizer_of_conj_mem fun g hg => ?_
    rcases hmem g hg with h | h
    · exact mem_sup_left ((mem_normalizer_iff.mp hw₂M.1 g).mp h)
    · have e : w₂ * g * w₂⁻¹ = w₁ * (w₂ * (w₁⁻¹ * g) * w₂⁻¹) := by
        calc w₂ * g * w₂⁻¹ = (w₂ * w₁) * (w₁⁻¹ * g) * w₂⁻¹ := by group
          _ = (w₁ * w₂) * (w₁⁻¹ * g) * w₂⁻¹ := by rw [hc]
          _ = w₁ * (w₂ * (w₁⁻¹ * g) * w₂⁻¹) := by group
      rw [e]
      exact mul_mem (mem_sup_right (mem_zpowers w₁))
        (mem_sup_left ((mem_normalizer_iff.mp hw₂M.1 _).mp h))
  have hw₂E : w₂ ∉ I.E ⊔ zpowers w₁ := by
    intro h
    rcases hmem w₂ h with h' | h'
    · have hM := Inst.Mat.of_mem_centralizer (I.E_le_centralizer h')
      exact absurd (congrFun (hw₂M.unique hM) 2) (by decide)
    · have hM := Inst.Mat.of_mem_centralizer (I.E_le_centralizer h')
      have h2 := (hw₁M.mul hM)
      rw [mul_inv_cancel_left] at h2
      have := hw₂M.unique h2
      exact absurd (congrFun this 2) (by decide)
  have hc₂ := card_sup_zpowers hN₂ (mem_sup_left hs₂) hw₂E
  refine (Subgroup.eq_of_le_of_card_ge (sup_le (sup_le hEQ (zpowers_le.mpr hw₁Q))
    (zpowers_le.mpr hw₂Q)) ?_).symm
  rw [hc₂, hc₁, hE16, hQ]

@[expose] noncomputable def qd (I : S.Inst) {R : Subgroup X} (hRp : IsPGroup 2 R)
    (hRN : R ≤ normalizer (I.E : Set X)) (hR : Nat.card R = 128)
    (hRC : R ⊓ centralizer (I.E : Set X) = I.E) {d : X} (hdM : I.Mat d dCols)
    (hdQ : d ∈ normalizer ((R ⊓ oddTwoCoreIn (normalizer (I.E : Set X)) : Subgroup X) : Set X))
    (hd3 : ∃ a : ℕ, d ^ (3 ^ a) = 1) : I.QD where
  Q := R ⊓ oddTwoCoreIn (normalizer (I.E : Set X))
  d := d
  isPGroup := hRp.to_le inf_le_left
  le := inf_le_left.trans hRN
  inf_centralizer := (H.Q_props I hRN hR hRC).2.1
  d_mat := hdM
  d_normalizer := hdQ
  d_cube := by
    intro q hq
    have hM3 : I.Mat (d ^ 3) bas := by
      have := hdM.mul (hdM.mul hdM)
      rwa [show comp dCols (comp dCols dCols) = bas from funext dCols_ddCols', ← pow_three] at this
    have hodd : Odd (orderOf (d ^ 3)) := by
      obtain ⟨a, ha⟩ := hd3
      have h1 : orderOf (d ^ 3) ∣ 3 ^ a := by
        apply orderOf_dvd_of_pow_eq_one
        rw [← pow_mul, mul_comm, pow_mul, ha, one_pow]
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 3)).mp h1
      rw [hj]
      exact Odd.pow (by decide)
    have hK := I.mem_K_of_odd hM3.mem_centralizer hodd
    exact I.commute_of_mem_K (hRp.to_le inf_le_left) (inf_le_left.trans hRN) hK
      (pow_mem hdQ 3) hq
  ki_central := by
    intro q hq
    have h := H.k_fixed I (hRN (mem_inf.mp hq).1)
    calc q * I.ki = q * I.ki * q⁻¹ * q := by group
      _ = I.ki * q := by rw [h]

end Sec5Hyp

end A7Base

end CFSG.ComponentClassification.HSFLit
