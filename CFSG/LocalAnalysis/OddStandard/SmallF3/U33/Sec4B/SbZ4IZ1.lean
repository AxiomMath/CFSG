module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4IZ0B
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4IK1A

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped commutatorElement

variable {H : Type} [Group H] [Finite H]

namespace ZEData

variable {Q Y V V' B K : Subgroup H} {ρ t τ l : H}

theorem t_ne_one (h : ZEData Q Y V V' B K ρ t τ l) : t ≠ 1 := by
  intro ht
  exact h.t_not_mem_K (by simpa [ht] using K.one_mem)

private theorem orderOf_t (h : ZEData Q Y V V' B K ρ t τ l) : orderOf t = 2 :=
  orderOf_eq_prime (p := 2) (by rw [pow_two]; exact h.t_sq) (t_ne_one h)

theorem t_regular_Y (h : ZEData Q Y V V' B K ρ t τ l) : ActsRegularly t ⊥ Y := by
  refine (actsRegularly_iff_card (N := (⊥ : Subgroup H)) (M := Y) (orderOf_t h) bot_le
    ?_ ?_ ?_ ?_).mpr ?_
  · intro x hx y hy
    rw [Subgroup.mem_bot]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (h.toZIKData.Y_comm x hx y hy)
  · intro x hx
    rw [Subgroup.mem_bot, pow_two]
    exact h.Y_sq x hx
  · intro g hg
    rw [Subgroup.mem_bot] at hg ⊢
    rw [hg]
    group
  · intro g hg
    exact h.normal_Y t g hg
  · have hset : Nat.card {g : H // g ∈ Y ∧ ⁅t, g⁆ ∈ (⊥ : Subgroup H)}
        = Nat.card ↥(Y ⊓ centralizer ({t} : Set H)) := by
      apply Nat.card_congr
      refine Equiv.subtypeEquivRight ?_
      intro g
      constructor
      · rintro ⟨hgY, hg⟩
        refine ⟨hgY, Subgroup.mem_centralizer_iff.mpr ?_⟩
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        rw [hy]
        exact commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp hg)
      · rintro ⟨hgY, hgc⟩
        refine ⟨hgY, ?_⟩
        rw [Subgroup.mem_bot]
        exact commutatorElement_eq_one_iff_mul_comm.mpr
          (Subgroup.mem_centralizer_iff.mp hgc t (Set.mem_singleton t))
    have hVC : Y ⊓ centralizer ({t} : Set H) = V := by
      apply le_antisymm
      · intro x hx
        exact h.Y_cent_t x hx.1
          (Subgroup.mem_centralizer_iff.mp hx.2 t (Set.mem_singleton t))
      · intro x hx
        exact ⟨h.toZIKData.V_le_Y hx,
          Subgroup.mem_centralizer_iff.mpr (fun y hy => by
            rw [Set.mem_singleton_iff] at hy
            rw [hy]
            exact h.V_cent_t x hx)⟩
    rw [hset, hVC, h.card_V, h.toZIKData.card_Y, Subgroup.card_bot]
    norm_num

theorem cent_K_t (h : ZEData Q Y V V' B K ρ t τ l) :
    ∀ x ∈ K, t * x = x * t → x ∈ B := by
  let C : Subgroup H := K ⊓ centralizer ({t} : Set H)
  let T3 : Subgroup H := z4iT3 t τ l
  let R : Subgroup H := C ⊔ T3
  have hT3C : ∀ s ∈ T3, ∀ c ∈ C, s * c * s⁻¹ ∈ C := by
    intro s hs c hc
    refine ⟨h.T3_norm_K s hs c hc.1, ?_⟩
    have hs_cent : s ∈ centralizer ({t} : Set H) := h.T3_cent_t hs
    have hst : t * s = s * t := Subgroup.mem_centralizer_iff.mp hs_cent t (Set.mem_singleton t)
    have hct : t * c = c * t :=
      Subgroup.mem_centralizer_iff.mp hc.2 t (Set.mem_singleton t)
    have hs1 : t * s * t⁻¹ = s := by rw [hst]; group
    have hc1 : t * c * t⁻¹ = c := by rw [hct]; group
    have hconj : t * (s * c * s⁻¹) * t⁻¹ = s * c * s⁻¹ := by
      calc t * (s * c * s⁻¹) * t⁻¹
          = (t * s * t⁻¹) * (t * c * t⁻¹) * (t * s * t⁻¹)⁻¹ := by group
        _ = s * c * s⁻¹ := by rw [hs1, hc1]
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    calc t * (s * c * s⁻¹) = t * (s * c * s⁻¹) * t⁻¹ * t := by group
      _ = (s * c * s⁻¹) * t := by rw [hconj]
  have hCT3 : C ⊓ T3 = ⊥ := by
    apply le_antisymm _ bot_le
    intro x hx
    exact Subgroup.mem_bot.mpr (h.T3_inf_K x hx.2 hx.1.1)
  have hcardR : Nat.card R = Nat.card C * 8 := by
    show Nat.card (C ⊔ T3 : Subgroup H) = Nat.card C * 8
    rw [card_sup_eq_mul (H := C) (K := T3) hT3C hCT3,
      show Nat.card ↥T3 = 8 from h.card_T3]
  have hRcent : R ≤ centralizer ({t} : Set H) :=
    sup_le (fun x hx => hx.2) h.T3_cent_t
  have hRVc : R ≤ z4iVc K t τ l :=
    sup_le (fun x hx => K_le_Vc K t τ l hx.1) (T3_le_Vc K t τ l)
  have hRpgrp : IsPGroup 2 R := (h.Vc_pgroup).to_le hRVc
  have hle128 : Nat.card R ≤ 128 := h.bound R hRpgrp hRcent
  have hCle16 : Nat.card C ≤ 16 := by
    rw [hcardR] at hle128
    omega
  have hBC : B ≤ C := by
    intro b hb
    refine ⟨h.Q_le_K (h.B_le_Q hb), Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact h.B_cent_t b hb
  have hCB : C = B := (Subgroup.eq_of_le_of_card_ge (H := B) (K := C) hBC
    (by rw [h.card_B]; exact hCle16)).symm
  intro x hx hxt
  have hxC : x ∈ C := by
    refine ⟨hx, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact hxt
  rw [hCB] at hxC
  exact hxC

theorem comm_t_mem_Y_iff (h : ZEData Q Y V V' B K ρ t τ l) {x : H} (hx : x ∈ K) :
    ⁅t, x⁆ ∈ Y ↔ x ∈ Q := by
  constructor
  · intro hxY
    obtain ⟨w, hwY, hwreg⟩ :=
      z4i_fpl h.t_sq h.Y_sq (fun y hy => h.normal_Y t y hy) (t_regular_Y h) hxY
    have hzK : w⁻¹ * x ∈ K :=
      K.mul_mem (K.inv_mem (h.Q_le_K (h.toZIKData.Y_le_Q hwY))) hx
    have hzt : t * (w⁻¹ * x) = (w⁻¹ * x) * t := by
      calc t * (w⁻¹ * x) = t * (w⁻¹ * x) * t⁻¹ * t := by group
        _ = (w⁻¹ * x) * t := by rw [hwreg]
    have hzB : w⁻¹ * x ∈ B := cent_K_t h _ hzK hzt
    have hxw : x = w * (w⁻¹ * x) := by group
    rw [hxw]
    exact Q.mul_mem (h.toZIKData.Y_le_Q hwY) (h.B_le_Q hzB)
  · intro hxQ
    obtain ⟨b, hb, y, hy, hxeq⟩ := h.toZIKData.exists_mul_BY x hxQ
    have hcomm : ⁅t, b * y⁆ = b * ⁅t, y⁆ * b⁻¹ := by
      calc ⁅t, b * y⁆ = t * b * y * t⁻¹ * y⁻¹ * b⁻¹ := by
            simp only [commutatorElement_def, mul_inv_rev]
            group
        _ = b * t * y * t⁻¹ * y⁻¹ * b⁻¹ := by rw [h.B_cent_t b hb]
        _ = b * ⁅t, y⁆ * b⁻¹ := by
            simp only [commutatorElement_def, mul_inv_rev]
            group
    have hy1 : ⁅t, y⁆ ∈ Y := by
      rw [commutatorElement_def]
      exact Y.mul_mem (h.normal_Y t y hy) (Y.inv_mem hy)
    have hconj : b * ⁅t, y⁆ * b⁻¹ = ⁅t, y⁆ := by
      rw [h.Q_comm b (h.B_le_Q hb) ⁅t, y⁆ (h.toZIKData.Y_le_Q hy1)]
      group
    rw [hxeq, hcomm, hconj]
    exact hy1

theorem t_regular_KY (h : ZEData Q Y V V' B K ρ t τ l) : ActsRegularly t Y K := by
  have hYK : Y ≤ K := h.toZIKData.Y_le_Q.trans h.Q_le_K
  refine (actsRegularly_iff_card (N := Y) (M := K) (orderOf_t h) hYK ?_ ?_ ?_ ?_).mpr ?_
  · intro x hx y hy
    exact h.toZIKData.V_le_Y (by
      rw [commutatorElement_def]
      exact h.toZIKData.comm_mem_V x hx y hy)
  · intro x hx
    exact h.toZIKData.sq_mem_Y x hx
  · intro g hg
    exact h.normal_Y t g hg
  · intro g hg
    exact h.t_norm_K g hg
  · have hset : Nat.card {g : H // g ∈ K ∧ ⁅t, g⁆ ∈ Y} = Nat.card ↥Q := by
      apply Nat.card_congr
      refine Equiv.subtypeEquivRight ?_
      intro g
      constructor
      · rintro ⟨hgK, hgY⟩
        exact (comm_t_mem_Y_iff h hgK).mp hgY
      · intro hgQ
        exact ⟨h.Q_le_K hgQ, (comm_t_mem_Y_iff h (h.Q_le_K hgQ)).mpr hgQ⟩
    rw [hset, h.card_Q, h.toZIKData.card_K, h.toZIKData.card_Y]
    norm_num

theorem invol_tK (h : ZEData Q Y V V' B K ρ t τ l) :
    ∀ j : H, (∃ s ∈ K, j = t * s) → j * j = 1 → ∃ w ∈ K, j = w * t * w⁻¹ := by
  have hYK : Y ≤ K := h.toZIKData.Y_le_Q.trans h.Q_le_K
  have hcommK : ∀ x ∈ K, ∀ y ∈ K, ⁅x, y⁆ ∈ Y := by
    intro x hx y hy
    exact h.toZIKData.V_le_Y (by
      rw [commutatorElement_def]
      exact h.toZIKData.comm_mem_V x hx y hy)
  intro j hj hjj
  by_cases hj1 : j = 1
  · exfalso
    obtain ⟨s, hs, hjs⟩ := hj
    have hts : t * s = 1 := by rw [hj1] at hjs; exact hjs.symm
    exact h.t_not_mem_K (by rw [eq_inv_of_mul_eq_one_left hts]; exact K.inv_mem hs)
  · exact z4i_invol_coset (Z := H) (K := K) (Y := Y) (u := t) h.t_sq (t_ne_one h) hYK hcommK
      (h.toZIKData.sq_mem_Y) h.toZIKData.Y_comm h.Y_sq h.t_norm_K
      (fun y hy => h.normal_Y t y hy) (t_regular_Y h) (t_regular_KY h) j hj hjj hj1

end ZEData

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
