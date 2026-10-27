module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4IZ1

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped commutatorElement

variable {H : Type} [Group H] [Finite H]

namespace ZEData

variable {Q Y V V' B K : Subgroup H} {ρ t τ l : H}

private lemma tau_cent_Y (h : ZEData Q Y V V' B K ρ t τ l) {y : H} (hy : y ∈ Y) :
    τ * y * τ⁻¹ = y := by
  rw [h.tau_inv y (h.Y_le_Q hy), inv_eq_of_mul_eq_one_right (h.Y_sq y hy)]

private lemma ttau_sq (h : ZEData Q Y V V' B K ρ t τ l) : (t * τ) * (t * τ) = 1 := by
  calc (t * τ) * (t * τ) = t * (τ * t) * τ := by group
    _ = t * (t * τ) * τ := by rw [← h.t_tau]
    _ = (t * t) * (τ * τ) := by group
    _ = 1 := by rw [h.t_sq, h.tau_sq, one_mul]

private lemma ttau_comm_eq (h : ZEData Q Y V V' B K ρ t τ l) {y : H} (hy : y ∈ Y) :
    ⁅t * τ, y⁆ = ⁅t, y⁆ := by
  have hstep : (t * τ) * y * (t * τ)⁻¹ = t * y * t⁻¹ := by
    calc (t * τ) * y * (t * τ)⁻¹ = t * (τ * y * τ⁻¹) * t⁻¹ := by group
      _ = t * y * t⁻¹ := by rw [tau_cent_Y h hy]
  rw [commutatorElement_def, commutatorElement_def, hstep]

private lemma ttau_norm_K (h : ZEData Q Y V V' B K ρ t τ l) {k : H} (hk : k ∈ K) :
    (t * τ) * k * (t * τ)⁻¹ ∈ K := by
  rw [show (t * τ) * k * (t * τ)⁻¹ = t * (τ * k * τ⁻¹) * t⁻¹ by group]
  exact h.t_norm_K _ (h.tau_norm_K k hk)

private lemma taul_sq (h : ZEData Q Y V V' B K ρ t τ l) : (τ * l) * (τ * l) = 1 := by
  calc (τ * l) * (τ * l) = τ * (l * τ) * l := by group
    _ = τ * (τ * l) * l := by rw [← h.tau_l]
    _ = (τ * τ) * (l * l) := by group
    _ = 1 := by rw [h.tau_sq, h.l_sq, one_mul]

private lemma taul_norm_K (h : ZEData Q Y V V' B K ρ t τ l) {k : H} (hk : k ∈ K) :
    (τ * l) * k * (τ * l)⁻¹ ∈ K := by
  rw [show (τ * l) * k * (τ * l)⁻¹ = τ * (l * k * l⁻¹) * τ⁻¹ by group]
  exact h.tau_norm_K _ (h.l_norm_K k hk)

private lemma rho_conj_t (h : ZEData Q Y V V' B K ρ t τ l) : ρ * t * ρ⁻¹ = t := by
  rw [← h.t_rho]; group

private lemma rho_conj_tau (h : ZEData Q Y V V' B K ρ t τ l) : ρ * τ * ρ⁻¹ = τ := by
  rw [← h.tau_rho]; group

private lemma taul_rho (h : ZEData Q Y V V' B K ρ t τ l) :
    (τ * l) * ρ * (τ * l)⁻¹ = ρ⁻¹ := by
  have hτρ : τ * ρ * τ⁻¹ = ρ := by rw [h.tau_rho]; group
  calc (τ * l) * ρ * (τ * l)⁻¹ = τ * (l * ρ * l⁻¹) * τ⁻¹ := by group
    _ = τ * ρ⁻¹ * τ⁻¹ := by rw [h.l_rho]
    _ = (τ * ρ * τ⁻¹)⁻¹ := by group
    _ = ρ⁻¹ := by rw [hτρ]

private lemma rho_comm_ttau (h : ZEData Q Y V V' B K ρ t τ l) :
    ρ * (t * τ) * ρ⁻¹ = t * τ := by
  calc ρ * (t * τ) * ρ⁻¹ = (ρ * t * ρ⁻¹) * (ρ * τ * ρ⁻¹) := by group
    _ = t * τ := by rw [rho_conj_t h, rho_conj_tau h]

private lemma rho_mem_z4iCuK (h : ZEData Q Y V V' B K ρ t τ l) {z : H}
    (hz : z ∈ z4iCuK K Y (t * τ) h.K_cent_Y) :
    ρ * z * ρ⁻¹ ∈ z4iCuK K Y (t * τ) h.K_cent_Y := by
  rw [mem_z4iCuK (K := K) (Y := Y) (u := t * τ) h.K_cent_Y] at hz ⊢
  refine ⟨h.rho_norm_K z hz.1, ?_⟩
  have hconj : ⁅t * τ, ρ * z * ρ⁻¹⁆ = ρ * ⁅t * τ, z⁆ * ρ⁻¹ := by
    have h1 := conjugate_commutatorElement (g₁ := t * τ) (g₂ := z) (g₃ := ρ)
    rw [rho_comm_ttau h] at h1
    exact h1.symm
  rw [hconj]
  exact h.rho_norm_Y _ hz.2

private lemma ttau_not_mem_K (h : ZEData Q Y V V' B K ρ t τ l) : t * τ ∉ K := by
  intro hK
  have hword : t ^ ((1 : Fin 2) : ℕ) * τ ^ ((1 : Fin 2) : ℕ) * l ^ ((0 : Fin 2) : ℕ)
      = t * τ := by simp
  have hbad := (h.word_mem_K (a := (1 : Fin 2)) (b := (1 : Fin 2)) (c := (0 : Fin 2))
    (by rw [hword]; exact hK)).1
  exact absurd hbad (by decide)

private lemma l_not_mem_K (h : ZEData Q Y V V' B K ρ t τ l) : l ∉ K := by
  intro hK
  have hword : t ^ ((0 : Fin 2) : ℕ) * τ ^ ((0 : Fin 2) : ℕ) * l ^ ((1 : Fin 2) : ℕ)
      = l := by simp
  have hbad := (h.word_mem_K (a := (0 : Fin 2)) (b := (0 : Fin 2)) (c := (1 : Fin 2))
    (by rw [hword]; exact hK)).2.2
  exact absurd hbad (by decide)

private lemma taul_not_mem_K (h : ZEData Q Y V V' B K ρ t τ l) : τ * l ∉ K := by
  intro hK
  have hword : t ^ ((0 : Fin 2) : ℕ) * τ ^ ((1 : Fin 2) : ℕ) * l ^ ((1 : Fin 2) : ℕ)
      = τ * l := by simp
  have hbad := (h.word_mem_K (a := (0 : Fin 2)) (b := (1 : Fin 2)) (c := (1 : Fin 2))
    (by rw [hword]; exact hK)).2.1
  exact absurd hbad (by decide)

private lemma ttau_ne_one (h : ZEData Q Y V V' B K ρ t τ l) : t * τ ≠ 1 :=
  fun h1 => ttau_not_mem_K h (by rw [h1]; exact K.one_mem)

private lemma l_ne_one (h : ZEData Q Y V V' B K ρ t τ l) : l ≠ 1 :=
  fun h1 => l_not_mem_K h (by rw [h1]; exact K.one_mem)

private lemma taul_ne_one (h : ZEData Q Y V V' B K ρ t τ l) : τ * l ≠ 1 :=
  fun h1 => taul_not_mem_K h (by rw [h1]; exact K.one_mem)

theorem ttau_dich (h : ZEData Q Y V V' B K ρ t τ l) :
    (∀ x ∈ K, ⁅t * τ, x⁆ ∈ Y) ∨ ActsRegularly (t * τ) Y K := by
  let Z : Subgroup H := z4iCuK K Y (t * τ) h.K_cent_Y
  have hQZ : Q ≤ Z := by
    intro x hx
    change x ∈ z4iCuK K Y (t * τ) h.K_cent_Y
    rw [mem_z4iCuK (K := K) (Y := Y) (u := t * τ) h.K_cent_Y]
    refine ⟨h.Q_le_K hx, ?_⟩
    have htx : ⁅t, x⁻¹⁆ ∈ Y :=
      (h.comm_t_mem_Y_iff (x := x⁻¹) (K.inv_mem (h.Q_le_K hx))).mpr (Q.inv_mem hx)
    have hsq : (x ^ 2)⁻¹ ∈ Y := Y.inv_mem (h.V_le_Y (h.sq_mem_V x hx))
    have hcx : ⁅t * τ, x⁆ = ⁅t, x⁻¹⁆ * (x ^ 2)⁻¹ := by
      have hstep : (t * τ) * x * (t * τ)⁻¹ = t * x⁻¹ * t⁻¹ := by
        calc (t * τ) * x * (t * τ)⁻¹ = t * (τ * x * τ⁻¹) * t⁻¹ := by group
          _ = t * x⁻¹ * t⁻¹ := by rw [h.tau_inv x hx]
      rw [commutatorElement_def, commutatorElement_def, hstep, pow_two]
      group
    rw [hcx]
    exact Y.mul_mem htx hsq
  have hZK : Z ≤ K := by
    intro z hz
    exact ((mem_z4iCuK (K := K) (Y := Y) (u := t * τ) h.K_cent_Y).mp hz).1
  have hρZ : ∀ z ∈ Z, ρ * z * ρ⁻¹ ∈ Z := fun z hz => rho_mem_z4iCuK h hz
  rcases z4i_between (Q := Q) (K := K) (Z := Z) (ρ := ρ) h.rho_pow_three h.Q_le_K hQZ
    hZK h.relIndex_K h.Q_normal_K h.rho_norm_Q h.rho_norm_K hρZ h.rho_fpf_KQ with hZQ | hZK'
  · right
    have hu2 : (t * τ) * (t * τ) = 1 := ttau_sq h
    have hord : orderOf (t * τ) = 2 :=
      orderOf_eq_prime (p := 2) (by rw [pow_two]; exact hu2) (ttau_ne_one h)
    refine (actsRegularly_iff_card hord (h.Y_le_Q.trans h.Q_le_K) ?_ h.sq_mem_Y ?_ ?_).mpr ?_
    · intro x hx y hy
      exact h.V_le_Y (h.comm_mem_V x hx y hy)
    · intro g hg
      exact h.normal_Y (t * τ) g hg
    · intro g hg
      exact ttau_norm_K h hg
    · have hcardZ : Nat.card {g : H // g ∈ K ∧ ⁅t * τ, g⁆ ∈ Y} = Nat.card Z :=
        Nat.card_congr (Equiv.subtypeEquivRight
          (fun g => (mem_z4iCuK (K := K) (Y := Y) (u := t * τ) h.K_cent_Y).symm))
      rw [hcardZ, hZQ, h.card_Q, h.card_K, h.card_Y]
      norm_num
  · left
    intro x hx
    have hxZ : x ∈ Z := by rw [hZK']; exact hx
    exact ((mem_z4iCuK (K := K) (Y := Y) (u := t * τ) h.K_cent_Y).mp hxZ).2

theorem invol_ttauK (h : ZEData Q Y V V' B K ρ t τ l) (hreg : ActsRegularly (t * τ) Y K) :
    ∀ j : H, (∃ s ∈ K, j = t * τ * s) → j * j = 1 → ∃ w ∈ K, j = w * (t * τ) * w⁻¹ := by
  intro j hj hjj
  refine z4i_invol_coset (K := K) (Y := Y) (u := t * τ) (ttau_sq h) (ttau_ne_one h)
    (h.Y_le_Q.trans h.Q_le_K) ?_ h.sq_mem_Y (fun x hx y hy => h.Y_comm x hx y hy) h.Y_sq
    (fun k hk => ttau_norm_K h hk) (fun y hy => h.normal_Y (t * τ) y hy) ?_ hreg j hj hjj ?_
  · intro x hx y hy
    exact h.V_le_Y (h.comm_mem_V x hx y hy)
  · intro x hx hxbot
    have hx' : ⁅t, x⁆ ∈ (⊥ : Subgroup H) := by rwa [ttau_comm_eq h hx] at hxbot
    obtain ⟨u, hu, hu'⟩ := h.t_regular_Y x hx hx'
    exact ⟨u, hu, by rwa [ttau_comm_eq h hu]⟩
  · intro hj1
    obtain ⟨s, hs, hjs⟩ := hj
    apply ttau_not_mem_K h
    have h1 : (t * τ) * s = 1 := by rw [← hjs, hj1]
    have h2 : t * τ = s⁻¹ := mul_eq_one_iff_eq_inv.mp h1
    rw [h2]
    exact K.inv_mem hs

theorem invol_lK (h : ZEData Q Y V V' B K ρ t τ l) :
    ∀ j : H, (∃ s ∈ K, j = l * s) → j * j = 1 → ∃ w ∈ K, j = w * l * w⁻¹ := by
  intro j hj hjj
  refine z4i_invol_coset (K := K) (Y := Y) (u := l) h.l_sq (l_ne_one h)
    (h.Y_le_Q.trans h.Q_le_K) ?_ h.sq_mem_Y (fun x hx y hy => h.Y_comm x hx y hy) h.Y_sq
    h.l_norm_K (fun y hy => h.normal_Y l y hy) ?_ ?_ j hj hjj ?_
  · intro x hx y hy
    exact h.V_le_Y (h.comm_mem_V x hx y hy)
  · exact z4i_s3_regular h.rho_pow_three h.l_sq h.l_rho bot_le
      (fun x hx y hy => Subgroup.mem_bot.mpr (by rw [h.Y_comm x hx y hy]; group))
      (fun x hx => Subgroup.mem_bot.mpr (by rw [pow_two]; exact h.Y_sq x hx))
      (fun n hn => Subgroup.mem_bot.mpr (by rw [Subgroup.mem_bot.mp hn]; group))
      h.rho_norm_Y
      (fun n hn => Subgroup.mem_bot.mpr (by rw [Subgroup.mem_bot.mp hn]; group))
      (fun y hy => h.normal_Y l y hy)
      (fun x hx hxN => Subgroup.mem_bot.mpr
        (h.rho_fpf_Q x (h.Y_le_Q hx) (mul_inv_eq_one.mp (Subgroup.mem_bot.mp hxN))))
  · exact z4i_s3_regular h.rho_pow_three h.l_sq h.l_rho (h.Y_le_Q.trans h.Q_le_K)
      (fun x hx y hy => h.V_le_Y (h.comm_mem_V x hx y hy))
      h.sq_mem_Y h.rho_norm_Y h.rho_norm_K (fun n hn => h.normal_Y l n hn)
      h.l_norm_K h.fpf_KY
  · intro hj1
    obtain ⟨s, hs, hjs⟩ := hj
    apply l_not_mem_K h
    have h1 : l * s = 1 := by rw [← hjs, hj1]
    have h2 : l = s⁻¹ := mul_eq_one_iff_eq_inv.mp h1
    rw [h2]
    exact K.inv_mem hs

theorem invol_taulK (h : ZEData Q Y V V' B K ρ t τ l) :
    ∀ j : H, (∃ s ∈ K, j = τ * l * s) → j * j = 1 → ∃ w ∈ K, j = w * (τ * l) * w⁻¹ := by
  intro j hj hjj
  refine z4i_invol_coset (K := K) (Y := Y) (u := τ * l) (taul_sq h) (taul_ne_one h)
    (h.Y_le_Q.trans h.Q_le_K) ?_ h.sq_mem_Y (fun x hx y hy => h.Y_comm x hx y hy) h.Y_sq
    (fun k hk => taul_norm_K h hk) (fun y hy => h.normal_Y (τ * l) y hy) ?_ ?_ j hj hjj ?_
  · intro x hx y hy
    exact h.V_le_Y (h.comm_mem_V x hx y hy)
  · exact z4i_s3_regular h.rho_pow_three (taul_sq h) (taul_rho h) bot_le
      (fun x hx y hy => Subgroup.mem_bot.mpr (by rw [h.Y_comm x hx y hy]; group))
      (fun x hx => Subgroup.mem_bot.mpr (by rw [pow_two]; exact h.Y_sq x hx))
      (fun n hn => Subgroup.mem_bot.mpr (by rw [Subgroup.mem_bot.mp hn]; group))
      h.rho_norm_Y
      (fun n hn => Subgroup.mem_bot.mpr (by rw [Subgroup.mem_bot.mp hn]; group))
      (fun y hy => h.normal_Y (τ * l) y hy)
      (fun x hx hxN => Subgroup.mem_bot.mpr
        (h.rho_fpf_Q x (h.Y_le_Q hx) (mul_inv_eq_one.mp (Subgroup.mem_bot.mp hxN))))
  · exact z4i_s3_regular h.rho_pow_three (taul_sq h) (taul_rho h) (h.Y_le_Q.trans h.Q_le_K)
      (fun x hx y hy => h.V_le_Y (h.comm_mem_V x hx y hy))
      h.sq_mem_Y h.rho_norm_Y h.rho_norm_K (fun y hy => h.normal_Y (τ * l) y hy)
      (fun k hk => taul_norm_K h hk) h.fpf_KY
  · intro hj1
    obtain ⟨s, hs, hjs⟩ := hj
    apply taul_not_mem_K h
    have h1 : (τ * l) * s = 1 := by rw [← hjs, hj1]
    have h2 : τ * l = s⁻¹ := mul_eq_one_iff_eq_inv.mp h1
    rw [h2]
    exact K.inv_mem hs

theorem tau_comm_K_mod_Q (h : ZEData Q Y V V' B K ρ t τ l) :
    ∀ x ∈ K, τ * x * τ⁻¹ * x⁻¹ ∈ Q := by
  intro x hx
  exact z4i_comm_invol_trivial (N := Q) (M := K) (ρ := ρ) (τ := τ) h.rho_pow_three
    h.Q_le_K h.Q_normal_K h.rho_norm_Q h.rho_norm_K h.relIndex_K h.rho_fpf_KQ
    h.tau_sq h.tau_rho (fun n hn => h.normal_Q τ n hn) h.tau_norm_K (x := x) hx

end ZEData

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
