module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4JA1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4IR5A

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X] {N Q Y V V' B : Subgroup X}
  {ρ t τ l y z v₁ v₂ : X} [N.Normal]

private lemma zj_isPGroup_Q (h : Z4JData N Q Y V V' B ρ t τ l y z v₁ v₂) :
    IsPGroup 2 Q :=
  IsPGroup.of_card (n := 6) (by rw [h.card_Q]; norm_num)

private lemma zj_V_le_Q (h : Z4JData N Q Y V V' B ρ t τ l y z v₁ v₂) : V ≤ Q := by
  calc V ≤ V ⊔ V' := le_sup_left
    _ = Y := h.Y_eq.symm
    _ ≤ Q := h.Y_le_Q

private lemma zj_V'_le_Q (h : Z4JData N Q Y V V' B ρ t τ l y z v₁ v₂) : V' ≤ Q := by
  calc V' ≤ V ⊔ V' := le_sup_right
    _ = Y := h.Y_eq.symm
    _ ≤ Q := h.Y_le_Q

private lemma zj_y_mem_V (h : Z4JData N Q Y V V' B ρ t τ l y z v₁ v₂) : y ∈ V := by
  rw [h.V_eq]
  exact Subgroup.subset_closure (Set.mem_insert _ _)

private lemma zj_z_mem_V (h : Z4JData N Q Y V V' B ρ t τ l y z v₁ v₂) : z ∈ V := by
  rw [h.V_eq]
  exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))

private lemma zj_y_mem_Y (h : Z4JData N Q Y V V' B ρ t τ l y z v₁ v₂) : y ∈ Y := by
  rw [h.Y_eq]
  exact Subgroup.mem_sup_left (zj_y_mem_V h)

private lemma zj_z_mem_Y (h : Z4JData N Q Y V V' B ρ t τ l y z v₁ v₂) : z ∈ Y := by
  rw [h.Y_eq]
  exact Subgroup.mem_sup_left (zj_z_mem_V h)

private lemma zj_v₁_mem_V' (h : Z4JData N Q Y V V' B ρ t τ l y z v₁ v₂) : v₁ ∈ V' := by
  rw [h.V'_eq]
  exact Subgroup.subset_closure (Set.mem_insert _ _)

private lemma zj_v₂_mem_V' (h : Z4JData N Q Y V V' B ρ t τ l y z v₁ v₂) : v₂ ∈ V' := by
  rw [h.V'_eq]
  exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))

private lemma zj_v₁_mem_Y (h : Z4JData N Q Y V V' B ρ t τ l y z v₁ v₂) : v₁ ∈ Y := by
  rw [h.Y_eq]
  exact Subgroup.mem_sup_right (zj_v₁_mem_V' h)

private lemma zj_v₂_mem_Y (h : Z4JData N Q Y V V' B ρ t τ l y z v₁ v₂) : v₂ ∈ Y := by
  rw [h.Y_eq]
  exact Subgroup.mem_sup_right (zj_v₂_mem_V' h)

private lemma zj_Q_inf_N (h : Z4JData N Q Y V V' B ρ t τ l y z v₁ v₂) : Q ⊓ N = ⊥ :=
  z4i_inf_N_eq_bot N h.odd_N (zj_isPGroup_Q h)

private lemma zj_Q_comm (h : Z4JData N Q Y V V' B ρ t τ l y z v₁ v₂) :
    ∀ a ∈ Q.map (z4iπ N), ∀ b ∈ Q.map (z4iπ N), a * b = b * a := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  simp only [← map_mul, h.Q_comm a ha b hb]

private lemma zj_card_Q (h : Z4JData N Q Y V V' B ρ t τ l y z v₁ v₂) :
    Nat.card (Q.map (z4iπ N)) = 64 := by
  rw [z4i_card_map N h.odd_N (zj_isPGroup_Q h), h.card_Q]

private lemma zj_cent_Q (h : Z4JData N Q Y V V' B ρ t τ l y z v₁ v₂) :
    ∀ g : X ⧸ N, (∀ q ∈ Q.map (z4iπ N), g * q = q * g) → g ∈ Q.map (z4iπ N) := by
  intro g hg
  obtain ⟨g₀, rfl⟩ := z4iπ_surjective N g
  refine (z4iπ_mem_map_iff N).mpr (h.cent_Q g₀ ?_)
  intro q hq
  exact z4i_commute_of_map N (zj_Q_inf_N h) (fun x hx => h.normal_Q g₀ x hx) hq
    (hg (z4iπ N q) (Subgroup.mem_map_of_mem (z4iπ N) hq))

private lemma zj_Q_eq (h : Z4JData N Q Y V V' B ρ t τ l y z v₁ v₂) :
    Q.map (z4iπ N) = B.map (z4iπ N) ⊔ V'.map (z4iπ N) := by
  rw [← Subgroup.map_sup, ← h.Q_eq]

private lemma zj_B_le_Q (h : Z4JData N Q Y V V' B ρ t τ l y z v₁ v₂) :
    B.map (z4iπ N) ≤ Q.map (z4iπ N) :=
  Subgroup.map_mono h.B_le_Q

private lemma zj_Y_le_Q (h : Z4JData N Q Y V V' B ρ t τ l y z v₁ v₂) :
    Y.map (z4iπ N) ≤ Q.map (z4iπ N) :=
  Subgroup.map_mono h.Y_le_Q

private lemma zj_Y_eq (h : Z4JData N Q Y V V' B ρ t τ l y z v₁ v₂) :
    Y.map (z4iπ N) = V.map (z4iπ N) ⊔ V'.map (z4iπ N) := by
  rw [← Subgroup.map_sup, ← h.Y_eq]

private lemma zj_V_inf_V' (h : Z4JData N Q Y V V' B ρ t τ l y z v₁ v₂) :
    V.map (z4iπ N) ⊓ V'.map (z4iπ N) = ⊥ := by
  have h1 := z4i_map_inf N h.odd_N (zj_isPGroup_Q h) (zj_V_le_Q h) (zj_V'_le_Q h)
  rw [h.V_inf_V', Subgroup.map_bot] at h1
  exact h1.symm

private lemma zj_card_V (h : Z4JData N Q Y V V' B ρ t τ l y z v₁ v₂) :
    Nat.card (V.map (z4iπ N)) = 4 := by
  rw [z4i_card_map N h.odd_N ((zj_isPGroup_Q h).to_le (zj_V_le_Q h)), h.card_V]

private lemma zj_card_V' (h : Z4JData N Q Y V V' B ρ t τ l y z v₁ v₂) :
    Nat.card (V'.map (z4iπ N)) = 4 := by
  rw [z4i_card_map N h.odd_N ((zj_isPGroup_Q h).to_le (zj_V'_le_Q h)), h.card_V']

private lemma zj_card_B (h : Z4JData N Q Y V V' B ρ t τ l y z v₁ v₂) :
    Nat.card (B.map (z4iπ N)) = 16 := by
  rw [z4i_card_map N h.odd_N ((zj_isPGroup_Q h).to_le h.B_le_Q), h.card_B]

private lemma zj_sq_mem_V (h : Z4JData N Q Y V V' B ρ t τ l y z v₁ v₂) :
    ∀ q ∈ Q.map (z4iπ N), q ^ 2 ∈ V.map (z4iπ N) := by
  rintro _ ⟨q, hq, rfl⟩
  simpa only [map_pow] using Subgroup.mem_map_of_mem (z4iπ N) (h.sq_mem_V q hq)

private lemma zj_Y_sq (h : Z4JData N Q Y V V' B ρ t τ l y z v₁ v₂) :
    ∀ u ∈ Y.map (z4iπ N), u * u = 1 := by
  rintro _ ⟨u, hu, rfl⟩
  rw [← map_mul, h.Y_sq u hu, map_one]

private lemma zj_Y_mem (h : Z4JData N Q Y V V' B ρ t τ l y z v₁ v₂) :
    ∀ q ∈ Q.map (z4iπ N), q * q = 1 → q ∈ Y.map (z4iπ N) := by
  rintro _ ⟨q, hq, rfl⟩ hq2
  have hq2N : q * q ∈ N := by
    rw [← z4iπ_ker N]
    exact MonoidHom.mem_ker.2 (by rw [map_mul, hq2])
  have hmem : q * q ∈ (⊥ : Subgroup X) := by
    rw [← zj_Q_inf_N h]
    exact ⟨Q.mul_mem hq hq, hq2N⟩
  have hqq : q * q = 1 := Subgroup.mem_bot.1 hmem
  exact Subgroup.mem_map_of_mem (z4iπ N) (h.Y_mem q hq hqq)

private lemma zj_normal {A : Subgroup X}
    (hA : ∀ g x : X, x ∈ A → g * x * g⁻¹ ∈ A) :
    ∀ g x : X ⧸ N, x ∈ A.map (z4iπ N) → g * x * g⁻¹ ∈ A.map (z4iπ N) := by
  intro g x hx
  obtain ⟨g0, rfl⟩ := z4iπ_surjective N g
  obtain ⟨x0, hx0, rfl⟩ := hx
  rw [← map_mul, ← map_inv, ← map_mul]
  exact Subgroup.mem_map_of_mem (z4iπ N) (hA g0 x0 hx0)

private lemma zj_V_eq (h : Z4JData N Q Y V V' B ρ t τ l y z v₁ v₂) :
    V.map (z4iπ N) = closure ({z4iπ N y, z4iπ N z} : Set (X ⧸ N)) := by
  rw [h.V_eq, MonoidHom.map_closure, Set.image_pair]

private lemma zj_V'_eq (h : Z4JData N Q Y V V' B ρ t τ l y z v₁ v₂) :
    V'.map (z4iπ N) = closure ({z4iπ N v₁, z4iπ N v₂} : Set (X ⧸ N)) := by
  rw [h.V'_eq, MonoidHom.map_closure, Set.image_pair]

private lemma zj_y_ne_one (h : Z4JData N Q Y V V' B ρ t τ l y z v₁ v₂) :
    z4iπ N y ≠ 1 :=
  z4i_map_ne_one N h.odd_N (h.Y_sq y (zj_y_mem_Y h)) h.y_ne_one

private lemma zj_z_ne_one (h : Z4JData N Q Y V V' B ρ t τ l y z v₁ v₂) :
    z4iπ N z ≠ 1 :=
  z4i_map_ne_one N h.odd_N (h.Y_sq z (zj_z_mem_Y h)) h.z_ne_one

private lemma zj_v₁_ne_one (h : Z4JData N Q Y V V' B ρ t τ l y z v₁ v₂) :
    z4iπ N v₁ ≠ 1 :=
  z4i_map_ne_one N h.odd_N (h.Y_sq v₁ (zj_v₁_mem_Y h)) h.v₁_ne_one

private lemma zj_v₂_ne_one (h : Z4JData N Q Y V V' B ρ t τ l y z v₁ v₂) :
    z4iπ N v₂ ≠ 1 :=
  z4i_map_ne_one N h.odd_N (h.Y_sq v₂ (zj_v₂_mem_Y h)) h.v₂_ne_one

private lemma zj_y_ne_z (h : Z4JData N Q Y V V' B ρ t τ l y z v₁ v₂) :
    z4iπ N y ≠ z4iπ N z := by
  intro heq
  exact h.y_ne_z (z4iπ_injOn N h.odd_N (zj_isPGroup_Q h)
    (zj_V_le_Q h (zj_y_mem_V h)) (zj_V_le_Q h (zj_z_mem_V h)) heq)

private lemma zj_v₁_ne_v₂ (h : Z4JData N Q Y V V' B ρ t τ l y z v₁ v₂) :
    z4iπ N v₁ ≠ z4iπ N v₂ := by
  intro heq
  exact h.v₁_ne_v₂ (z4iπ_injOn N h.odd_N (zj_isPGroup_Q h)
    (zj_V'_le_Q h (zj_v₁_mem_V' h)) (zj_V'_le_Q h (zj_v₂_mem_V' h)) heq)

private lemma zj_rho_pow_three (h : Z4JData N Q Y V V' B ρ t τ l y z v₁ v₂) :
    (z4iπ N ρ) ^ 3 = 1 := by
  have h3 : z4iπ N (ρ ^ 3) = 1 := by rw [h.rho_pow_three, map_one]
  simpa only [map_pow] using h3

private lemma zj_norm {A : Subgroup X} {a : X} (ha : ∀ x ∈ A, a * x * a⁻¹ ∈ A) :
    ∀ x ∈ A.map (z4iπ N), z4iπ N a * x * (z4iπ N a)⁻¹ ∈ A.map (z4iπ N) := by
  rintro _ ⟨x, hx, rfl⟩
  rw [← map_mul, ← map_inv, ← map_mul]
  exact Subgroup.mem_map_of_mem (z4iπ N) (ha x hx)

private lemma zj_rho_fpf_Q (h : Z4JData N Q Y V V' B ρ t τ l y z v₁ v₂) :
    ∀ q ∈ Q.map (z4iπ N), z4iπ N ρ * q * (z4iπ N ρ)⁻¹ = q → q = 1 := by
  rintro _ ⟨q, hq, rfl⟩ hq'
  have hcomm : z4iπ N ρ * z4iπ N q = z4iπ N q * z4iπ N ρ := by
    have h1 : (z4iπ N ρ * z4iπ N q * (z4iπ N ρ)⁻¹) * z4iπ N ρ =
        z4iπ N q * z4iπ N ρ := by rw [hq']
    calc z4iπ N ρ * z4iπ N q
        = (z4iπ N ρ * z4iπ N q * (z4iπ N ρ)⁻¹) * z4iπ N ρ := by group
      _ = z4iπ N q * z4iπ N ρ := h1
  have hρq : ρ * q = q * ρ :=
    z4i_commute_of_map N (zj_Q_inf_N h) h.rho_norm_Q hq hcomm
  have hfix : ρ * q * ρ⁻¹ = q := by rw [hρq]; group
  have hq1 : q = 1 := h.rho_fpf_Q q hq hfix
  rw [hq1, map_one]

private lemma zj_tau_inv (h : Z4JData N Q Y V V' B ρ t τ l y z v₁ v₂) :
    ∀ q ∈ Q.map (z4iπ N), z4iπ N τ * q * (z4iπ N τ)⁻¹ = q⁻¹ := by
  rintro _ ⟨q, hq, rfl⟩
  rw [← map_mul, ← map_inv, ← map_mul, h.tau_inv q hq, map_inv]

private lemma zj_tau_not_mem_Q (h : Z4JData N Q Y V V' B ρ t τ l y z v₁ v₂) :
    z4iπ N τ ∉ Q.map (z4iπ N) :=
  fun hmem => h.tau_not_mem_Q ((z4iπ_mem_map_iff N (A := Q) (x := τ)).mp hmem)

private lemma zj_t_ne_one (h : Z4JData N Q Y V V' B ρ t τ l y z v₁ v₂) :
    z4iπ N t ≠ 1 :=
  z4i_map_ne_one N h.odd_N h.t_sq h.t_ne_one

private lemma zj_t_sq (h : Z4JData N Q Y V V' B ρ t τ l y z v₁ v₂) :
    z4iπ N t * z4iπ N t = 1 := by
  rw [← map_mul, h.t_sq, map_one]

private lemma zj_tau_sq (h : Z4JData N Q Y V V' B ρ t τ l y z v₁ v₂) :
    z4iπ N τ * z4iπ N τ = 1 := by
  rw [← map_mul, h.tau_sq, map_one]

private lemma zj_l_sq (h : Z4JData N Q Y V V' B ρ t τ l y z v₁ v₂) :
    z4iπ N l * z4iπ N l = 1 := by
  rw [← map_mul, h.l_sq, map_one]

private lemma zj_t_tau (h : Z4JData N Q Y V V' B ρ t τ l y z v₁ v₂) :
    z4iπ N t * z4iπ N τ = z4iπ N τ * z4iπ N t := by
  rw [← map_mul, ← map_mul, h.t_tau]

private lemma zj_t_l (h : Z4JData N Q Y V V' B ρ t τ l y z v₁ v₂) :
    z4iπ N t * z4iπ N l = z4iπ N l * z4iπ N t := by
  rw [← map_mul, ← map_mul, h.t_l]

private lemma zj_tau_l (h : Z4JData N Q Y V V' B ρ t τ l y z v₁ v₂) :
    z4iπ N τ * z4iπ N l = z4iπ N l * z4iπ N τ := by
  rw [← map_mul, ← map_mul, h.tau_l]

private lemma zj_t_rho (h : Z4JData N Q Y V V' B ρ t τ l y z v₁ v₂) :
    z4iπ N t * z4iπ N ρ = z4iπ N ρ * z4iπ N t := by
  rw [← map_mul, ← map_mul, h.t_rho]

private lemma zj_tau_rho (h : Z4JData N Q Y V V' B ρ t τ l y z v₁ v₂) :
    z4iπ N τ * z4iπ N ρ = z4iπ N ρ * z4iπ N τ := by
  rw [← map_mul, ← map_mul, h.tau_rho]

private lemma zj_l_rho (h : Z4JData N Q Y V V' B ρ t τ l y z v₁ v₂) :
    z4iπ N l * z4iπ N ρ * (z4iπ N l)⁻¹ = (z4iπ N ρ)⁻¹ := by
  rw [← map_mul, ← map_inv, ← map_mul, h.l_rho, map_inv]

private lemma zj_B_cent_t (h : Z4JData N Q Y V V' B ρ t τ l y z v₁ v₂) :
    ∀ b ∈ B.map (z4iπ N), z4iπ N t * b = b * z4iπ N t := by
  rintro _ ⟨b, hb, rfl⟩
  rw [← map_mul, ← map_mul, h.B_cent_t b hb]

private lemma zj_cent_t_Q (h : Z4JData N Q Y V V' B ρ t τ l y z v₁ v₂) :
    ∀ q ∈ Q.map (z4iπ N), z4iπ N t * q = q * z4iπ N t → q ∈ B.map (z4iπ N) := by
  rintro _ ⟨q, hq, rfl⟩ hcomm
  exact Subgroup.mem_map_of_mem (z4iπ N) (h.cent_t_Q q hq
    (z4i_commute_of_map N (zj_Q_inf_N h) (fun x hx => h.normal_Q t x hx) hq hcomm))

private lemma zj_V_cent_t (h : Z4JData N Q Y V V' B ρ t τ l y z v₁ v₂) :
    ∀ v ∈ V.map (z4iπ N), z4iπ N t * v = v * z4iπ N t := by
  rintro _ ⟨v, hv, rfl⟩
  rw [← map_mul, ← map_mul, h.V_cent_t v hv]

private lemma zj_Y_cent_t (h : Z4JData N Q Y V V' B ρ t τ l y z v₁ v₂) :
    ∀ u ∈ Y.map (z4iπ N), z4iπ N t * u = u * z4iπ N t → u ∈ V.map (z4iπ N) := by
  rintro _ ⟨u, hu, rfl⟩ hcomm
  exact Subgroup.mem_map_of_mem (z4iπ N) (h.Y_cent_t u hu
    (z4i_commute_of_map N (zj_Q_inf_N h) (fun x hx => h.normal_Q t x hx) (h.Y_le_Q hu)
      hcomm))

private lemma zj_t_v₁ (h : Z4JData N Q Y V V' B ρ t τ l y z v₁ v₂) :
    z4iπ N t * z4iπ N v₁ * (z4iπ N t)⁻¹ = z4iπ N v₁ * z4iπ N y := by
  have h1 := congrArg (z4iπ N) h.t_v₁
  simpa only [map_mul, map_inv] using h1

private lemma zj_t_v₂ (h : Z4JData N Q Y V V' B ρ t τ l y z v₁ v₂) :
    z4iπ N t * z4iπ N v₂ * (z4iπ N t)⁻¹ = z4iπ N v₂ * (z4iπ N y * z4iπ N z) := by
  have h1 := congrArg (z4iπ N) h.t_v₂
  simpa only [map_mul, map_inv] using h1

private lemma zj_l_y (h : Z4JData N Q Y V V' B ρ t τ l y z v₁ v₂) :
    z4iπ N l * z4iπ N y * (z4iπ N l)⁻¹ = z4iπ N y * z4iπ N z := by
  have h1 := congrArg (z4iπ N) h.l_y
  simpa only [map_mul, map_inv] using h1

private lemma zj_l_z (h : Z4JData N Q Y V V' B ρ t τ l y z v₁ v₂) :
    z4iπ N l * z4iπ N z * (z4iπ N l)⁻¹ = z4iπ N z := by
  have h1 := congrArg (z4iπ N) h.l_z
  simpa only [map_mul, map_inv] using h1

private lemma zj_lt_v₁ (h : Z4JData N Q Y V V' B ρ t τ l y z v₁ v₂) :
    (z4iπ N l * z4iπ N t) * z4iπ N v₁ * (z4iπ N l * z4iπ N t)⁻¹ = z4iπ N v₂ := by
  have h1 := congrArg (z4iπ N) h.lt_v₁
  simpa only [map_mul, map_inv] using h1

theorem Z4JData.toZJBase (h : Z4JData N Q Y V V' B ρ t τ l y z v₁ v₂) :
    ZJBase (Q.map (z4iπ N)) (Y.map (z4iπ N)) (V.map (z4iπ N)) (V'.map (z4iπ N))
      (B.map (z4iπ N)) (z4iπ N ρ) (z4iπ N t) (z4iπ N τ) (z4iπ N l) (z4iπ N y) (z4iπ N z)
      (z4iπ N v₁) (z4iπ N v₂) :=
  { Q_comm := zj_Q_comm h
    card_Q := zj_card_Q h
    normal_Q := zj_normal h.normal_Q
    cent_Q := zj_cent_Q h
    Q_eq := zj_Q_eq h
    B_le_Q := zj_B_le_Q h
    Y_le_Q := zj_Y_le_Q h
    Y_eq := zj_Y_eq h
    V_inf_V' := zj_V_inf_V' h
    card_V := zj_card_V h
    card_V' := zj_card_V' h
    card_B := zj_card_B h
    sq_mem_V := zj_sq_mem_V h
    Y_sq := zj_Y_sq h
    Y_mem := zj_Y_mem h
    normal_Y := zj_normal h.normal_Y
    normal_V := zj_normal h.normal_V
    V_eq := zj_V_eq h
    V'_eq := zj_V'_eq h
    y_ne_one := zj_y_ne_one h
    z_ne_one := zj_z_ne_one h
    y_ne_z := zj_y_ne_z h
    v₁_ne_one := zj_v₁_ne_one h
    v₂_ne_one := zj_v₂_ne_one h
    v₁_ne_v₂ := zj_v₁_ne_v₂ h
    rho_pow_three := zj_rho_pow_three h
    rho_norm_Q := zj_norm h.rho_norm_Q
    rho_norm_Y := zj_norm h.rho_norm_Y
    rho_norm_V := zj_norm h.rho_norm_V
    rho_norm_V' := zj_norm h.rho_norm_V'
    rho_norm_B := zj_norm h.rho_norm_B
    rho_fpf_Q := zj_rho_fpf_Q h
    tau_inv := zj_tau_inv h
    tau_not_mem_Q := zj_tau_not_mem_Q h
    t_ne_one := zj_t_ne_one h
    t_sq := zj_t_sq h
    tau_sq := zj_tau_sq h
    l_sq := zj_l_sq h
    t_tau := zj_t_tau h
    t_l := zj_t_l h
    tau_l := zj_tau_l h
    t_rho := zj_t_rho h
    tau_rho := zj_tau_rho h
    l_rho := zj_l_rho h
    B_cent_t := zj_B_cent_t h
    cent_t_Q := zj_cent_t_Q h
    V_cent_t := zj_V_cent_t h
    Y_cent_t := zj_Y_cent_t h
    t_v₁ := zj_t_v₁ h
    t_v₂ := zj_t_v₂ h
    l_y := zj_l_y h
    l_z := zj_l_z h
    lt_v₁ := zj_lt_v₁ h }

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
