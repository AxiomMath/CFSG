module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog82P29Sb

public section

namespace CFSG.ComponentClassification.GSThmB.P29

open CFSG Subgroup DihedralGroup

namespace Model

variable {P : Type*} [Group P] {L : Subgroup P} {ι : P} {J : Subgroup P} {m : ℕ}
  (M : Model L ι J m)

theorem J_sup_mem_of_ρ₂_r (j : ZMod (2 ^ m)) : M.ρ₂ (r j) ∈ J ⊔ centralizer (J : Set P) := by
  rw [M.ρ₂_r]
  exact mul_mem (mem_sup_left (pow_mem M.z₁_mem_J _)) (mem_sup_right (pow_mem M.γ_mem _))

theorem ρ₂_sr_not_mem (j : ZMod (2 ^ m)) : M.ρ₂ (sr j) ∉ J ⊔ centralizer (J : Set P) := by
  intro h
  have h1 : M.ρ₂ (sr 0) = M.ρ₂ (sr j) * (M.ρ₂ (r j))⁻¹ := by
    rw [← map_inv, ← map_mul, inv_r, sr_mul_r, add_neg_cancel]
  apply M.sr_not
  rw [← M.ρ₂_apply, h1]
  exact mul_mem h (inv_mem (M.J_sup_mem_of_ρ₂_r j))

theorem inf_D_eq_bot : M.D₁ ⊓ M.D₂ = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨⟨a, rfl⟩, ⟨b, hb⟩⟩
  rw [mem_bot]
  rcases b with j | j
  · rw [M.ρ₂_r] at hb
    have hγ : M.γ ^ j.val = 1 := by
      apply M.mem_one_of_mem_J_cent _ (pow_mem M.γ_mem _)
      have : M.γ ^ j.val = (M.z₁ ^ j.val)⁻¹ * M.ρ a := by rw [← hb]; group
      rw [this]
      exact mul_mem (inv_mem (pow_mem M.z₁_mem_J _)) (M.le_J a)
    have hd : 2 ^ m ∣ j.val := by
      have h := orderOf_dvd_of_pow_eq_one hγ
      rwa [M.orderOf_γ] at h
    have hj : j.val = 0 := Nat.eq_zero_of_dvd_of_lt hd (ZMod.val_lt j)
    rw [← hb, hj, pow_zero, pow_zero, mul_one]
  · exfalso
    apply M.ρ₂_sr_not_mem j
    rw [hb]
    exact mem_sup_left (M.le_J a)

@[expose] def ρ₁₂ : DihedralGroup (2 ^ m) × DihedralGroup (2 ^ m) →* P where
  toFun x := M.ρ x.1 * M.ρ₂ x.2
  map_one' := by simp
  map_mul' x y := by
    show M.ρ (x.1 * y.1) * M.ρ₂ (x.2 * y.2) = M.ρ x.1 * M.ρ₂ x.2 * (M.ρ y.1 * M.ρ₂ y.2)
    rw [map_mul, map_mul]
    calc M.ρ x.1 * M.ρ y.1 * (M.ρ₂ x.2 * M.ρ₂ y.2)
        = M.ρ x.1 * (M.ρ y.1 * M.ρ₂ x.2) * M.ρ₂ y.2 := by simp only [mul_assoc]
      _ = M.ρ x.1 * (M.ρ₂ x.2 * M.ρ y.1) * M.ρ₂ y.2 := by rw [M.comm₁₂]
      _ = M.ρ x.1 * M.ρ₂ x.2 * (M.ρ y.1 * M.ρ₂ y.2) := by simp only [mul_assoc]

theorem ρ₁₂_apply (x : DihedralGroup (2 ^ m) × DihedralGroup (2 ^ m)) :
    M.ρ₁₂ x = M.ρ x.1 * M.ρ₂ x.2 := rfl

theorem ρ₁₂_injective : Function.Injective M.ρ₁₂ := by
  rw [injective_iff_map_eq_one]
  rintro ⟨a, b⟩ h
  rw [ρ₁₂_apply] at h
  have h1 : M.ρ a = (M.ρ₂ b)⁻¹ := eq_inv_of_mul_eq_one_left h
  have h2 : M.ρ a ∈ M.D₁ ⊓ M.D₂ := ⟨⟨a, rfl⟩, h1 ▸ ⟨b⁻¹, by rw [map_inv]⟩⟩
  rw [M.inf_D_eq_bot, mem_bot] at h2
  have ha : a = 1 := M.inj (by rw [h2, map_one])
  have hb : M.ρ₂ b = 1 := by rw [h2, one_mul] at h; exact h
  have hb' : b = 1 := M.ρ₂_injective (by rw [hb, map_one])
  rw [ha, hb']
  rfl

@[expose] def T : Subgroup P := M.ρ₁₂.range

theorem D₁_le_T : M.D₁ ≤ M.T := by
  rintro _ ⟨a, rfl⟩
  exact ⟨(a, 1), by simp [ρ₁₂_apply]⟩

theorem D₂_le_T : M.D₂ ≤ M.T := by
  rintro _ ⟨b, rfl⟩
  exact ⟨(1, b), by simp [ρ₁₂_apply]⟩

theorem sup_D_eq_T : M.D₁ ⊔ M.D₂ = M.T := by
  refine le_antisymm (sup_le M.D₁_le_T M.D₂_le_T) ?_
  rintro _ ⟨⟨a, b⟩, rfl⟩
  exact mul_mem (mem_sup_left ⟨a, rfl⟩) (mem_sup_right ⟨b, rfl⟩)

theorem card_T : Nat.card M.T = 2 ^ (2 * m + 2) := by
  rw [T, ← Nat.card_congr (MonoidHom.ofInjective M.ρ₁₂_injective).toEquiv, Nat.card_prod,
    DihedralGroup.nat_card]
  ring

theorem card_D₁ : Nat.card M.D₁ = 2 ^ (m + 1) := by
  rw [D₁, ← Nat.card_congr (MonoidHom.ofInjective M.inj).toEquiv, DihedralGroup.nat_card]
  ring

theorem card_D₂ : Nat.card M.D₂ = 2 ^ (m + 1) := by
  rw [D₂, ← Nat.card_congr (MonoidHom.ofInjective M.ρ₂_injective).toEquiv,
    DihedralGroup.nat_card]
  ring

theorem iota_mem_T : ι ∈ M.T := M.D₂_le_T M.iota_mem_D₂

theorem z₁_mem_T : M.z₁ ∈ M.T := M.D₁_le_T M.z₁_mem_D₁

theorem ρ_mem_L (x : DihedralGroup (2 ^ m)) : M.ρ x ∈ L := M.J_le_L (M.le_J x)

theorem ρ₂_mem_L (x : DihedralGroup (2 ^ m)) : M.ρ₂ x ∈ L := by
  rw [M.ρ₂_apply]
  exact mul_mem (mul_mem (inv_mem M.t₀_mem) (M.ρ_mem_L x)) M.t₀_mem

theorem T_le : M.T ≤ centralizer ({ι} : Set P) ⊓ L := by
  rintro _ ⟨⟨a, b⟩, rfl⟩
  rw [ρ₁₂_apply]
  exact ⟨mul_mem (M.J_le (M.le_J a)) (mem_centralizer_singleton_iff.mpr (M.iota_comm₂ b).symm),
    mul_mem (M.ρ_mem_L a) (M.ρ₂_mem_L b)⟩

theorem z₁_comm (x : DihedralGroup (2 ^ m)) : M.z₁ * M.ρ x = M.ρ x * M.z₁ := by
  rw [z₁, ← map_mul, ← map_mul, r_cc_central M.two_le]

theorem sq_conj_ρ (x : DihedralGroup (2 ^ m)) :
    (M.t₀ * M.t₀)⁻¹ * M.ρ x * (M.t₀ * M.t₀) = M.ρ x := by
  rw [M.sq, show M.ρ (r (cc m)) = M.z₁ from rfl]
  have h1 := M.iota_comm₁ x
  have h2 := M.z₁_comm x
  calc (ι * M.z₁)⁻¹ * M.ρ x * (ι * M.z₁) = M.z₁⁻¹ * (ι⁻¹ * (M.ρ x * ι)) * M.z₁ := by group
    _ = M.z₁⁻¹ * (ι⁻¹ * (ι * M.ρ x)) * M.z₁ := by rw [h1]
    _ = M.z₁⁻¹ * (M.ρ x * M.z₁) := by rw [inv_mul_cancel_left, mul_assoc]
    _ = M.z₁⁻¹ * (M.z₁ * M.ρ x) := by rw [h2]
    _ = M.ρ x := by rw [inv_mul_cancel_left]

theorem conj_t₀_mem_T {x : P} (hx : x ∈ M.T) : M.t₀⁻¹ * x * M.t₀ ∈ M.T := by
  obtain ⟨⟨a, b⟩, rfl⟩ := hx
  rw [ρ₁₂_apply]
  have h0 : M.t₀⁻¹ * (M.ρ a * M.ρ₂ b) * M.t₀ =
      M.ρ₂ a * ((M.t₀ * M.t₀)⁻¹ * M.ρ b * (M.t₀ * M.t₀)) := by
    rw [M.ρ₂_apply, M.ρ₂_apply]
    group
  have h1 : M.t₀⁻¹ * (M.ρ a * M.ρ₂ b) * M.t₀ = M.ρ₂ a * M.ρ b := by
    rw [h0, M.sq_conj_ρ]
  rw [h1, ← M.comm₁₂]
  exact ⟨(b, a), rfl⟩

theorem t₀_sq_mem_T : M.t₀ * M.t₀ ∈ M.T := by
  rw [M.sq]
  exact mul_mem M.iota_mem_T M.z₁_mem_T

theorem t₀_conj_mem_T {x : P} (hx : x ∈ M.T) : M.t₀ * x * M.t₀⁻¹ ∈ M.T := by
  have h := M.conj_t₀_mem_T (mul_mem (mul_mem M.t₀_sq_mem_T hx) (inv_mem M.t₀_sq_mem_T))
  have e : M.t₀⁻¹ * (M.t₀ * M.t₀ * x * (M.t₀ * M.t₀)⁻¹) * M.t₀ = M.t₀ * x * M.t₀⁻¹ := by group
  rwa [e] at h

theorem t₀_mem_normalizer : M.t₀ ∈ normalizer (M.T : Set P) := by
  rw [mem_normalizer_iff]
  intro x
  refine ⟨M.t₀_conj_mem_T, fun h => ?_⟩
  have := M.conj_t₀_mem_T h
  rwa [show M.t₀⁻¹ * (M.t₀ * x * M.t₀⁻¹) * M.t₀ = x by group] at this

theorem t₀_conj_iota : M.t₀⁻¹ * ι * M.t₀ = M.z₁ := by
  have h1 : M.t₀⁻¹ * ι * M.t₀ = (M.t₀ * M.t₀)⁻¹ * M.z₁ * (M.t₀ * M.t₀) := by
    have h : M.t₀⁻¹ * ι * M.t₀ = M.t₀⁻¹ * (M.t₀⁻¹ * M.ρ (r (cc m)) * M.t₀) * M.t₀ :=
      congrArg (fun x => M.t₀⁻¹ * x * M.t₀) M.iota
    rw [h, show M.ρ (r (cc m)) = M.z₁ from rfl]
    group
  rw [h1, M.sq, show M.ρ (r (cc m)) = M.z₁ from rfl, _root_.mul_inv_rev, M.z₁_inv]
  have hc := M.iota_comm_z₁
  calc M.z₁ * ι⁻¹ * M.z₁ * (ι * M.z₁) = M.z₁ * (ι⁻¹ * (M.z₁ * ι)) * M.z₁ := by group
    _ = M.z₁ * (ι⁻¹ * (ι * M.z₁)) * M.z₁ := by rw [hc]
    _ = M.z₁ := by rw [inv_mul_cancel_left, M.z₁_sq, one_mul]

end Model

end CFSG.ComponentClassification.GSThmB.P29
