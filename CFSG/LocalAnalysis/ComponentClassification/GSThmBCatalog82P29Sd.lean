module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog82P29Sc

public section

namespace CFSG.ComponentClassification.GSThmB.P29

open CFSG Subgroup DihedralGroup

namespace Model

variable {P : Type*} [Group P] {L : Subgroup P} {ι : P} {J : Subgroup P} {m : ℕ}
  (M : Model L ι J m)

omit M in
theorem central_of_comm (hm : 2 ≤ m) {f : DihedralGroup (2 ^ m) →* P} (hf : Function.Injective f)
    {a : DihedralGroup (2 ^ m)} (ha : ∀ c, f a * f c = f c * f a) : a = 1 ∨ a = r (cc m) := by
  rw [← mem_center_dih hm, Subgroup.mem_center_iff]
  intro c
  apply hf
  rw [map_mul, map_mul, ha]

theorem mem_T_of_comm {x : P} (hx : x ∈ M.T) (hc : ∀ y ∈ M.T, x * y = y * x) :
    x = 1 ∨ x = M.z₁ ∨ x = ι ∨ x = M.z₁ * ι := by
  obtain ⟨⟨a, b⟩, rfl⟩ := hx
  rw [ρ₁₂_apply] at hc ⊢
  have ha : ∀ c, M.ρ a * M.ρ c = M.ρ c * M.ρ a := by
    intro c
    have h := hc (M.ρ c) (M.D₁_le_T ⟨c, rfl⟩)
    have h2 := M.comm₁₂ c b
    have e : M.ρ a * M.ρ c * M.ρ₂ b = M.ρ c * M.ρ a * M.ρ₂ b := by
      calc M.ρ a * M.ρ c * M.ρ₂ b = M.ρ a * (M.ρ c * M.ρ₂ b) := mul_assoc _ _ _
        _ = M.ρ a * (M.ρ₂ b * M.ρ c) := by rw [h2]
        _ = M.ρ c * M.ρ a * M.ρ₂ b := by rw [← mul_assoc, h, mul_assoc]
    exact mul_right_cancel e
  have hb : ∀ c, M.ρ₂ b * M.ρ₂ c = M.ρ₂ c * M.ρ₂ b := by
    intro c
    have h := hc (M.ρ₂ c) (M.D₂_le_T ⟨c, rfl⟩)
    have h2 := M.comm₁₂ a c
    have e : M.ρ a * (M.ρ₂ b * M.ρ₂ c) = M.ρ a * (M.ρ₂ c * M.ρ₂ b) := by
      calc M.ρ a * (M.ρ₂ b * M.ρ₂ c) = M.ρ a * M.ρ₂ b * M.ρ₂ c := (mul_assoc _ _ _).symm
        _ = M.ρ₂ c * (M.ρ a * M.ρ₂ b) := h
        _ = M.ρ a * (M.ρ₂ c * M.ρ₂ b) := by rw [← mul_assoc, ← h2, mul_assoc]
    exact mul_left_cancel e
  have hz : M.ρ₂ (r (cc m)) = ι := M.iota_eq.symm
  rcases central_of_comm M.two_le M.inj ha with rfl | rfl <;>
    rcases central_of_comm M.two_le M.ρ₂_injective hb with rfl | rfl
  · left; simp
  · right; right; left; rw [map_one, one_mul, hz]
  · right; left; rw [map_one, mul_one]; rfl
  · right; right; right; rw [hz]; rfl

theorem ρ₂_r_mem_cent_iff (j : ZMod (2 ^ m)) :
    M.ρ₂ (r j) ∈ centralizer (J : Set P) ↔ Even j.val := by
  rw [M.ρ₂_r]
  constructor
  · intro h
    have h1 : M.z₁ ^ j.val ∈ centralizer (J : Set P) := by
      have := mul_mem h (inv_mem (pow_mem M.γ_mem j.val))
      rwa [mul_inv_cancel_right] at this
    have h2 := M.mem_one_of_mem_J_cent (pow_mem M.z₁_mem_J _) h1
    by_contra hodd
    rw [M.z₁_pow_odd (Nat.not_even_iff_odd.mp hodd)] at h2
    exact M.z₁_ne h2
  · intro h
    rw [M.z₁_pow_even h, one_mul]
    exact pow_mem M.γ_mem _

theorem D₂_inf_cent : M.D₂ ⊓ centralizer (J : Set P) = (zpowers (r 2)).map M.ρ₂ := by
  ext x
  constructor
  · rintro ⟨⟨b, rfl⟩, hc⟩
    rcases b with j | j
    · refine ⟨r j, (mem_zpowers_r_two M.two_le _).mpr ⟨j, ?_, rfl⟩, rfl⟩
      exact (M.ρ₂_r_mem_cent_iff j).mp hc
    · exact absurd (mem_sup_right hc) (M.ρ₂_sr_not_mem j)
  · rintro ⟨b, hb, rfl⟩
    obtain ⟨j, hj, rfl⟩ := (mem_zpowers_r_two M.two_le b).mp hb
    exact ⟨⟨r j, rfl⟩, (M.ρ₂_r_mem_cent_iff j).mpr hj⟩

theorem card_D₂_inf_cent : Nat.card ↥(M.D₂ ⊓ centralizer (J : Set P)) = 2 ^ (m - 1) := by
  rw [M.D₂_inf_cent, Subgroup.card_map_of_injective M.ρ₂_injective,
    card_zpowers_r_two M.two_le]

theorem isCyclic_D₂_inf_cent : IsCyclic ↥(M.D₂ ⊓ centralizer (J : Set P)) := by
  rw [M.D₂_inf_cent, MonoidHom.map_zpowers]
  infer_instance

theorem γ_mem_T : M.γ ∈ M.T := mul_mem M.z₁_mem_T (M.D₂_le_T ⟨r 1, rfl⟩)

theorem T_inf_cent : M.T ⊓ centralizer (J : Set P) = zpowers M.γ := by
  refine le_antisymm ?_ (zpowers_le.mpr ⟨M.γ_mem_T, M.γ_mem⟩)
  rintro _ ⟨⟨⟨a, b⟩, rfl⟩, hc⟩
  have hc' : M.ρ a * M.ρ₂ b ∈ centralizer (J : Set P) := hc
  clear hc
  rw [ρ₁₂_apply]
  rcases b with j | j
  · rw [M.ρ₂_r] at hc' ⊢
    have h1 : M.ρ a * M.z₁ ^ j.val ∈ centralizer (J : Set P) := by
      have := mul_mem hc' (inv_mem (pow_mem M.γ_mem j.val))
      rwa [← mul_assoc, mul_inv_cancel_right] at this
    have h2 := M.mem_one_of_mem_J_cent (mul_mem (M.le_J a) (pow_mem M.z₁_mem_J _)) h1
    rw [← mul_assoc, h2, one_mul]
    exact pow_mem (mem_zpowers _) _
  · exfalso
    apply M.ρ₂_sr_not_mem j
    have : M.ρ₂ (sr j) = (M.ρ a)⁻¹ * (M.ρ a * M.ρ₂ (sr j)) := by group
    rw [this]
    exact mul_mem (mem_sup_left (inv_mem (M.le_J a))) (mem_sup_right hc')

theorem card_T_inf_cent : Nat.card ↥(M.T ⊓ centralizer (J : Set P)) = 2 ^ m := by
  rw [M.T_inf_cent, Nat.card_zpowers, M.orderOf_γ]

theorem isCyclic_T_inf_cent : IsCyclic ↥(M.T ⊓ centralizer (J : Set P)) := by
  rw [M.T_inf_cent]
  infer_instance

theorem isPGroup_T : IsPGroup 2 M.T := IsPGroup.of_card M.card_T

theorem T_inf_J [Finite P] : M.T ⊓ J = M.D₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  symm
  refine Subgroup.eq_of_le_of_card_ge (le_inf M.D₁_le_T (fun x ⟨a, ha⟩ => ha ▸ M.le_J a)) ?_
  rw [M.card_D₁]
  obtain ⟨k, hk⟩ := (M.isPGroup_T.to_le (inf_le_left : M.T ⊓ J ≤ M.T)).exists_card_eq
  have hdvd : Nat.card ↥(M.T ⊓ J) ∣ Nat.card J := Subgroup.card_dvd_of_le inf_le_right
  rw [hk] at hdvd ⊢
  rcases Nat.lt_or_ge k (m + 2) with h | h
  · exact Nat.pow_le_pow_right (by norm_num) (by omega)
  · exact absurd ((pow_dvd_pow 2 h).trans hdvd) M.not_dvd_J

end Model

end CFSG.ComponentClassification.GSThmB.P29
