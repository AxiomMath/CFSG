module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank632NearCyclic
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank632GL3Part
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank632Gen3

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

private theorem isPGroup_two_of_sq {W : Type*} [Group W] (h : ∀ v : W, v ^ 2 = 1) :
    IsPGroup 2 W := fun v => ⟨1, by simpa using h v⟩

private theorem exists_card_eq_two_pow {W : Type*} [Group W] [Finite W] (h : ∀ v : W, v ^ 2 = 1) :
    ∃ n : ℕ, Nat.card W = 2 ^ n :=
  (isPGroup_two_of_sq h).exists_card_eq

private theorem fixed_apply_mem {Γ V : Type*} [Group Γ] [Group V] (ρ : Γ →* MulAut V) {x y : Γ}
    (hxy : x * y = y * x) {v : V} (hv : v ∈ fixedSubgroup ρ x) : ρ y v ∈ fixedSubgroup ρ x := by
  change ρ x (ρ y v) = ρ y v
  have h1 : ρ x (ρ y v) = ρ (x * y) v := by rw [map_mul]; rfl
  have h2 : ρ y (ρ x v) = ρ (y * x) v := by rw [map_mul]; rfl
  rw [h1, hxy, ← h2]
  exact congrArg (ρ y) hv

private def fixedAut {Γ V : Type*} [Group Γ] [Group V] (ρ : Γ →* MulAut V) {x y : Γ}
    (hxy : x * y = y * x) : MulAut (fixedSubgroup ρ x) where
  toFun v := ⟨ρ y v, fixed_apply_mem ρ hxy v.2⟩
  invFun v := ⟨ρ y⁻¹ v, fixed_apply_mem ρ (show Commute x y⁻¹ from
    (show Commute x y from hxy).inv_right) v.2⟩
  left_inv v := Subtype.ext (by
    change ρ y⁻¹ (ρ y v) = v
    rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl)
  right_inv v := Subtype.ext (by
    change ρ y (ρ y⁻¹ v) = v
    rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one]; rfl)
  map_mul' a b := Subtype.ext (map_mul (ρ y) (a : V) (b : V))

private theorem fixedAut_pow_three {Γ V : Type*} [Group Γ] [Group V] (ρ : Γ →* MulAut V)
    {x y : Γ} (hxy : x * y = y * x) (hy : y ^ 3 = 1) : fixedAut ρ hxy ^ 3 = 1 := by
  ext v
  have h : ρ y (ρ y (ρ y (v : V))) = ρ (y ^ 3) v := by
    rw [pow_three, map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply]
  rw [hy, map_one] at h
  rw [pow_three]
  exact h

private theorem card_fixedSubgroup_conj {Γ V : Type*} [Group Γ] [Group V] (ρ : Γ →* MulAut V)
    (a y : Γ) : Nat.card (fixedSubgroup ρ (a * y * a⁻¹)) = Nat.card (fixedSubgroup ρ y) := by
  symm
  refine Nat.card_congr (Equiv.subtypeEquiv (ρ a).toEquiv (fun v => ?_))
  change ρ y v = v ↔ ρ (a * y * a⁻¹) (ρ a v) = ρ a v
  have h : ρ (a * y * a⁻¹) (ρ a v) = ρ a (ρ y v) := by
    rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel_right, map_mul, MulAut.mul_apply]
  rw [h]
  exact ((ρ a).injective.eq_iff).symm

theorem card_dvd_eighty_one_of_fixed_data {Γ V : Type*} [Group Γ] [Finite Γ] [Group V] [Finite V]
    (hΓ : IsPGroup 3 Γ) (ρ : Γ →* MulAut V) (hV : ∀ a b : V, a * b = b * a)
    (hV2 : ∀ a : V, a ^ 2 = 1) (hρ : Function.Injective ρ) {x z g : Γ} (hx : x ^ 3 = 1)
    (hz : z ^ 3 = 1) (hzc : ∀ a : Γ, a * z = z * a) (hxz : x * z = z * x) {b : ℕ}
    (hb : ¬ 3 ∣ b) (hg : g * x * g⁻¹ = x * z ^ b) (hfree : ∀ v : V, ρ z v = v → v = 1)
    (hnear : NearCyclic ↥(fixedSubgroup ρ x)) : Nat.card Γ ∣ 81 := by
  obtain ⟨m, hm⟩ := exists_card_eq_two_pow hV2
  have hV3 : ¬ 3 ∣ Nat.card V := by
    rw [hm]
    intro h
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
    omega
  have hF2 : ∀ v : fixedSubgroup ρ x, v ^ 2 = 1 := fun v => Subtype.ext (hV2 v)
  have hF8 : Nat.card (fixedSubgroup ρ x) ≤ 8 := hnear.card_le_eight hF2
  obtain ⟨n, hn⟩ := exists_card_eq_two_pow hF2
  have hmod : Nat.card (fixedSubgroup ρ x) ≡ 1 [MOD 3] :=
    card_modEq_one_of_fixedPointFree (fixedAut ρ hxz) (fixedAut_pow_three ρ hxz hz)
      fun v hv => Subtype.ext (hfree v (congrArg Subtype.val hv))
  have hF4 : Nat.card (fixedSubgroup ρ x) ≤ 4 := by
    rw [hn] at hF8 hmod ⊢
    have hn3 : n ≤ 3 := by
      by_contra h
      have h4 : 2 ^ 4 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    interval_cases n <;> simp_all [Nat.ModEq]
  have hc1 : Nat.card (fixedSubgroup ρ (x * z ^ b)) = Nat.card (fixedSubgroup ρ x) := by
    rw [← hg]
    exact card_fixedSubgroup_conj ρ g x
  have hc2 : Nat.card (fixedSubgroup ρ (x * z ^ (2 * b))) = Nat.card (fixedSubgroup ρ x) := by
    have hgz : g * z ^ b * g⁻¹ = z ^ b :=
      ((show Commute g z from hzc g).pow_right b).mul_inv_cancel
    have h : g * (x * z ^ b) * g⁻¹ = x * z ^ (2 * b) :=
      calc g * (x * z ^ b) * g⁻¹ = (g * x * g⁻¹) * (g * z ^ b * g⁻¹) := by group
        _ = x * z ^ b * z ^ b := by rw [hg, hgz]
        _ = x * z ^ (2 * b) := by rw [mul_assoc, ← pow_add, two_mul]
    rw [← h, card_fixedSubgroup_conj, hc1]
  have hzb : z ^ b = z ^ (b % 3) := pow_eq_pow_mod b hz
  have hz2b : z ^ (2 * b) = z ^ (2 * b % 3) := pow_eq_pow_mod (2 * b) hz
  have hcz : Nat.card (fixedSubgroup ρ (x * z)) = Nat.card (fixedSubgroup ρ x) ∧
      Nat.card (fixedSubgroup ρ (x * z ^ 2)) = Nat.card (fixedSubgroup ρ x) := by
    rcases (by omega : b % 3 = 1 ∨ b % 3 = 2) with h | h
    · have e1 : 2 * b % 3 = 2 := by omega
      rw [h, pow_one] at hzb
      rw [e1] at hz2b
      rw [hzb] at hc1
      rw [hz2b] at hc2
      exact ⟨hc1, hc2⟩
    · have e1 : 2 * b % 3 = 1 := by omega
      rw [h] at hzb
      rw [e1, pow_one] at hz2b
      rw [hzb] at hc1
      rw [hz2b] at hc2
      exact ⟨hc2, hc1⟩
  have hVc : Nat.card V ≤ 2 ^ 6 := by
    have h := card_le_mul_fixedSubgroups hV hV3 ρ hx hz hxz hfree
    rw [hcz.1, hcz.2] at h
    calc Nat.card V ≤ Nat.card (fixedSubgroup ρ x) * Nat.card (fixedSubgroup ρ x) *
          Nat.card (fixedSubgroup ρ x) := h
      _ ≤ 4 * 4 * 4 := by gcongr
      _ = 2 ^ 6 := by norm_num
  exact card_dvd_eighty_one_of_faithful_action hV hV2 hVc hΓ ρ hρ

end CFSG.LocalAnalysis.RankThreeTheoremC
