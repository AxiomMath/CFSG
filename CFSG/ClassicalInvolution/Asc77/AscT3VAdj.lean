module

public import CFSG.ClassicalInvolution.Asc77.AscT3VBase
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Int.Star

public section

namespace CFSG.ClassicalInvolution.Asc77.T3CII.T3V

section Arith

theorem exists_cob {k : ℕ} (hk : 2 ≤ k) {κ : ℤ} (hκ : κ = 2 ^ k + 1 ∨ κ = 2 ^ k - 1) {m : ℤ}
    (hm : (2 : ℤ) ^ (k + 1) ∣ m * (1 + κ)) :
    ∃ m' : ℤ, (2 : ℤ) ^ (k + 1) ∣ m - m' * (1 - κ) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  rcases hκ with rfl | rfl
  · have h1 : (2 : ℤ) ^ (j + 2 + 1) ∣ 2 * (m * (1 + 2 ^ (j + 1))) := by
      have : m * (1 + (2 ^ (j + 2) + 1)) = 2 * (m * (1 + 2 ^ (j + 1))) := by ring
      rwa [this] at hm
    have h2 : (2 : ℤ) ^ (j + 2) ∣ m * (1 + 2 ^ (j + 1)) := by
      have e : (2 : ℤ) ^ (j + 2 + 1) = 2 * 2 ^ (j + 2) := by ring
      rw [e] at h1
      exact (mul_dvd_mul_iff_left (by norm_num : (2 : ℤ) ≠ 0)).mp h1
    have h3 : (2 : ℤ) ^ (j + 2) ∣ m := by
      have e : m = (m * (1 + 2 ^ (j + 1))) * (1 - 2 ^ (j + 1)) +
          2 ^ (j + 2) * (m * 2 ^ j) := by ring
      rw [e]
      exact dvd_add (dvd_mul_of_dvd_left h2 _) (dvd_mul_right _ _)
    obtain ⟨s, hs⟩ := h3
    refine ⟨s, ?_⟩
    have : m - s * (1 - (2 ^ (j + 2) + 1)) = 2 ^ (j + 2 + 1) * s := by rw [hs]; ring
    rw [this]
    exact dvd_mul_right _ _
  · have h1 : (2 : ℤ) ^ (j + 2) * 2 ∣ 2 ^ (j + 2) * m := by
      have : m * (1 + (2 ^ (j + 2) - 1)) = 2 ^ (j + 2) * m := by ring
      rw [this] at hm
      have e : (2 : ℤ) ^ (j + 2 + 1) = 2 ^ (j + 2) * 2 := by ring
      rwa [e] at hm
    have h2 : (2 : ℤ) ∣ m := (mul_dvd_mul_iff_left (by positivity : (2 : ℤ) ^ (j + 2) ≠ 0)).mp h1
    obtain ⟨s, hs⟩ := h2
    refine ⟨s * (1 + 2 ^ (j + 1)), ?_⟩
    have : m - s * (1 + 2 ^ (j + 1)) * (1 - (2 ^ (j + 2) - 1)) =
        2 ^ (j + 2 + 1) * (s * 2 ^ j) := by rw [hs]; ring
    rw [this]
    exact dvd_mul_right _ _

end Arith

section Decomp

variable {G : Type*} [Group G]

theorem mem_sup_zpowers_of_commute {u v : G} (h : u * v = v * u) {w : G}
    (hw : w ∈ Subgroup.zpowers u ⊔ Subgroup.zpowers v) : ∃ i j : ℤ, w = u ^ i * v ^ j := by
  have hc : Commute u v := h
  let Q : Subgroup G :=
    { carrier := {w | ∃ i j : ℤ, w = u ^ i * v ^ j}
      mul_mem' := by
        rintro _ _ ⟨i, j, rfl⟩ ⟨i', j', rfl⟩
        refine ⟨i + i', j + j', ?_⟩
        have e : v ^ j * u ^ i' = u ^ i' * v ^ j := (hc.symm.zpow_zpow j i').eq
        calc u ^ i * v ^ j * (u ^ i' * v ^ j') = u ^ i * (v ^ j * u ^ i') * v ^ j' := by
              simp only [mul_assoc]
          _ = u ^ i * (u ^ i' * v ^ j) * v ^ j' := by rw [e]
          _ = u ^ (i + i') * v ^ (j + j') := by rw [zpow_add, zpow_add]; simp only [mul_assoc]
      one_mem' := ⟨0, 0, by simp⟩
      inv_mem' := by
        rintro _ ⟨i, j, rfl⟩
        refine ⟨-i, -j, ?_⟩
        have e : v ^ (-j) * u ^ (-i) = u ^ (-i) * v ^ (-j) := (hc.symm.zpow_zpow (-j) (-i)).eq
        rw [mul_inv_rev, ← zpow_neg, ← zpow_neg, e] }
  have hle : Subgroup.zpowers u ⊔ Subgroup.zpowers v ≤ Q := by
    refine sup_le (Subgroup.zpowers_le.mpr ⟨1, 0, by simp⟩)
      (Subgroup.zpowers_le.mpr ⟨0, 1, by simp⟩)
  exact hle hw

theorem cocycle_cob {W : Subgroup G} {a u v w₁ : G} {k : ℕ} (hk : 2 ≤ k) {κ : ℤ}
    (hκ : κ = 2 ^ k + 1 ∨ κ = 2 ^ k - 1) (hW : W = Subgroup.zpowers u ⊔ Subgroup.zpowers v)
    (huv : u * v = v * u) (hu : orderOf u = 2 ^ (k + 1)) (hv : orderOf v = 2 ^ (k + 1))
    (hdis : Subgroup.zpowers u ⊓ Subgroup.zpowers v = ⊥)
    (hα : ∀ w ∈ W, a * w * a⁻¹ = w ^ κ) (hw₁ : w₁ ∈ W)
    (hcoc : w₁ * (a * w₁ * a⁻¹) = 1) : ∃ w ∈ W, w₁ * (a * w * a⁻¹) = w := by
  have hc : Commute u v := huv
  obtain ⟨i, j, rfl⟩ := mem_sup_zpowers_of_commute huv (hW ▸ hw₁)
  rw [hα _ hw₁] at hcoc
  have h1 : (u ^ i * v ^ j) ^ (1 + κ) = 1 := by
    rw [zpow_add, zpow_one]
    exact hcoc
  rw [(hc.zpow_zpow i j).mul_zpow, ← zpow_mul, ← zpow_mul] at h1
  have hu1 : u ^ (i * (1 + κ)) = 1 := by
    have hm : u ^ (i * (1 + κ)) ∈ Subgroup.zpowers u ⊓ Subgroup.zpowers v := by
      refine ⟨Subgroup.zpow_mem _ (Subgroup.mem_zpowers u) _, ?_⟩
      have : u ^ (i * (1 + κ)) = (v ^ (j * (1 + κ)))⁻¹ := eq_inv_of_mul_eq_one_left h1
      rw [this]
      exact Subgroup.inv_mem _ (Subgroup.zpow_mem _ (Subgroup.mem_zpowers v) _)
    rw [hdis] at hm
    exact Subgroup.mem_bot.mp hm
  have hv1 : v ^ (j * (1 + κ)) = 1 := by
    rw [hu1, one_mul] at h1
    exact h1
  have hdu : (2 : ℤ) ^ (k + 1) ∣ i * (1 + κ) := by
    have := (orderOf_dvd_iff_zpow_eq_one (x := u) (i := i * (1 + κ))).mpr hu1
    rwa [hu, Nat.cast_pow, Nat.cast_ofNat] at this
  have hdv : (2 : ℤ) ^ (k + 1) ∣ j * (1 + κ) := by
    have := (orderOf_dvd_iff_zpow_eq_one (x := v) (i := j * (1 + κ))).mpr hv1
    rwa [hv, Nat.cast_pow, Nat.cast_ofNat] at this
  obtain ⟨i', hi'⟩ := exists_cob hk hκ hdu
  obtain ⟨j', hj'⟩ := exists_cob hk hκ hdv
  have hwW : u ^ i' * v ^ j' ∈ W := by
    rw [hW]
    exact Subgroup.mul_mem _
      (Subgroup.mem_sup_left (Subgroup.zpow_mem _ (Subgroup.mem_zpowers u) _))
      (Subgroup.mem_sup_right (Subgroup.zpow_mem _ (Subgroup.mem_zpowers v) _))
  refine ⟨u ^ i' * v ^ j', hwW, ?_⟩
  rw [hα _ hwW, (hc.zpow_zpow i' j').mul_zpow, ← zpow_mul, ← zpow_mul]
  have hu2 : u ^ (i + i' * κ - i') = 1 := by
    refine (orderOf_dvd_iff_zpow_eq_one (x := u)).mp ?_
    rw [hu, Nat.cast_pow, Nat.cast_ofNat]
    have : i + i' * κ - i' = i - i' * (1 - κ) := by ring
    rw [this]
    exact hi'
  have hv2 : v ^ (j + j' * κ - j') = 1 := by
    refine (orderOf_dvd_iff_zpow_eq_one (x := v)).mp ?_
    rw [hv, Nat.cast_pow, Nat.cast_ofNat]
    have : j + j' * κ - j' = j - j' * (1 - κ) := by ring
    rw [this]
    exact hj'
  have e1 : u ^ (i + i' * κ - i') = u ^ i * u ^ (i' * κ) * (u ^ i')⁻¹ := by
    rw [sub_eq_add_neg, zpow_add, zpow_add, zpow_neg]
  have e2 : v ^ (j + j' * κ - j') = v ^ j * v ^ (j' * κ) * (v ^ j')⁻¹ := by
    rw [sub_eq_add_neg, zpow_add, zpow_add, zpow_neg]
  rw [e1] at hu2
  rw [e2] at hv2
  have hc1 : u ^ i * u ^ (i' * κ) = u ^ i' := by
    have := hu2
    rw [mul_inv_eq_one] at this
    exact this
  have hc2 : v ^ j * v ^ (j' * κ) = v ^ j' := by
    have := hv2
    rw [mul_inv_eq_one] at this
    exact this
  calc u ^ i * v ^ j * (u ^ (i' * κ) * v ^ (j' * κ))
      = u ^ i * (v ^ j * u ^ (i' * κ)) * v ^ (j' * κ) := by simp only [mul_assoc]
    _ = u ^ i * (u ^ (i' * κ) * v ^ j) * v ^ (j' * κ) := by
        rw [(hc.symm.zpow_zpow j (i' * κ)).eq]
    _ = (u ^ i * u ^ (i' * κ)) * (v ^ j * v ^ (j' * κ)) := by simp only [mul_assoc]
    _ = u ^ i' * v ^ j' := by rw [hc1, hc2]

end Decomp


section Fixed

variable {G : Type*} [Group G] [Finite G]

theorem exists_fixed_coset {W Q : Subgroup G} {x s : G}
    (hxN : x ∈ Subgroup.normalizer (W : Set G)) (hsN : s ∈ Subgroup.normalizer (W : Set G))
    (hQN : Q ≤ Subgroup.normalizer (W : Set G)) (hQ : Odd (Nat.card Q))
    (hQW : ∀ q ∈ Q, q ∈ W → q = 1) (hQx : ∀ q ∈ Q, x * q * x⁻¹ ∈ Q)
    (hQs : ∀ q ∈ Q, s * q * s⁻¹ ∈ Q) (hss : s * s = 1)
    (hsx : ∃ q₂ ∈ Q, ∃ w₂ ∈ W, s * x * s⁻¹ = x * q₂ * w₂) :
    ∃ q ∈ Q, ∃ w ∈ W, s * (q * x) * s⁻¹ = (q * x) * w := by
  set N : Subgroup G := Subgroup.normalizer (W : Set G) with hN
  let W' : Subgroup ↥N := W.subgroupOf N
  have hW'n : W'.Normal := ⟨fun n hn g => by
    have h1 : (n : G) ∈ W := hn
    show ((g * n * g⁻¹ : ↥N) : G) ∈ W
    have := (Subgroup.mem_normalizer_iff.mp g.2 (n : G)).mp h1
    simpa using this⟩
  let Q' : Subgroup ↥N := Q.subgroupOf N
  have hcard : Nat.card Q' = Nat.card Q :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQN).toEquiv
  obtain ⟨q₂, hq₂, w₂, hw₂, hsxe⟩ := hsx
  have hWN : W ≤ N := Subgroup.le_normalizer
  obtain ⟨q', hq', w', hw', hfix⟩ := exists_mod_fixed W' Q' (x := ⟨x, hxN⟩) (s := ⟨s, hsN⟩)
    (hcard ▸ hQ)
    (fun q hq hqw => by
      have h1 : (q : G) ∈ Q := hq
      have h2 : (q : G) ∈ W := hqw
      exact Subtype.ext (hQW _ h1 h2))
    (fun q hq => by
      have h1 : (q : G) ∈ Q := hq
      show ((⟨x, hxN⟩ * q * ⟨x, hxN⟩⁻¹ : ↥N) : G) ∈ Q
      simpa using hQx _ h1)
    (fun q hq => by
      have h1 : (q : G) ∈ Q := hq
      show ((⟨s, hsN⟩ * q * ⟨s, hsN⟩⁻¹ : ↥N) : G) ∈ Q
      simpa using hQs _ h1)
    (Subtype.ext (by simpa using hss))
    ⟨⟨q₂, hQN hq₂⟩, hq₂, ⟨w₂, hWN hw₂⟩, hw₂, Subtype.ext (by simpa using hsxe)⟩
  refine ⟨(q' : G), hq', (w' : G), hw', ?_⟩
  have := congrArg Subtype.val hfix
  simpa using this

end Fixed

end CFSG.ClassicalInvolution.Asc77.T3CII.T3V
