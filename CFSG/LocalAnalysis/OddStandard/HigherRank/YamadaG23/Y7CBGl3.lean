module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisGL3
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup

private theorem y7c_mat_pow6 :
    ∀ g : Matrix (Fin 3) (Fin 3) (ZMod 2), g ^ 6 = 1 → g ^ 2 = 1 ∨ g ^ 3 = 1 := by
  decide +kernel

theorem y7c_gl3_pow6 (g : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) (h : g ^ 6 = 1) :
    g ^ 2 = 1 ∨ g ^ 3 = 1 := by
  have h' : ((g : Matrix (Fin 3) (Fin 3) (ZMod 2))) ^ 6 = 1 := by
    have := congrArg (fun u : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2) =>
      (u : Matrix (Fin 3) (Fin 3) (ZMod 2))) h
    simpa [Units.val_pow_eq_pow_val] using this
  rcases y7c_mat_pow6 _ h' with h2 | h3
  · left
    exact Units.ext (by simpa [Units.val_pow_eq_pow_val] using h2)
  · right
    exact Units.ext (by simpa [Units.val_pow_eq_pow_val] using h3)

private theorem y7c_no_six {H : Type} [Group H] [Finite H] (hcard : Nat.card H = 168)
    (h6 : ∀ g : H, g ^ 6 = 1 → g ^ 2 = 1 ∨ g ^ 3 = 1) {X Y : H} (hX : X ≠ 1)
    (hXa : ∃ a : ℕ, orderOf X = 3 ^ a) (hYb : ∃ b : ℕ, orderOf Y = 2 ^ b) (hY1 : Y ≠ 1)
    (hXY : X * Y = Y * X) : False := by
  obtain ⟨a, ha⟩ := hXa
  obtain ⟨b, hb⟩ := hYb
  have hXdvd : orderOf X ∣ 168 := hcard ▸ orderOf_dvd_natCard X
  have hX3o : orderOf X = 3 := by
    rw [ha] at hXdvd ⊢
    have ha1 : a ≤ 1 := by
      by_contra hlt
      have h9 : 3 ^ 2 ∣ 3 ^ a := pow_dvd_pow 3 (by omega)
      have := h9.trans hXdvd
      omega
    have ha0 : a ≠ 0 := by
      rintro rfl
      exact hX (orderOf_eq_one_iff.mp (by simpa using ha))
    have : a = 1 := by omega
    subst this
    norm_num
  have hXcube : X ^ 3 = 1 := by rw [← hX3o]; exact pow_orderOf_eq_one X
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact hY1 (orderOf_eq_one_iff.mp (by simpa using hb))
  set Y' : H := Y ^ (2 ^ (b - 1)) with hY'
  have hYord : orderOf Y' = 2 := by
    rw [hY', orderOf_pow_of_dvd (by positivity) (by rw [hb]; exact pow_dvd_pow 2 (by omega)), hb,
      Nat.pow_div (by omega : b - 1 ≤ b) (by norm_num : 0 < 2)]
    have : b - (b - 1) = 1 := by omega
    rw [this]
  have hY'sq : Y' ^ 2 = 1 := by rw [← hYord]; exact pow_orderOf_eq_one Y'
  have hY'ne : Y' ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hYord
    exact absurd hYord (by norm_num)
  have hc : Commute X Y' := Commute.pow_right hXY _
  have hX6 : X ^ 6 = 1 := by
    rw [show (6 : ℕ) = 3 * 2 from rfl, pow_mul, hXcube, one_pow]
  have hY6 : Y' ^ 6 = 1 := by
    rw [show (6 : ℕ) = 2 * 3 from rfl, pow_mul, hY'sq, one_pow]
  have hZ6 : (X * Y') ^ 6 = 1 := by rw [hc.mul_pow, hX6, hY6, one_mul]
  rcases h6 _ hZ6 with h2 | h3
  · rw [hc.mul_pow, hY'sq, mul_one] at h2
    apply hX
    have : X ^ 3 = X ^ 2 * X := pow_succ X 2
    rw [hXcube, h2, one_mul] at this
    exact this.symm
  · rw [hc.mul_pow, hXcube, one_mul] at h3
    apply hY'ne
    have : Y' ^ 3 = Y' ^ 2 * Y' := pow_succ Y' 2
    rw [h3, hY'sq, one_mul] at this
    exact this.symm

theorem y7c_cent_three_of_iso {Γ : Type} [Group Γ] {J : Subgroup Γ}
    (e : ↥J ≃* Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) {x y : Γ} (hxJ : x ∈ J) (hyJ : y ∈ J)
    (hx : x ≠ 1) (hx3 : IsPGroup 3 ↥(zpowers x)) (hy : IsPGroup 2 ↥(zpowers y))
    (hxy : x * y = y * x) : y = 1 := by
  by_contra hy1
  have hcard : Nat.card (Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) = 168 :=
    CFSG.ComponentClassification.GHarris.card_GL32_gh
  haveI : Finite (Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hord : ∀ (z : Γ) (hz : z ∈ J), orderOf (e ⟨z, hz⟩) = orderOf z := fun z hz => by
    rw [MulEquiv.orderOf_eq e ⟨z, hz⟩, Subgroup.orderOf_mk]
  have hpg : ∀ (p : ℕ) [Fact p.Prime] (z : Γ), IsPGroup p ↥(zpowers z) →
      ∃ n : ℕ, orderOf z = p ^ n := by
    intro p _ z h
    obtain ⟨n, hn⟩ := IsPGroup.iff_orderOf.mp h ⟨z, Subgroup.mem_zpowers z⟩
    exact ⟨n, by rw [← hn, Subgroup.orderOf_mk]⟩
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  obtain ⟨a, ha⟩ := hpg 3 x hx3
  obtain ⟨b, hb⟩ := hpg 2 y hy
  refine y7c_no_six (X := e ⟨x, hxJ⟩) (Y := e ⟨y, hyJ⟩) hcard y7c_gl3_pow6 ?_
    ⟨a, by rw [hord x hxJ, ha]⟩ ⟨b, by rw [hord y hyJ, hb]⟩ ?_ ?_
  · intro h
    apply hx
    have := (e.injective (h.trans (map_one e).symm))
    simpa using congrArg Subtype.val this
  · intro h
    apply hy1
    have := (e.injective (h.trans (map_one e).symm))
    simpa using congrArg Subtype.val this
  · have : (⟨x, hxJ⟩ : ↥J) * ⟨y, hyJ⟩ = ⟨y, hyJ⟩ * ⟨x, hxJ⟩ := Subtype.ext hxy
    rw [← map_mul, ← map_mul, this]

end CFSG.OddStandard.HigherRank.YamadaG23
