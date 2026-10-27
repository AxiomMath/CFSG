module

public import CFSG.ClassicalInvolution.Q3.TL3T16
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPfGlue

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf

open CFSG CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Q3.TC.Thin

variable {G : Type} [Group G]

theorem e8_centralizes {X E : Subgroup G} (hE : E8Struct X E) {J : Subgroup G} {z : G}
    (hz : z ∈ J) (hzE : z ∈ E)
    (htr : ∀ k ∈ J, ∀ e ∈ E, k * e * k⁻¹ = e ∨ k * e * k⁻¹ = z * e)
    (hC : ∀ e ∈ E, (∀ k ∈ J, k * e = e * k) → e = 1 ∨ e = z)
    {y : G} (hy : y ∈ Subgroup.normalizer (X : Set G)) (hy3 : ∃ a : ℕ, y ^ 3 ^ a = 1)
    (hyJ : ∀ k ∈ J, y * k = k * y) : ∀ x ∈ X, y * x = x * y := by
  obtain ⟨a, ha⟩ := hy3
  have hN : Odd (3 ^ a) := Odd.pow (by decide)
  have hyz : y * z = z * y := hyJ z hz
  have hcomm : ∀ {a b : G}, a ∈ E → b ∈ E → a * b = b * a := fun ha hb => comm_of_sq hE.sq ha hb
  have hy' : y⁻¹ ∈ Subgroup.normalizer (X : Set G) := (Subgroup.normalizer _).inv_mem hy
  have hyE : ∀ e ∈ E, y * e * y⁻¹ ∈ E := by
    intro e he
    have h2 : IsPGroup 2 ↥(conjSub y E) := by
      intro q
      refine ⟨1, ?_⟩
      obtain ⟨e', he', hq⟩ := q.2
      apply Subtype.ext
      have : (e' * e') = 1 := hE.sq e' he'
      show (q : G) ^ 2 ^ 1 = 1
      rw [← hq]
      show (MulAut.conj y e') ^ 2 ^ 1 = 1
      rw [pow_one, ← map_pow, pow_two, this, map_one]
    have hle : conjSub y E ≤ E := by
      refine hE.core _ ?_ ?_ h2
      · rintro _ ⟨e', he', rfl⟩
        exact conj_mem_of_normalizer hy (hE.le he')
      · intro x hx q hq
        rw [mem_conjSub_iff]
        have hq' := mem_conjSub_iff.mp hq
        have hx' : y⁻¹ * x * y ∈ X := by simpa using conj_mem_of_normalizer hy' hx
        have := hE.normal _ hx' _ hq'
        convert this using 1
        group
    exact hle ⟨e, he, rfl⟩
  have hw : ∀ e ∈ E, y * e * y⁻¹ * e⁻¹ = 1 ∨ y * e * y⁻¹ * e⁻¹ = z := by
    intro e he
    have hwE : y * e * y⁻¹ * e⁻¹ ∈ E := E.mul_mem (hyE e he) (E.inv_mem he)
    refine hC _ hwE fun k hk => ?_
    have hyk : y * k = k * y := hyJ k hk
    have hkk : k * y * k⁻¹ = y := by rw [← hyk]; group
    have hkk' : k * y⁻¹ * k⁻¹ = y⁻¹ := by
      calc k * y⁻¹ * k⁻¹ = (k * y * k⁻¹)⁻¹ := by group
        _ = y⁻¹ := by rw [hkk]
    have hkw : k * (y * e * y⁻¹ * e⁻¹) * k⁻¹ = y * (k * e * k⁻¹) * y⁻¹ * (k * e * k⁻¹)⁻¹ := by
      calc k * (y * e * y⁻¹ * e⁻¹) * k⁻¹
          = (k * y * k⁻¹) * (k * e * k⁻¹) * (k * y⁻¹ * k⁻¹) * (k * e * k⁻¹)⁻¹ := by group
        _ = _ := by rw [hkk, hkk']
    have hkwz : k * (y * e * y⁻¹ * e⁻¹) * k⁻¹ = y * e * y⁻¹ * e⁻¹ := by
      rw [hkw]
      rcases htr k hk e he with h | h
      · rw [h]
      · rw [h]
        have h1 : y * (z * e) * y⁻¹ * (z * e)⁻¹ = z * (y * e * y⁻¹ * e⁻¹) * z⁻¹ := by
          calc y * (z * e) * y⁻¹ * (z * e)⁻¹ = (y * z * y⁻¹) * (y * e * y⁻¹) * e⁻¹ * z⁻¹ := by
                group
            _ = z * (y * e * y⁻¹ * e⁻¹) * z⁻¹ := by
                rw [show y * z * y⁻¹ = z by rw [hyz]; group]; group
        rw [h1, hcomm hzE hwE]
        group
    calc k * (y * e * y⁻¹ * e⁻¹) = (k * (y * e * y⁻¹ * e⁻¹) * k⁻¹) * k := by group
      _ = (y * e * y⁻¹ * e⁻¹) * k := by rw [hkwz]
  have hyE' : ∀ e ∈ E, y * e = e * y := by
    intro e he
    rcases hw e he with h | h
    · calc y * e = (y * e * y⁻¹ * e⁻¹) * e * y := by group
        _ = e * y := by rw [h, one_mul]
    · have h1 : y * e * y⁻¹ = z * e := by
        calc y * e * y⁻¹ = (y * e * y⁻¹ * e⁻¹) * e := by group
          _ = z * e := by rw [h]
      have key : ∀ k : ℕ, y ^ k * e * (y ^ k)⁻¹ = z ^ k * e := by
        intro k
        induction k with
        | zero => simp
        | succ k ih =>
          have hzk : y * z ^ k * y⁻¹ = z ^ k := by
            have := (show Commute y z from hyz).pow_right k
            rw [this.eq]; group
          calc y ^ (k + 1) * e * (y ^ (k + 1)) ⁻¹ = y * (y ^ k * e * (y ^ k)⁻¹) * y⁻¹ := by
                rw [pow_succ']; group
            _ = (y * z ^ k * y⁻¹) * (y * e * y⁻¹) := by rw [ih]; group
            _ = z ^ (k + 1) * e := by rw [hzk, h1, pow_succ']; group
      have h2 := key (3 ^ a)
      rw [ha, inv_one, one_mul, mul_one] at h2
      have hzz : z * z = 1 := hE.sq z hzE
      have hzN : z ^ 3 ^ a = z := by
        obtain ⟨m, hm⟩ := hN
        rw [hm, pow_succ, pow_mul, sq, hzz, one_pow, one_mul]
      rw [hzN] at h2
      have hz1 : z = 1 := by
        have h3 : z * e = 1 * e := by rw [← h2, one_mul]
        exact mul_right_cancel h3
      rw [hz1] at h1
      calc y * e = (y * e * y⁻¹) * y := by group
        _ = e * y := by rw [h1, one_mul]
  have hδ : ∀ x ∈ X, x⁻¹ * (y * x * y⁻¹) ∈ E := by
    intro x hx
    have hyxX : y * x * y⁻¹ ∈ X := conj_mem_of_normalizer hy hx
    refine hE.cent _ (X.mul_mem (X.inv_mem hx) hyxX) fun e he => ?_
    have hxe : x * e * x⁻¹ ∈ E := hE.normal x hx e he
    have h1 : y * (x * e * x⁻¹) = (x * e * x⁻¹) * y := hyE' _ hxe
    have h2 : y⁻¹ * e * y = e := by
      calc y⁻¹ * e * y = y⁻¹ * (e * y) := by group
        _ = y⁻¹ * (y * e) := by rw [hyE' e he]
        _ = e := by group
    calc x⁻¹ * (y * x * y⁻¹) * e = x⁻¹ * y * x * (y⁻¹ * e * y) * y⁻¹ := by group
      _ = x⁻¹ * (y * (x * e * x⁻¹)) * x * y⁻¹ := by rw [h2]; group
      _ = x⁻¹ * ((x * e * x⁻¹) * y) * x * y⁻¹ := by rw [h1]
      _ = e * (x⁻¹ * (y * x * y⁻¹)) := by group
  intro x hx
  set d := x⁻¹ * (y * x * y⁻¹) with hd
  have hdE : d ∈ E := hδ x hx
  have hdd : d * d = 1 := hE.sq d hdE
  have hdy : ∀ k : ℕ, y * d ^ k * y⁻¹ = d ^ k := by
    intro k
    have := hyE' _ (E.pow_mem hdE k)
    rw [this]; group
  have key : ∀ k : ℕ, y ^ k * x * (y ^ k)⁻¹ = x * d ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc y ^ (k + 1) * x * (y ^ (k + 1))⁻¹ = y * (y ^ k * x * (y ^ k)⁻¹) * y⁻¹ := by
            rw [pow_succ']; group
        _ = (y * x * y⁻¹) * (y * d ^ k * y⁻¹) := by rw [ih]; group
        _ = x * d ^ (k + 1) := by
            rw [hdy k, pow_succ', show y * x * y⁻¹ = x * d by rw [hd]; group]; group
  have h2 := key (3 ^ a)
  rw [ha, inv_one, one_mul, mul_one] at h2
  have hdN : d ^ 3 ^ a = d := by
    obtain ⟨m, hm⟩ := hN
    rw [hm, pow_succ, pow_mul, sq, hdd, one_pow, one_mul]
  rw [hdN] at h2
  have hd1 : d = 1 := by
    have h3 : x * d = x * 1 := by rw [← h2, mul_one]
    exact mul_left_cancel h3
  have : y * x * y⁻¹ = x := by
    calc y * x * y⁻¹ = x * (x⁻¹ * (y * x * y⁻¹)) := by group
      _ = x := by rw [← hd, hd1, mul_one]
  calc y * x = (y * x * y⁻¹) * y := by group
    _ = x * y := by rw [this]

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf
