module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx29
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx31

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
open scoped commutatorElement Pointwise

namespace Setup8

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ W₁ W₂ U : Subgroup G} {u h : G}

theorem w_inv_A (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) (hk : Nat.card ↥(Vof S K₁ W₂) = 2 ^ (1 + 1)) {t w : G}
    (htS : t ∈ S) (ht2 : t * t = 1) (htu : t * u * t⁻¹ = u * z) (hwW : w ∈ Wsub S U)
    (htw : t * w = w * t) (hwh : w * h = h * w) (hw1 : w ≠ 1) :
    ∀ a ∈ Aof S K₁ W₂ h, w * a * w⁻¹ = a⁻¹ := by
  obtain ⟨x, hVx, -, -, -, hz⟩ := hs.xdata hII hq hk
  have hxV : x ∈ Vof S K₁ W₂ := hVx ▸ Subgroup.mem_zpowers x
  have hxA : x ∈ Aof S K₁ W₂ h := Subgroup.mem_sup_left hxV
  have hx'A : h⁻¹ * x * h ∈ Aof S K₁ W₂ h := (hs.A_conj hII hq hrec hk hxA).2
  have hcommA := hs.A_comm hII hq hrec
  have hzz : z * z = 1 := hs.z_sq
  have hx4 : x * x * (x * x) = 1 := by rw [← hz]; exact hzz
  have hwU : ∀ c ∈ U, w * c * w⁻¹ = c := fun c hc => hs.W_cent_U hwW hc
  have hwh' : h * w * h⁻¹ = w := by
    calc h * w * h⁻¹ = (h * w) * h⁻¹ := rfl
      _ = (w * h) * h⁻¹ := by rw [hwh]
      _ = w := by group
  have htw'' : t⁻¹ * w * t = w := by
    calc t⁻¹ * w * t = t⁻¹ * (w * t) := by group
      _ = t⁻¹ * (t * w) := by rw [htw]
      _ = w := by group
  have hεh : ∀ a : G, (w * (h⁻¹ * a * h) * w⁻¹) * (h⁻¹ * a * h)⁻¹ =
      h⁻¹ * ((w * a * w⁻¹) * a⁻¹) * h := by
    intro a
    calc (w * (h⁻¹ * a * h) * w⁻¹) * (h⁻¹ * a * h)⁻¹
        = h⁻¹ * ((h * w * h⁻¹) * a * (h * w * h⁻¹)⁻¹) * h * (h⁻¹ * a * h)⁻¹ := by group
      _ = h⁻¹ * ((w * a * w⁻¹) * a⁻¹) * h := by rw [hwh']; group
  have hεt : ∀ a : G, (w * (t * a * t⁻¹) * w⁻¹) * (t * a * t⁻¹)⁻¹ =
      t * ((w * a * w⁻¹) * a⁻¹) * t⁻¹ := by
    intro a
    calc (w * (t * a * t⁻¹) * w⁻¹) * (t * a * t⁻¹)⁻¹
        = t * ((t⁻¹ * w * t) * a * (t⁻¹ * w * t)⁻¹ * a⁻¹) * t⁻¹ := by group
      _ = t * ((w * a * w⁻¹) * a⁻¹) * t⁻¹ := by rw [htw'']
  have he₁U : (w * x * w⁻¹) * x⁻¹ ∈ U := hs.eps_mem_U hII hq hrec hk hwW hxA
  have hx'' : t * x * t⁻¹ ∈ Aof S K₁ W₂ h := hs.A_normS hII hq hrec htS hxA
  have hxx'' : (t * x * t⁻¹) * (t * x * t⁻¹) = z := by
    calc (t * x * t⁻¹) * (t * x * t⁻¹) = t * (x * x) * t⁻¹ := by group
      _ = t * z * t⁻¹ := by rw [← hz]
      _ = z := by rw [← hs.z_comm hII htS]; group
  have hu₀A : x⁻¹ * (t * x * t⁻¹) ∈ Aof S K₁ W₂ h := mul_mem (inv_mem hxA) hx''
  have hu₀U : x⁻¹ * (t * x * t⁻¹) ∈ U := by
    apply hs.A_inv_mem_U hII hq hrec hu₀A
    have hc : (t * x * t⁻¹) * x⁻¹ = x⁻¹ * (t * x * t⁻¹) := hcommA _ hx'' _ (inv_mem hxA)
    calc x⁻¹ * (t * x * t⁻¹) * (x⁻¹ * (t * x * t⁻¹))
        = x⁻¹ * ((t * x * t⁻¹) * x⁻¹) * (t * x * t⁻¹) := by group
      _ = x⁻¹ * (x⁻¹ * (t * x * t⁻¹)) * (t * x * t⁻¹) := by rw [hc]
      _ = (x * x)⁻¹ * ((t * x * t⁻¹) * (t * x * t⁻¹)) := by group
      _ = 1 := by rw [hxx'', ← hz, inv_mul_cancel]
  have hεx'' : (w * (t * x * t⁻¹) * w⁻¹) * (t * x * t⁻¹)⁻¹ = (w * x * w⁻¹) * x⁻¹ := by
    have e : t * x * t⁻¹ = x * (x⁻¹ * (t * x * t⁻¹)) := by group
    generalize hu₀ : x⁻¹ * (t * x * t⁻¹) = u₀ at e hu₀U
    rw [e]
    calc (w * (x * u₀) * w⁻¹) * (x * u₀)⁻¹
        = (w * x * w⁻¹) * (w * u₀ * w⁻¹) * u₀⁻¹ * x⁻¹ := by group
      _ = (w * x * w⁻¹) * u₀ * u₀⁻¹ * x⁻¹ := by rw [hwU u₀ hu₀U]
      _ = (w * x * w⁻¹) * x⁻¹ := by group
  have he₁t : t * ((w * x * w⁻¹) * x⁻¹) * t⁻¹ = (w * x * w⁻¹) * x⁻¹ :=
    (hεt x).symm.trans hεx''
  have hzt : t * z * t⁻¹ = z := by rw [← hs.z_comm hII htS]; group
  have he₁ : (w * x * w⁻¹) * x⁻¹ = 1 ∨ (w * x * w⁻¹) * x⁻¹ = z := by
    rcases hs.U_elems _ he₁U with h1 | h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1
    · exfalso
      rw [h1, htu] at he₁t
      apply hs.z_ne
      have : u * z = u * 1 := by rw [mul_one]; exact he₁t
      exact mul_left_cancel this
    · exfalso
      rw [h1] at he₁t
      have h2 : t * (u * z) * t⁻¹ = u := by
        calc t * (u * z) * t⁻¹ = (t * u * t⁻¹) * (t * z * t⁻¹) := by group
          _ = (u * z) * z := by rw [htu, hzt]
          _ = u := by rw [mul_assoc, hzz, mul_one]
      rw [h2] at he₁t
      apply hs.z_ne
      have : u * 1 = u * z := by rw [mul_one]; exact he₁t
      exact (mul_left_cancel this).symm
  have he₁ne : (w * x * w⁻¹) * x⁻¹ ≠ 1 := by
    intro h1
    have hwx : x * w = w * x := by
      have : w * x * w⁻¹ = x := mul_inv_eq_one.1 h1
      calc x * w = (w * x * w⁻¹) * w := by rw [this]
        _ = w * x := by group
    have h2 : (w * (h⁻¹ * x * h) * w⁻¹) * (h⁻¹ * x * h)⁻¹ = 1 := by rw [hεh, h1]; group
    have hwx' : (h⁻¹ * x * h) * w = w * (h⁻¹ * x * h) := by
      have : w * (h⁻¹ * x * h) * w⁻¹ = h⁻¹ * x * h := mul_inv_eq_one.1 h2
      calc (h⁻¹ * x * h) * w = (w * (h⁻¹ * x * h) * w⁻¹) * w := by rw [this]
        _ = w * (h⁻¹ * x * h) := by group
    have hwA : w ∈ Aof S K₁ W₂ h := hs.mem_A_of_fix hII hq hrec hVx hwW.1 hwx hwx'
    apply hw1
    apply hs.A_fixed_trivial hII hq hrec hk hwA
    calc h⁻¹ * w * h = h⁻¹ * (w * h) := by group
      _ = h⁻¹ * (h * w) := by rw [hwh]
      _ = w := by group
  have hε₁ : (w * x * w⁻¹) * x⁻¹ = z := he₁.resolve_left he₁ne
  have hxinv : x⁻¹ = x * x * x := inv_eq_of_mul_eq_one_right (by
    calc x * (x * x * x) = x * x * (x * x) := by group
      _ = 1 := hx4)
  have hwx : w * x * w⁻¹ = x⁻¹ := by
    calc w * x * w⁻¹ = ((w * x * w⁻¹) * x⁻¹) * x := by group
      _ = z * x := by rw [hε₁]
      _ = x⁻¹ := by rw [hz, hxinv]
  have hx'x' : (h⁻¹ * x * h) * (h⁻¹ * x * h) = h⁻¹ * z * h := by
    calc (h⁻¹ * x * h) * (h⁻¹ * x * h) = h⁻¹ * (x * x) * h := by group
      _ = h⁻¹ * z * h := by rw [← hz]
  have hx'4 : (h⁻¹ * x * h) * (h⁻¹ * x * h) * ((h⁻¹ * x * h) * (h⁻¹ * x * h)) = 1 := by
    calc (h⁻¹ * x * h) * (h⁻¹ * x * h) * ((h⁻¹ * x * h) * (h⁻¹ * x * h))
        = h⁻¹ * (x * x * (x * x)) * h := by group
      _ = 1 := by rw [hx4]; group
  have hx'inv : (h⁻¹ * x * h)⁻¹ = (h⁻¹ * x * h) * (h⁻¹ * x * h) * (h⁻¹ * x * h) :=
    inv_eq_of_mul_eq_one_right (by
      calc (h⁻¹ * x * h) * ((h⁻¹ * x * h) * (h⁻¹ * x * h) * (h⁻¹ * x * h))
          = (h⁻¹ * x * h) * (h⁻¹ * x * h) * ((h⁻¹ * x * h) * (h⁻¹ * x * h)) := by group
        _ = 1 := hx'4)
  have hwx' : w * (h⁻¹ * x * h) * w⁻¹ = (h⁻¹ * x * h)⁻¹ := by
    have h3 := hεh x
    rw [hε₁] at h3
    calc w * (h⁻¹ * x * h) * w⁻¹
        = ((w * (h⁻¹ * x * h) * w⁻¹) * (h⁻¹ * x * h)⁻¹) * (h⁻¹ * x * h) := by group
      _ = (h⁻¹ * z * h) * (h⁻¹ * x * h) := by rw [h3]
      _ = (h⁻¹ * x * h)⁻¹ := by rw [← hx'x', hx'inv]
  have hzx : zpowers x ≤ Aof S K₁ W₂ h := zpowers_le.2 hxA
  have hzx' : zpowers (h⁻¹ * x * h) ≤ Aof S K₁ W₂ h := zpowers_le.2 hx'A
  have hcx : ∀ p ∈ zpowers x, ∀ q ∈ zpowers (h⁻¹ * x * h), p * q = q * p :=
    fun p hp q hq => hcommA p (hzx hp) q (hzx' hq)
  intro a ha
  have hle := hs.A_le_gen hII hq hrec hVx ha
  obtain ⟨p, hp, q, hq, rfl⟩ := Basic.mem_sup_of_le_normalizer' (A := zpowers x)
    (B := zpowers (h⁻¹ * x * h))
    (Basic.le_normalizer_of_commute' (A := zpowers (h⁻¹ * x * h)) (B := zpowers x)
      (fun a ha b hb => (hcx b hb a ha).symm)) hle
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hp
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hq
  have hp' : w * x ^ i * w⁻¹ = (x ^ i)⁻¹ := by
    rw [(conj_zpow).symm, hwx, inv_zpow]
  have hq' : w * (h⁻¹ * x * h) ^ j * w⁻¹ = ((h⁻¹ * x * h) ^ j)⁻¹ := by
    rw [(conj_zpow).symm, hwx', inv_zpow]
  have hc := hcx (x ^ i) hp ((h⁻¹ * x * h) ^ j) hq
  calc w * (x ^ i * (h⁻¹ * x * h) ^ j) * w⁻¹
      = (w * x ^ i * w⁻¹) * (w * (h⁻¹ * x * h) ^ j * w⁻¹) := by group
    _ = (x ^ i)⁻¹ * ((h⁻¹ * x * h) ^ j)⁻¹ := by rw [hp', hq']
    _ = (x ^ i * (h⁻¹ * x * h) ^ j)⁻¹ := by
      rw [mul_inv_rev, ← (Commute.inv_inv (show Commute (x ^ i) ((h⁻¹ * x * h) ^ j) from hc)).eq]

end Setup8

end CFSG.GH74.GLS.Stage1.Thm3.Sec8
