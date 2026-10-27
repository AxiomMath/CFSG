module

public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.Tactic.Group
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7

section Pow

theorem exists_zpow_eq_of_pow_eq_one {M : Type*} [Group M] {p m : ℕ} (hm : Nat.Coprime m p)
    {x : M} (hx : x ^ p = 1) : ∃ a : ℤ, x = (x ^ m) ^ a := by
  obtain ⟨a, b, hab⟩ := (Nat.isCoprime_iff_coprime.2 hm : IsCoprime (m : ℤ) (p : ℤ))
  refine ⟨a, ?_⟩
  have h1 : x ^ (b * (p : ℤ)) = 1 := by rw [mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]
  calc x = x ^ (a * (m : ℤ) + b * (p : ℤ)) := by rw [hab, zpow_one]
    _ = (x ^ m) ^ a := by
      rw [zpow_add, h1, mul_one, ← zpow_natCast, ← zpow_mul, mul_comm]

end Pow

section Decomp

variable {M : Type*} [Group M]

theorem decomp_identity {A : Type*} [CommGroup A] {p : ℕ} {c d : ℤ} (hcd : c * 6 + d * p = 1)
    {z₂ g₀ : A} (htp : (z₂ * g₀) ^ p = 1) :
    z₂ * g₀ = (z₂ * (z₂ ^ p) ^ (-d)) * (g₀ ^ 6) ^ c := by
  have h1 : g₀ ^ p = (z₂ ^ p)⁻¹ := by
    rw [mul_pow] at htp
    exact eq_inv_of_mul_eq_one_right htp
  have h6 : (6 : ℤ) * c = 1 + (p : ℤ) * (-d) := by linarith
  have h2 : (g₀ ^ 6) ^ c = g₀ * (z₂ ^ p) ^ d := by
    have e1 : (g₀ ^ 6) ^ c = g₀ ^ ((6 : ℤ) * c) := by
      rw [zpow_mul]; norm_cast
    rw [e1, h6, zpow_add, zpow_one, zpow_mul, zpow_natCast, h1, inv_zpow', neg_neg]
  rw [h2]
  have : (z₂ ^ p) ^ (-d) * (z₂ ^ p) ^ d = 1 := by rw [← zpow_add, neg_add_cancel, zpow_zero]
  calc z₂ * g₀ = z₂ * g₀ * ((z₂ ^ p) ^ (-d) * (z₂ ^ p) ^ d) := by rw [this, mul_one]
    _ = _ := by simp only [mul_assoc, mul_comm, mul_left_comm]

theorem exists_central_mul_of_pow_prime (θ : M →* M) {H Q P : Subgroup M} {p : ℕ}
    (hp3 : 3 < p) (hpp : p.Prime)
    (hH : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a)
    (hθH : ∀ h ∈ H, θ h ∈ H) (hθQ : ∀ g ∈ Q, θ g ∈ Q)
    (hθZ : ∀ z ∈ H, (∀ q ∈ Q, z * q = q * z) → ∀ q ∈ Q, θ z * q = q * θ z)
    (h4 : ∀ t ∈ H, θ t = t → ∃ z ∈ H, (∀ q ∈ Q, z * q = q * z) ∧
      ∃ s ∈ H ⊓ Q, t ^ 6 = z * s)
    (h5 : ∀ f ∈ H ⊓ Q, (∀ q ∈ Q, f * q = q * f) → f ^ 6 = 1)
    (h6 : ∀ g ∈ Q, θ g = g → g ^ 6 ∈ P)
    {t : M} (htH : t ∈ H) (hθt : θ t = t) (htp : t ^ p = 1) :
    ∃ z ∈ H, θ z = z ∧ (∀ q ∈ Q, z * q = q * z) ∧ ∃ x ∈ P, t = z * x := by
  have hc : ∀ a ∈ H, ∀ b ∈ H, Commute a b := fun a ha b hb => hH a ha b hb
  obtain ⟨z, hzH, hzc, s, hsHQ, hts⟩ := h4 t htH hθt
  obtain ⟨hsH, hsQ⟩ := Subgroup.mem_inf.1 hsHQ
  have hθts : θ z * θ s = z * s := by rw [← map_mul, ← hts, map_pow, hθt]
  set f : M := z⁻¹ * θ z with hf
  have hfH : f ∈ H := H.mul_mem (H.inv_mem hzH) (hθH z hzH)
  have hzf : θ z = z * f := by rw [hf]; group
  have hθs : θ s = f⁻¹ * s := by
    have : θ s = (θ z)⁻¹ * (z * s) := by rw [← hθts]; group
    rw [this, hzf]; group
  have hfQ : f ∈ Q := by
    have : f = s * (θ s)⁻¹ := by rw [hθs]; rw [hf, hzf]; group
    rw [this]; exact Q.mul_mem hsQ (Q.inv_mem (hθQ s hsQ))
  have hfc : ∀ q ∈ Q, f * q = q * f := by
    intro q hq
    have h1 : Commute (θ z) q := hθZ z hzH hzc q hq
    have h2 : Commute z q := hzc q hq
    exact (h2.inv_left.mul_left h1).eq
  have hf6 : f ^ 6 = 1 := h5 f (Subgroup.mem_inf.2 ⟨hfH, hfQ⟩) hfc
  have hfc' : Commute z f := hc z hzH f hfH
  have hz6 : θ (z ^ 6) = z ^ 6 := by
    rw [map_pow, hzf, hfc'.mul_pow, hf6, mul_one]
  have hsc : Commute f⁻¹ s := (hc f hfH s hsH).inv_left
  have hs6 : θ (s ^ 6) = s ^ 6 := by
    rw [map_pow, hθs, hsc.mul_pow, inv_pow, hf6, inv_one, one_mul]
  have hzs : Commute z s := hc z hzH s hsH
  have ht36 : t ^ 36 = z ^ 6 * s ^ 6 := by
    rw [show (36 : ℕ) = 6 * 6 by norm_num, pow_mul, hts, hzs.mul_pow]
  have hcop36 : Nat.Coprime 36 p := by
    refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hpp).2 ?_)
    intro hd
    have : p ∣ 2 ^ 2 * 3 ^ 2 := hd
    rcases (Nat.Prime.dvd_mul hpp).1 this with h | h
    · have := Nat.le_of_dvd (by norm_num) (hpp.dvd_of_dvd_pow h); omega
    · have := Nat.le_of_dvd (by norm_num) (hpp.dvd_of_dvd_pow h); omega
  obtain ⟨a, ha⟩ := exists_zpow_eq_of_pow_eq_one hcop36 htp
  set z₂ : M := (z ^ 6) ^ a with hz₂
  set g₀ : M := (s ^ 6) ^ a with hg₀
  have hz6H : z ^ 6 ∈ H := H.pow_mem hzH 6
  have hs6H : s ^ 6 ∈ H := H.pow_mem hsH 6
  have hz₂H : z₂ ∈ H := H.zpow_mem hz6H a
  have hg₀H : g₀ ∈ H := H.zpow_mem hs6H a
  have hg₀Q : g₀ ∈ Q := Q.zpow_mem (Q.pow_mem hsQ 6) a
  have hz₂c : ∀ q ∈ Q, z₂ * q = q * z₂ := by
    intro q hq
    have : Commute z q := hzc q hq
    exact ((this.pow_left 6).zpow_left a).eq
  have hθz₂ : θ z₂ = z₂ := by rw [hz₂, map_zpow, hz6]
  have hθg₀ : θ g₀ = g₀ := by rw [hg₀, map_zpow, hs6]
  have htz : t = z₂ * g₀ := by
    rw [ha, ht36, ((hc _ hz6H _ hs6H)).mul_zpow]
  have hcz₂g : Commute z₂ g₀ := hc z₂ hz₂H g₀ hg₀H
  have htp' : (z₂ * g₀) ^ p = 1 := by rw [← htz]; exact htp
  clear_value z₂ g₀
  have hcop6 : Nat.Coprime 6 p := by
    refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hpp).2 ?_)
    intro hd
    have : p ∣ 2 * 3 := hd
    rcases (Nat.Prime.dvd_mul hpp).1 this with h | h
    · have := Nat.le_of_dvd (by norm_num) h; omega
    · have := Nat.le_of_dvd (by norm_num) h; omega
  obtain ⟨c', d', hcd⟩ := (Nat.isCoprime_iff_coprime.2 hcop6 : IsCoprime ((6 : ℕ) : ℤ) (p : ℤ))
  have hcd' : c' * 6 + d' * p = 1 := by simpa using hcd
  refine ⟨z₂ * (z₂ ^ p) ^ (-d'), H.mul_mem hz₂H (H.zpow_mem (H.pow_mem hz₂H p) _), ?_, ?_,
    (g₀ ^ 6) ^ c', P.zpow_mem (h6 g₀ hg₀Q hθg₀) c', ?_⟩
  · rw [map_mul, hθz₂, map_zpow, map_pow, hθz₂]
  · intro q hq
    have h1 : Commute z₂ q := hz₂c q hq
    exact (h1.mul_left (((h1.pow_left p).zpow_left (-d')))).eq
  ·
    let _ : CommGroup H := { (inferInstance : Group ↥H) with
      mul_comm := fun a b => Subtype.ext (hH a a.2 b b.2) }
    have key := decomp_identity (A := H) (p := p) hcd' (z₂ := ⟨z₂, hz₂H⟩) (g₀ := ⟨g₀, hg₀H⟩)
      (Subtype.ext (by simpa using htp'))
    have := congrArg Subtype.val key
    rw [htz]
    simpa using this

end Decomp

end CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7
