module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.Models1

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec13

open Subgroup
open scoped commutatorElement

namespace UT3

variable {F : Type*} [CommRing F]

theorem commutator_eq (u v : UT3 F) :
    ⁅u, v⁆ = ⟨0, 0, u.a * v.b - v.a * u.b⟩ := by
  ext <;> simp [commutatorElement_def]
  ring

end UT3

theorem exists_tau_eq (a : GaloisField 2 4) : ∃ c : GaloisField 2 4, c + c ^ 4 = a * a ^ 4 := by
  have h16 : (a ^ 4) ^ 4 = a := by rw [← pow_mul]; exact gf16_pow16 a
  have hk : a * a ^ 4 ∈ tauHom.ker := by
    rw [AddMonoidHom.mem_ker, tau_apply, mul_pow, h16]
    linear_combination (a * a ^ 4) * gf16_char2
  rw [← range_tau_eq_ker] at hk
  obtain ⟨c, hc⟩ := hk
  exact ⟨c, hc⟩

theorem card_fiber_tau (y : GaloisField 2 4) (hy : y ∈ tauHom.range) :
    Nat.card {c : GaloisField 2 4 // c + c ^ 4 = y} = 4 := by
  obtain ⟨c₀, hc₀⟩ := hy
  have e : {c : GaloisField 2 4 // c + c ^ 4 = y} ≃ tauHom.ker :=
    { toFun := fun c => ⟨c.1 - c₀, by
        rw [AddMonoidHom.mem_ker, map_sub, hc₀]
        have : tauHom c.1 = y := c.2
        rw [this]; simp⟩
      invFun := fun k => ⟨k.1 + c₀, by
        have hk : tauHom k.1 = 0 := k.2
        have : tauHom (k.1 + c₀) = y := by rw [map_add, hk, hc₀]; simp
        exact this⟩
      left_inv := fun c => by ext; simp
      right_inv := fun k => by ext; simp }
  rw [Nat.card_congr e, card_ker_tau]

theorem card_SylSU34 : Nat.card SylSU34 = 64 := by
  classical
  have e : SylSU34 ≃ Σ a : GaloisField 2 4, {c : GaloisField 2 4 // c + c ^ 4 = a * a ^ 4} :=
    { toFun := fun u => ⟨u.1.a, u.1.c, by
        have h := ((mem_SylSU34_iff u.1).1 u.2).2
        linear_combination h + (-(u.1.a * u.1.a ^ 4)) * gf16_char2⟩
      invFun := fun p => ⟨⟨p.1, p.1 ^ 4, p.2.1⟩, (mem_SylSU34_iff _).2 ⟨rfl, by
        have h := p.2.2
        linear_combination h + (p.1 * p.1 ^ 4) * gf16_char2⟩⟩
      left_inv := fun u => by
        obtain ⟨⟨a, b, c⟩, hu⟩ := u
        have hb : b = a ^ 4 := ((mem_SylSU34_iff _).1 hu).1
        subst hb
        rfl
      right_inv := fun p => by
        obtain ⟨a, c, hc⟩ := p
        rfl }
  rw [Nat.card_congr e]
  have : Fintype (GaloisField 2 4) := Fintype.ofFinite _
  have hK : Nat.card (GaloisField 2 4) = 16 := by
    have := GaloisField.card 2 4 (by norm_num)
    simpa using this
  have hfib : ∀ a : GaloisField 2 4, Nat.card {c : GaloisField 2 4 // c + c ^ 4 = a * a ^ 4} = 4 := by
    intro a
    apply card_fiber_tau
    obtain ⟨c, hc⟩ := exists_tau_eq a
    exact ⟨c, hc⟩
  have h2 : Nat.card (Σ a : GaloisField 2 4, {c : GaloisField 2 4 // c + c ^ 4 = a * a ^ 4}) =
      ∑ a : GaloisField 2 4, Nat.card {c : GaloisField 2 4 // c + c ^ 4 = a * a ^ 4} := by
    rw [Nat.card_sigma]
  rw [h2]
  simp only [hfib, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [← Nat.card_eq_fintype_card, hK]

end CFSG.GH74.GLS.Stage1.Thm6.Sec13

