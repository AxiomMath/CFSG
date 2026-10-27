module

public import CFSG.GH74.Generic.S1.KL3Cfg
public import CFSG.GH74.GLS.IVK.Proofs2.GHInvExcShape

public section

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab
  CFSG.GH74.GLS.IVK.GHInv CFSG.ClassicalInvolution
open scoped MatrixGroups

namespace CFSG.GH74.Generic.S1

theorem kl3_shape_card_three {Y : Type} [Group Y] {F₁ F₂ : Type} [Field F₁] [Field F₂] [Finite F₁]
    (hodd : Odd (Nat.card F₁)) (Sh : Shape Y F₁ F₂) (hY : Group.IsSolvable Y) : Nat.card F₁ = 3 := by
  have h1 : Group.IsSolvable ↥Sh.I₁ := inferInstance
  have h2 : Group.IsSolvable SL(2, F₁) :=
    Group.isSolvable_of_isSolvable_injective (f := Sh.e₁.symm.toMonoidHom) Sh.e₁.symm.injective
  exact natCard_eq_three_of_isSolvable_sl2 hodd h2

theorem kl3_prime_pow_eq_three {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (h : p ^ f = 3) :
    p = 3 ∧ f = 1 := by
  have hpd : p ∣ 3 := h ▸ dvd_pow_self p (by omega : f ≠ 0)
  have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 hpd
  subst hp3
  refine ⟨rfl, ?_⟩
  exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) (by simpa using h)

theorem kl3FamG2 : KL3FamG2 := by
  intro S _ _ _ p f hp hp2 hf hM F _ _ Pb yb hcfg
  obtain ⟨-, -, -, hy2, hsolv⟩ := hcfg
  obtain ⟨F₀, hF₀, hFin, Sh, hcard, -⟩ := exists_shape_G2 hp hp2 hM yb hy2
  have hodd : Odd (Nat.card F₀) := by rw [hcard]; exact (hp.odd_of_ne_two hp2).pow
  have h3 := kl3_shape_card_three hodd Sh hsolv
  rw [hcard] at h3
  exact kl3_prime_pow_eq_three hp hf h3

theorem kl3FamD4 : KL3FamD4 := by
  intro S _ _ _ p f hp hp2 hf hM F _ _ Pb yb hcfg
  obtain ⟨-, -, -, hy2, hsolv⟩ := hcfg
  obtain ⟨F₁, F₂, hF₁, hF₂, hFin₁, hFin₂, Sh, hc₁, -, -⟩ := exists_shape_D4 hp hp2 hM yb hy2
  have hodd : Odd (Nat.card F₁) := by
    rw [hc₁]
    exact ((hp.odd_of_ne_two hp2).pow).pow
  have h3 := kl3_shape_card_three hodd Sh hsolv
  rw [hc₁] at h3
  have hq : 2 ≤ p ^ f := by
    calc 2 ≤ p := hp.two_le
      _ ≤ p ^ f := Nat.le_self_pow (by omega) p
  have : 8 ≤ (p ^ f) ^ 3 := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ (p ^ f) ^ 3 := Nat.pow_le_pow_left hq 3
  omega

end CFSG.GH74.Generic.S1
