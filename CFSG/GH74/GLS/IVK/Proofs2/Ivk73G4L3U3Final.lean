module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4Leaf2
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4L3U3Small
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4U3Out

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup CFSG CFSG.ABGLocalTools Blueprint

@[expose] def IVK73_L3even : Prop :=
  Ivk73Empty fun X _ => ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ Even f ∧ LieModel X .PSL 3 p f

theorem odd_prime_pow_eq_three_or_five_le {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) :
    (p = 3 ∧ f = 1) ∨ 5 ≤ p ^ f := by
  have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    have := hp.odd_of_ne_two hp2
    obtain ⟨k, hk⟩ := this
    omega
  have hpf : p ≤ p ^ f := Nat.le_self_pow (by omega) p
  obtain ⟨k, hk⟩ := hodd
  by_cases h5 : 5 ≤ p ^ f
  · exact Or.inr h5
  · left
    have h3 : p ^ f = 3 := by omega
    have hpd : p ∣ 3 := by rw [← h3]; exact dvd_pow_self p (by omega)
    have hp3' : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 hpd
    subst hp3'
    refine ⟨rfl, ?_⟩
    by_contra hne
    have : 3 ^ 2 ≤ 3 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

theorem ivk73_L3U3_of_even
    (h : IVK73_L3even) : IVK73_L3U3 := by
  rintro N _ _ L K Q hcfg ⟨p, f, hp, hp2, hf, hL | hU⟩
  · rcases odd_prime_pow_eq_three_or_five_le hp hp2 hf with ⟨rfl, rfl⟩ | h5
    · exact ivk73_l33 N L K Q hcfg hL
    · rcases Nat.even_or_odd f with hev | hodd
      · exact h N L K Q hcfg ⟨p, f, hp, hp2, hf, hev, hL⟩
      · exact ivk73_l3_odd hp hp2 h5 hodd N L K Q hcfg hL
  · rcases odd_prime_pow_eq_three_or_five_le hp hp2 hf with ⟨rfl, rfl⟩ | h5
    · exact ivk73_u33 N L K Q hcfg hU
    · exact ivk73_u3 hp hp2 h5 N L K Q hcfg hU

end CFSG.GH74.GLS.IVK
