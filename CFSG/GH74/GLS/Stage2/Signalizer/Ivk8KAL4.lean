module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8Stmt813
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAL4Cls

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.GH74.GLS.Stage2.Signalizer.Odd87

theorem kay_L4_of_classes (h3 : KAL4B3) (h2 : KAL4B2) (h2' : KAL4B2Three) (hNS : KAL4NS)
    (hO : KAL4GOrth) (hO' : KAL4GOrthThree) (hS : KAL4GSp) : KAY FL4 := by
  intro Y _ _ hY _ α hα2 hα1 p hp hp2 P hPp hP1 hcomm hnorm
  obtain ⟨p0, f0, hp0, hf0, hp02, hq8, hL⟩ := hY
  obtain ⟨F, _, _, hcard, ⟨e⟩⟩ := LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hL
  have : Fact p0.Prime := ⟨hp0⟩
  have : CharP F p0 := by
    have := Fintype.ofFinite F
    exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hcard])
  have hK2 : ringChar F ≠ 2 := by rwa [ringChar.eq F p0]
  have hpodd : p0 % 2 = 1 := Nat.odd_iff.mp (hp0.odd_of_ne_two hp02)
  have hfodd : Odd f0 := by
    by_contra hnot
    obtain ⟨m, rfl⟩ := Nat.not_odd_iff_even.mp hnot
    have hsq : p0 ^ (m + m) = (p0 ^ m) ^ 2 := by ring
    rw [hsq] at hq8
    have hm : p0 ^ m % 2 = 1 := by
      rw [Nat.pow_mod, hpodd]
      simp
    have h8 : ∀ a : ℕ, a % 2 = 1 → a ^ 2 % 8 = 1 := by
      intro a ha
      have := Nat.mod_lt a (by norm_num : 8 > 0)
      interval_cases h : a % 8 <;> simp [Nat.pow_mod, h] <;> omega
    exact hq8 (h8 _ hm)
  have hα'2 : MulAut.congr e α * MulAut.congr e α = 1 := by rw [← map_mul, hα2, map_one]
  have hα'1 : MulAut.congr e α ≠ 1 := fun h =>
    hα1 ((MulAut.congr e).injective (by rw [h, map_one]))
  have hK : KAAll (MulAut.congr e α) :=
    kaAll_pl4 h3 h2 h2' hNS hO hO' hS hp0 hf0 hcard hfodd hK2 hα'2 hα'1
  have h := KAAll.of_mulEquiv e.symm hK
  have key : MulAut.congr e.symm (MulAut.congr e α) = α := by
    ext y
    simp [MulAut.congr_apply]
  rw [key] at h
  have hc := h p hp hp2 P ⟨hPp, hP1, hcomm, hnorm⟩
  exact ⟨hc.1, Or.inl hc.2⟩

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
