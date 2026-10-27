module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Outside.OutFpfComm

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.Outside

open Subgroup

theorem abelian_of_card_sixteen {G : Type} [Group G] [Finite G] (h16 : Nat.card G = 16)
    (ρ : MulAut G) (hρ : ρ ^ 3 = 1) (hfpf : ∀ g : G, ρ g = g → g = 1) (a b : G) :
    a * b = b * a := by
  haveI : Nontrivial G :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [h16]; norm_num)
  have hZmod : Nat.card (center G) % 3 = 1 :=
    card_mod_three_of_fpf ρ hρ hfpf (center G) (fun z hz => rho_mem_center ρ hz)
  have hZdv : Nat.card (center G) ∣ 16 := by
    simpa [h16] using Subgroup.card_subgroup_dvd_card (center G)
  have hZcases : Nat.card (center G) = 1 ∨ Nat.card (center G) = 4 ∨
      Nat.card (center G) = 16 := by
    have hpow : 16 = 2 ^ 4 := by norm_num
    rw [hpow] at hZdv
    obtain ⟨k, hk4, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hZdv
    have hk5 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
    rcases hk5 with rfl | rfl | rfl | rfl | rfl
    · left; simpa using hk
    · exfalso; rw [hk] at hZmod; norm_num at hZmod
    · right; left; simpa using hk
    · exfalso; rw [hk] at hZmod; norm_num at hZmod
    · right; right; simpa using hk
  rcases hZcases with hZ | hZ | hZ
  · exfalso
    have hG2 : IsPGroup 2 G := IsPGroup.of_card (n := 4) (by rw [h16]; norm_num)
    haveI : Nontrivial (center G) := IsPGroup.center_nontrivial hG2
    have h1lt : 1 < Nat.card (center G) := Finite.one_lt_card
    omega
  · exfalso
    have hlag := Subgroup.card_eq_card_quotient_mul_card_subgroup (center G)
    rw [h16, hZ] at hlag
    have hq : Nat.card (G ⧸ center G) = 4 := by omega
    exact card_quot_center_ne_four ρ hρ hfpf hq
  · have htop : center G = ⊤ :=
      Subgroup.eq_top_of_card_eq (center G) (by rw [hZ, h16])
    have ha : a ∈ center G := by rw [htop]; exact Subgroup.mem_top a
    exact (Subgroup.mem_center_iff.mp ha b).symm

end CFSG.OddStandard.SmallF3.HarrisU33.Outside
