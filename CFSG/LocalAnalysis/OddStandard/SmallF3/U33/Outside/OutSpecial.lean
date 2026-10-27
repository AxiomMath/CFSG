module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Outside.OutCenterAut
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Outside.OutOrder16

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.Outside

open Subgroup
open scoped commutatorElement

structure FpfNonab (S : Type) [Group S] (ρ : MulAut S) : Prop where
  card : Nat.card S = 64
  nonab : ∃ a b : S, a * b ≠ b * a
  cube : ρ ^ 3 = 1
  fpf : ∀ g : S, ρ g = g → g = 1

structure FpfSpecial (S : Type) [Group S] : Prop where
  card_center : Nat.card (center S) = 4
  sq_center : ∀ z ∈ center S, z * z = 1
  comm_mem : ∀ g h : S, g * h * g⁻¹ * h⁻¹ ∈ center S
  sq_mem : ∀ g : S, g * g ∈ center S
  card_quot : Nat.card (S ⧸ center S) = 16
  commutator_eq : commutator S = center S

variable {S : Type} [Group S] [Finite S] {ρ : MulAut S}

theorem FpfNonab.card_center (h : FpfNonab S ρ) : Nat.card (center S) = 4 := by
  haveI hP : IsPGroup 2 S := IsPGroup.of_card (n := 6) (by rw [h.card]; norm_num)
  haveI hntS : Nontrivial S := by
    rw [← Finite.one_lt_card_iff_nontrivial, h.card]; norm_num
  haveI hntZ : Nontrivial (center S) := IsPGroup.center_nontrivial (p := 2) (G := S) hP
  have hmod : Nat.card (center S) % 3 = 1 :=
    card_mod_three_of_fpf ρ h.cube h.fpf (center S) (fun z hz => rho_mem_center ρ hz)
  have hdvd : Nat.card (center S) ∣ 2 ^ 6 := by
    have hdvd0 := Subgroup.card_subgroup_dvd_card (center S)
    rw [h.card] at hdvd0
    simpa only [show (2 : ℕ) ^ 6 = 64 by norm_num] using hdvd0
  obtain ⟨k, hk6, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hmodk : 2 ^ k % 3 = 1 := by rw [← hk]; exact hmod
  have hk0 : 0 ≤ k := by omega
  have hkcase : k = 0 ∨ k = 2 ∨ k = 4 ∨ k = 6 := by
    interval_cases k
    · exact Or.inl rfl
    · exfalso; norm_num at hmodk
    · exact Or.inr (Or.inl rfl)
    · exfalso; norm_num at hmodk
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exfalso; norm_num at hmodk
    · exact Or.inr (Or.inr (Or.inr rfl))
  rcases hkcase with rfl | rfl | rfl | rfl
  · rw [pow_zero] at hk
    have hlt : 1 < Nat.card (center S) := Finite.one_lt_card
    omega
  · rw [show (2 : ℕ) ^ 2 = 4 by norm_num] at hk
    exact hk
  · rw [show (2 : ℕ) ^ 4 = 16 by norm_num] at hk
    exact absurd (by
      have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (center S)
      rw [h.card, hk] at h1
      omega : Nat.card (S ⧸ center S) = 4)
      (card_quot_center_ne_four ρ h.cube h.fpf)
  · rw [show (2 : ℕ) ^ 6 = 64 by norm_num] at hk
    exfalso
    have htop : center S = ⊤ := Subgroup.eq_top_of_card_eq (H := center S) (by rw [hk, h.card])
    obtain ⟨a, b, hab⟩ := h.nonab
    have ha : a ∈ center S := by rw [htop]; exact Subgroup.mem_top a
    exact hab (Subgroup.mem_center_iff.mp ha b).symm

theorem FpfNonab.sq_center (h : FpfNonab S ρ) : ∀ z ∈ center S, z * z = 1 := by
  intro z hz
  by_contra hzz
  have hcard := h.card_center
  have horddvd : orderOf z ∣ 4 := by
    rw [← hcard, ← Nat.card_zpowers z]
    exact Subgroup.card_dvd_of_le (Subgroup.zpowers_le_of_mem hz)
  have horddvd' : orderOf z ∣ 2 ^ 2 := by
    rwa [show (2 : ℕ) ^ 2 = 4 by norm_num]
  obtain ⟨k, hk2, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp horddvd'
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    exact hzz (by
      have hz1 : z = 1 := orderOf_eq_one_iff.mp hk
      rw [hz1, one_mul])
  have hk1 : k ≠ 1 := by
    rintro rfl
    rw [pow_one] at hk
    have hz2 : z ^ 2 = 1 := by rw [← hk, pow_orderOf_eq_one]
    exact hzz (by rw [← pow_two]; exact hz2)
  have hk_eq : k = 2 := by omega
  have horder : orderOf z = 4 := by rw [hk, hk_eq]; norm_num
  have hZp : Subgroup.zpowers z = center S := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le_of_mem hz) ?_
    rw [Nat.card_zpowers, horder]
    exact le_of_eq hcard
  let W : Subgroup S := Subgroup.zpowers (z * z)
  have hzz_sq : (z * z) * (z * z) = 1 := by
    have hz4 : z ^ 4 = 1 := by rw [← horder, pow_orderOf_eq_one]
    rw [show z * z = z ^ (2 : ℕ) by rw [pow_two],
      ← pow_add, show (2 : ℕ) + 2 = 4 by norm_num, hz4]
  have hWcard : Nat.card W = 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    show Nat.card (Subgroup.zpowers (z * z)) = 2
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by rwa [pow_two]) hzz
  have hWinv : ∀ w ∈ W, ρ w ∈ W := by
    intro w hw
    have hgen : ρ (z * z) ∈ Subgroup.zpowers (z * z) := by
      have hzrho : ρ z ∈ Subgroup.zpowers z := by
        rw [hZp]; exact rho_mem_center ρ hz
      rw [Subgroup.mem_zpowers_iff] at hzrho
      obtain ⟨j, hj⟩ := hzrho
      rw [Subgroup.mem_zpowers_iff]
      refine ⟨j, ?_⟩
      rw [map_mul, ← hj]
      have hz2 : z * z = z ^ (2 : ℤ) := (zpow_two z).symm
      rw [hz2, ← zpow_mul z 2 j, ← zpow_add z j j]
      congr 1
      ring
    have hwm : w ∈ Subgroup.zpowers (z * z) := hw
    rw [Subgroup.mem_zpowers_iff] at hwm
    obtain ⟨n, rfl⟩ := hwm
    rw [Subgroup.mem_zpowers_iff] at hgen
    obtain ⟨m, hm⟩ := hgen
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨m * n, ?_⟩
    rw [map_zpow, ← hm, zpow_mul]
  have hbot : W = ⊥ :=
    eq_bot_of_card_le_two ρ h.cube h.fpf W hWinv (by rw [hWcard])
  have hmem : z * z ∈ W := by
    show z * z ∈ Subgroup.zpowers (z * z)
    exact Subgroup.mem_zpowers_iff.mpr ⟨1, by rw [zpow_one]⟩
  exact hzz (Subgroup.mem_bot.mp (hbot ▸ hmem))

private theorem card_quot_center_eq_sixteen (h : FpfNonab S ρ) :
    Nat.card (S ⧸ center S) = 16 := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (center S)
  rw [h.card, h.card_center] at h1
  omega

theorem FpfNonab.comm_mem (h : FpfNonab S ρ) (g k : S) : g * k * g⁻¹ * k⁻¹ ∈ center S := by
  have hquot : Nat.card (S ⧸ center S) = 16 := card_quot_center_eq_sixteen h
  have h3 : centerAut ρ ^ 3 = 1 := by
    rw [← centerAut_pow, h.cube, centerAut_one]
  have hfpf : ∀ v : S ⧸ center S, centerAut ρ v = v → v = 1 :=
    centerAut_fpf ρ h.cube h.fpf
  have hmul : (QuotientGroup.mk (g * k) : S ⧸ center S) =
      QuotientGroup.mk (k * g) := by
    have hcomm := abelian_of_card_sixteen hquot (centerAut ρ) h3 hfpf
      (QuotientGroup.mk g) (QuotientGroup.mk k)
    simpa only [← QuotientGroup.mk_mul] using hcomm
  have hmem := (QuotientGroup.eq_iff_div_mem).mp hmul
  simpa only [div_eq_mul_inv, mul_inv_rev, mul_assoc] using hmem

theorem FpfNonab.sq_mem (h : FpfNonab S ρ) (g : S) : g * g ∈ center S := by
  rw [Subgroup.mem_center_iff]
  intro k
  have hc : ⁅g, k⁆ ∈ center S := by
    simpa only [commutatorElement_def] using h.comm_mem g k
  have hcc : ⁅g, k⁆ * ⁅g, k⁆ = 1 := h.sq_center ⁅g, k⁆ hc
  have hcomm : Commute g ⁅g, k⁆ := Subgroup.mem_center_iff.mp hc g
  have h2 : ⁅g, k⁆ ^ 2 = ⁅g ^ 2, k⁆ := hcomm.commutatorElement_pow_left 2
  have hcomm2 : ⁅g ^ 2, k⁆ = 1 := by rw [← h2, pow_two, hcc]
  have hcomm : g ^ 2 * k = k * g ^ 2 := commutatorElement_eq_one_iff_mul_comm.mp hcomm2
  simpa only [pow_two] using hcomm.symm

theorem FpfNonab.commutator_eq (h : FpfNonab S ρ) : commutator S = center S := by
  have hle : commutator S ≤ center S := by
    change ⁅(⊤ : Subgroup S), ⊤⁆ ≤ center S
    rw [Subgroup.commutator_le]
    intro a _ b _
    simpa only [commutatorElement_def] using h.comm_mem a b
  have hmod : Nat.card (commutator S) % 3 = 1 :=
    card_mod_three_of_fpf ρ h.cube h.fpf (commutator S)
      (fun x hx => rho_mem_commutator ρ hx)
  have hdvd : Nat.card (commutator S) ∣ 4 := by
    rw [← h.card_center]
    exact Subgroup.card_dvd_of_le hle
  have hdvd' : Nat.card (commutator S) ∣ 2 ^ 2 := by
    rwa [show (2 : ℕ) ^ 2 = 4 by norm_num]
  obtain ⟨k, hk2, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd'
  have hmodk : 2 ^ k % 3 = 1 := by rw [← hk]; exact hmod
  have hne1 : Nat.card (commutator S) ≠ 1 := by
    intro h1
    have hbot : commutator S = ⊥ := Subgroup.eq_bot_of_card_eq (H := commutator S) h1
    obtain ⟨a, b, hab⟩ := h.nonab
    have hmem : ⁅a, b⁆ ∈ commutator S :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    have h1' : ⁅a, b⁆ = 1 := by
      rw [hbot] at hmem
      exact Subgroup.mem_bot.mp hmem
    exact hab (commutatorElement_eq_one_iff_mul_comm.mp h1')
  have hkcase : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  have hcardcomm : Nat.card (commutator S) = 4 := by
    rcases hkcase with rfl | rfl | rfl
    · rw [pow_zero] at hk
      exact absurd hk hne1
    · exfalso
      rw [pow_one] at hk
      rw [hk] at hmod
      norm_num at hmod
    · rw [show (2 : ℕ) ^ 2 = 4 by norm_num] at hk
      exact hk
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [h.card_center, hcardcomm])

theorem FpfNonab.card_quot (h : FpfNonab S ρ) : Nat.card (S ⧸ center S) = 16 :=
  card_quot_center_eq_sixteen h

theorem FpfNonab.special (h : FpfNonab S ρ) : FpfSpecial S :=
  ⟨h.card_center, h.sq_center, h.comm_mem, h.sq_mem, h.card_quot, h.commutator_eq⟩

end CFSG.OddStandard.SmallF3.HarrisU33.Outside
