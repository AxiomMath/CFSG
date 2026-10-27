module

public import CFSG.GH74.GLS.IVK.Lifted.Dict

public section

namespace CFSG.GH74.GLS.Bg.Pu5

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK.Lifted
open CFSG.GH74.GLS.Stage1.Thm2.Recip (innOf)

section Basic

variable {Q : Type} [Group Q]

theorem ii4_mem_center_of_conj_eq_one {c : Q} (h : MulAut.conj c = 1) : c ∈ Subgroup.center Q := by
  rw [Subgroup.mem_center_iff]
  intro x
  have h1 := congrArg (fun ρ : MulAut Q => ρ x) h
  simp only [MulAut.conj_apply, MulAut.one_apply] at h1
  calc x * c = (c * x * c⁻¹) * c := by rw [h1]
    _ = c * x := by group

theorem ii4_conj_eq_one_iff_mem_center {c : Q} : MulAut.conj c = 1 ↔ c ∈ Subgroup.center Q :=
  ⟨ii4_mem_center_of_conj_eq_one, conj_eq_one_of_mem_center⟩

theorem ii4_exists_central_ne_one (hO : HatOK Q) : ∃ z ∈ Subgroup.center Q, z ≠ 1 := by
  have hcard : Nat.card (Subgroup.center Q) = 2 := hO.sl2.2
  obtain ⟨w, hw1, -⟩ := (Nat.card_eq_two_iff' (1 : Subgroup.center Q)).1 hcard
  exact ⟨w, w.2, fun h => hw1 (Subtype.ext h)⟩

theorem ii4_center_eq_of_ne_one (hO : HatOK Q) {x y : Q} (hx : x ∈ Subgroup.center Q)
    (hy : y ∈ Subgroup.center Q) (hx1 : x ≠ 1) (hy1 : y ≠ 1) : x = y := by
  have hcard : Nat.card (Subgroup.center Q) = 2 := hO.sl2.2
  obtain ⟨w, -, hw⟩ := (Nat.card_eq_two_iff' (1 : Subgroup.center Q)).1 hcard
  have h1 : (⟨x, hx⟩ : Subgroup.center Q) = w := hw _ (fun h => hx1 (congrArg Subtype.val h))
  have h2 : (⟨y, hy⟩ : Subgroup.center Q) = w := hw _ (fun h => hy1 (congrArg Subtype.val h))
  exact congrArg Subtype.val (h1.trans h2.symm)

theorem ii4_mul_self_eq_one_of_mem_center (hO : HatOK Q) {x : Q} (hx : x ∈ Subgroup.center Q) :
    x * x = 1 := by
  have hcard : Nat.card (Subgroup.center Q) = 2 := hO.sl2.2
  have h := pow_card_eq_one' (x := (⟨x, hx⟩ : Subgroup.center Q))
  rw [hcard] at h
  have h' := congrArg Subtype.val h
  simpa [sq] using h'

variable [Finite Q]

theorem ii4_eq_of_commute_involutions (hO : HatOK Q) {u v : Q} (hu : orderOf u = 2)
    (hv : orderOf v = 2) (huv : u * v = v * u) : u = v := by
  have h' : CFSG.pRank 2 ↥(⊤ : Subgroup Q) = 1 := by
    rw [CFSG.GH74.GLS.Stage1.Thm2.Recip.pRank_eq_of_mulEquiv'
      (Subgroup.topEquiv : ↥(⊤ : Subgroup Q) ≃* Q)]
    exact hO.rank
  exact CFSG.GH74.GLS.Stage1.Thm2.Recip.eq_of_pRank_one h' (Subgroup.mem_top u)
    (Subgroup.mem_top v) hu hv huv

theorem ii4_involution_mem_center (hO : HatOK Q) {t : Q} (ht : t * t = 1) :
    t ∈ Subgroup.center Q := by
  by_cases h1 : t = 1
  · rw [h1]; exact Subgroup.one_mem _
  obtain ⟨z, hz, hz1⟩ := ii4_exists_central_ne_one hO
  have hzz := ii4_mul_self_eq_one_of_mem_center hO hz
  have ht2 : orderOf t = 2 := orderOf_eq_prime (by rwa [sq]) h1
  have hz2 : orderOf z = 2 := orderOf_eq_prime (by rwa [sq]) hz1
  have : t = z := ii4_eq_of_commute_involutions hO ht2 hz2 (Subgroup.mem_center_iff.1 hz t)
  rw [this]; exact hz

theorem ii4_orderFour_facts (hO : HatOK Q) {c : Q} (hc : orderOf c = 4) :
    c ∉ Subgroup.center Q ∧ c * c ∈ Subgroup.center Q ∧ c * c ≠ 1 := by
  have hc4 : c ^ 4 = 1 := by rw [← hc]; exact pow_orderOf_eq_one c
  have hc2 : c * c ≠ 1 := by
    intro h
    have : c ^ 2 = 1 := by rw [sq]; exact h
    have := orderOf_dvd_of_pow_eq_one this
    rw [hc] at this
    omega
  refine ⟨fun hcz => hc2 (ii4_mul_self_eq_one_of_mem_center hO hcz), ?_, hc2⟩
  apply ii4_involution_mem_center hO
  have : c * c * (c * c) = c ^ 4 := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  rw [this, hc4]

theorem ii4_orderFour_of_conj (hO : HatOK Q) {c : Q} (hc2 : MulAut.conj c * MulAut.conj c = 1)
    (hc1 : MulAut.conj c ≠ 1) : orderOf c = 4 := by
  have hcz : c ∉ Subgroup.center Q := fun h => hc1 (ii4_conj_eq_one_iff_mem_center.2 h)
  have hcc : c * c ∈ Subgroup.center Q := by
    rw [← ii4_conj_eq_one_iff_mem_center, map_mul]
    exact hc2
  have hcc1 : c * c ≠ 1 := fun h => hcz (ii4_involution_mem_center hO h)
  have h4' : c ^ 4 = 1 := by
    have := ii4_mul_self_eq_one_of_mem_center hO hcc
    have e : c ^ 4 = c * c * (c * c) := by
      simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    rw [e, this]
  have h4 : c ^ 2 ^ (1 + 1) = 1 := by
    rw [show (2 : ℕ) ^ (1 + 1) = 4 by norm_num]
    exact h4'
  have h2 : ¬ c ^ 2 ^ 1 = 1 := by
    intro h
    apply hcc1
    rw [← sq]
    simpa using h
  have := orderOf_eq_prime_pow h2 h4
  simpa using this

end Basic

theorem ii4_inner_involution (h2A7 : II4_2A7) {Q : Type} [Group Q] [Finite Q] (hO : HatOK Q)
    (φ ψ : MulAut Q) (hφ2 : φ * φ = 1) (hψ2 : ψ * ψ = 1) (_hcomm : φ * ψ = ψ * φ)
    (_hφ1 : φ ≠ 1) (_hψ1 : ψ ≠ 1) (_hne : φ ≠ ψ)
    (hφf : ¬ IsFAutomorphism Q φ) (hψf : ¬ IsFAutomorphism Q ψ)
    (_hφψf : ¬ IsFAutomorphism Q (φ * ψ)) :
    φ ∈ innOf Q ∨ ψ ∈ innOf Q ∨ φ * ψ ∈ innOf Q := by
  by_contra h
  simp only [not_or] at h
  obtain ⟨hφ, hψ, hφψ⟩ := h
  have hd := dict_diag h2A7 hO φ ψ hφ2 hψ2 hφ hψ hφf hψf
  rw [inv_eq_of_mul_eq_one_right hψ2] at hd
  exact hφψ hd

theorem ii4_43e (h2A7 : II4_2A7) {Q : Type} [Group Q] [Finite Q] (hO : HatOK Q)
    (φ : MulAut Q) (hφ2 : φ * φ = 1) (W : Subgroup Q) (hW2 : IsPGroup 2 ↥W)
    (hWnc : ¬ ∀ a ∈ W, ∀ b ∈ W, a * b = b * a) (hWφ : ∀ w ∈ W, φ w = w) :
    φ = 1 ∨ IsFAutomorphism Q φ :=
  dict_involution h2A7 hO φ hφ2 W hW2 hWnc hWφ

section FourThreeF

variable {Q : Type} [Group Q] [Finite Q]

theorem ii4_43f_of_43a (hO : HatOK Q)
    (h43a : ∀ φ : MulAut Q, φ * φ = 1 → φ ∉ innOf Q → ¬ IsFAutomorphism Q φ →
      ∀ c : Q, orderOf c = 4 → φ c ≠ c)
    (φ ψ : MulAut Q) (hφ2 : φ * φ = 1) (hψ2 : ψ * ψ = 1) (hcomm : φ * ψ = ψ * φ)
    (hφ1 : φ ≠ 1) (hψ1 : ψ ≠ 1) (hne : φ ≠ ψ)
    (hφf : ¬ IsFAutomorphism Q φ) (_hψf : ¬ IsFAutomorphism Q ψ) (hψin : ψ ∈ innOf Q) :
    ∃ u : Q, orderOf u = 4 ∧ ψ u = u ∧ φ u = u⁻¹ := by
  obtain ⟨c, rfl⟩ := hψin
  have hc4 : orderOf c = 4 := ii4_orderFour_of_conj hO hψ2 hψ1
  obtain ⟨-, hcc, hcc1⟩ := ii4_orderFour_facts hO hc4
  have hζ : c⁻¹ * φ c ∈ Subgroup.center Q := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨x, rfl⟩ := φ.surjective y
    have h1 := congrArg (fun ρ : MulAut Q => ρ x) hcomm
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv] at h1
    calc φ x * (c⁻¹ * φ c) = c⁻¹ * (c * φ x * c⁻¹) * φ c := by group
      _ = c⁻¹ * (φ c * φ x * (φ c)⁻¹) * φ c := by rw [h1]
      _ = c⁻¹ * φ c * φ x := by group
  by_cases hζ1 : c⁻¹ * φ c = 1
  · exfalso
    have hφc : φ c = c := by
      have : φ c = c * (c⁻¹ * φ c) := by group
      rw [this, hζ1, mul_one]
    by_cases hφin : φ ∈ innOf Q
    · obtain ⟨d, rfl⟩ := hφin
      have hd4 : orderOf d = 4 := ii4_orderFour_of_conj hO hφ2 hφ1
      obtain ⟨-, hdd, hdd1⟩ := ii4_orderFour_facts hO hd4
      have hdc : d * c = c * d := by
        have := hφc
        simp only [MulAut.conj_apply] at this
        calc d * c = (d * c * d⁻¹) * d := by group
          _ = c * d := by rw [this]
      have hsq : d * c⁻¹ * (d * c⁻¹) = 1 := by
        have hcd : c⁻¹ * d = d * c⁻¹ := by
          calc c⁻¹ * d = c⁻¹ * (d * c) * c⁻¹ := by group
            _ = c⁻¹ * (c * d) * c⁻¹ := by rw [hdc]
            _ = d * c⁻¹ := by group
        have h1 : d * c⁻¹ * (d * c⁻¹) = (d * d) * (c⁻¹ * c⁻¹) := by
          calc d * c⁻¹ * (d * c⁻¹) = d * (c⁻¹ * d) * c⁻¹ := by group
            _ = d * (d * c⁻¹) * c⁻¹ := by rw [hcd]
            _ = (d * d) * (c⁻¹ * c⁻¹) := by group
        have h2 : d * d = c * c := ii4_center_eq_of_ne_one hO hdd hcc hdd1 hcc1
        rw [h1, h2]
        group
      have hdcz : d * c⁻¹ ∈ Subgroup.center Q := ii4_involution_mem_center hO hsq
      apply hne
      have : MulAut.conj d = MulAut.conj (d * c⁻¹) * MulAut.conj c := by
        rw [← map_mul]; congr 1; group
      rw [this, ii4_conj_eq_one_iff_mem_center.2 hdcz, one_mul]
    · exact h43a φ hφ2 hφin hφf c hc4 hφc
  · refine ⟨c, hc4, by simp [MulAut.conj_apply], ?_⟩
    have hζc : c⁻¹ * φ c = c * c := ii4_center_eq_of_ne_one hO hζ hcc hζ1 hcc1
    have hc3 : c * c * (c * c) = 1 := ii4_mul_self_eq_one_of_mem_center hO hcc
    have hinv : c * (c * c) = c⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      simpa [mul_assoc] using hc3
    calc φ c = c * (c⁻¹ * φ c) := by group
      _ = c * (c * c) := by rw [hζc]
      _ = c⁻¹ := hinv

end FourThreeF

end CFSG.GH74.GLS.Bg.Pu5
