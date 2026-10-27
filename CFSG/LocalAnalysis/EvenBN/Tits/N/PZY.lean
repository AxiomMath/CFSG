module

public import CFSG.LocalAnalysis.EvenBN.Tits.S56N2
public import CFSG.LocalAnalysis.EvenBN.Tits.S56SevenAll

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.PZ

open Subgroup CFSG.Sporadic.Schreier.Tits CFSG.LocalAnalysis.EvenBN.Tits
  CFSG.LocalAnalysis.EvenBN.Tits.Data

section Abstract

theorem exists_fixed_coset {H : Type*} [Group H] {y u : H} {B : Subgroup H} [Finite B]
    (hy3 : y ^ 3 = 1) (hcard : ¬ 3 ∣ Nat.card B) (hyB : ∀ b ∈ B, y * b * y⁻¹ ∈ B)
    (hyu : u⁻¹ * (y * u * y⁻¹) ∈ B) : ∃ b ∈ B, y * (u * b) * y⁻¹ = u * b := by
  let f : B → B := fun b => ⟨u⁻¹ * (y * (u * b) * y⁻¹), by
    rw [show u⁻¹ * (y * (u * (b : H)) * y⁻¹) = u⁻¹ * (y * u * y⁻¹) * (y * b * y⁻¹) by group]
    exact B.mul_mem hyu (hyB b b.2)⟩
  have hA : ∀ b : B, u * (f b : H) = y * (u * b) * y⁻¹ := fun b => by
    show u * (u⁻¹ * (y * (u * (b : H)) * y⁻¹)) = y * (u * b) * y⁻¹
    group
  have h3 : y * y * y = 1 := (pow_three' y).symm.trans hy3
  have hf : ∀ b, f (f (f b)) = b := fun b => Subtype.ext <| mul_left_cancel (a := u) <| by
    rw [hA (f (f b)), hA (f b), hA b]
    calc y * (y * (y * (u * (b : H)) * y⁻¹) * y⁻¹) * y⁻¹
        = (y * y * y) * (u * b) * (y * y * y)⁻¹ := by group
      _ = u * b := by rw [h3]; group
  let σ : Equiv.Perm B := ⟨f, fun b => f (f b), hf, hf⟩
  have hσ : σ ^ 3 ^ 1 = 1 := Equiv.Perm.ext fun b => by
    rw [pow_one, Equiv.Perm.coe_pow]
    exact hf b
  haveI := Fintype.ofFinite B
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [Nat.card_eq_fintype_card] at hcard
  obtain ⟨a, ha⟩ := Equiv.Perm.exists_fixed_point_of_prime hcard hσ
  refine ⟨a, a.2, ?_⟩
  rw [← hA a]
  exact congrArg (fun x : B => u * (x : H)) ha

end Abstract

section Tits

variable {G : Type} [Group G] [Finite G] {d : Data G}


theorem inv_mul_conj_mem_B (h49 : d.Thm49Statement) (hd : d.Hyp) {u y : G}
    (huF : ∀ f ∈ d.F, u * f = f * u) (hy : y ∈ d.N ⊓ centralizer ({d.t} : Set G))
    (hyε : y * d.s56Eps u = d.s56Eps u * y) : u⁻¹ * (y * u * y⁻¹) ∈ d.B := by
  obtain ⟨hyN, hyC⟩ := mem_inf.1 hy
  have hyt : Commute y d.t := mem_centralizer_singleton_iff.1 hyC
  have hyε' : Commute y (d.s56Eps u) := hyε
  have hconj : (y * u * y⁻¹) * d.t * (y * u * y⁻¹)⁻¹ = u * d.t * u⁻¹ := by
    have e1 : y⁻¹ * d.t * y = d.t := by rw [mul_assoc, ← hyt.eq]; group
    have e2 : y * (d.t * d.s56Eps u) * y⁻¹ = d.t * d.s56Eps u :=
      mul_inv_eq_iff_eq_mul.2 (hyt.mul_right hyε').eq
    calc (y * u * y⁻¹) * d.t * (y * u * y⁻¹)⁻¹ = y * (u * (y⁻¹ * d.t * y) * u⁻¹) * y⁻¹ := by
          group
      _ = y * (d.t * d.s56Eps u) * y⁻¹ := by rw [e1, hd.s56_conj_t u]
      _ = u * d.t * u⁻¹ := by rw [e2, hd.s56_conj_t u]
  have hct : d.t * (u⁻¹ * (y * u * y⁻¹)) = (u⁻¹ * (y * u * y⁻¹)) * d.t := by
    calc d.t * (u⁻¹ * (y * u * y⁻¹)) = u⁻¹ * (u * d.t * u⁻¹) * (y * u * y⁻¹) := by group
      _ = u⁻¹ * ((y * u * y⁻¹) * d.t * (y * u * y⁻¹)⁻¹) * (y * u * y⁻¹) := by rw [hconj]
      _ = (u⁻¹ * (y * u * y⁻¹)) * d.t := by group
  have hcF : ∀ f ∈ d.F, f * (u⁻¹ * (y * u * y⁻¹)) = (u⁻¹ * (y * u * y⁻¹)) * f := by
    intro f hf
    have h1 : Commute f u := (huF f hf).symm
    have h2 : Commute (y⁻¹ * f * y⁻¹⁻¹) u := (huF _ (hd.s56_N_conj_F h49 (inv_mem hyN) hf)).symm
    have h3 := h2.conj y
    rw [show y * (y⁻¹ * f * y⁻¹⁻¹) * y⁻¹ = f by group] at h3
    exact (h1.inv_right.mul_right h3).eq
  have hle : d.F ⊔ zpowers d.t ≤ centralizer ({u⁻¹ * (y * u * y⁻¹)} : Set G) :=
    sup_le (fun f hf => mem_centralizer_singleton_iff.2 (hcF f hf))
      (zpowers_le.2 (mem_centralizer_singleton_iff.2 hct))
  rw [← hd.centralizer_B, mem_centralizer_iff]
  exact fun b hb => mem_centralizer_singleton_iff.1 (hle hb)

theorem mul_mul_self_cases (hd : d.Hyp) {u b : G} (huF : ∀ f ∈ d.F, u * f = f * u)
    (hεF : d.s56Eps u ∈ d.F) (hb : b ∈ d.B) :
    (u * b) * (u * b) = u * u ∨ (u * b) * (u * b) = d.s56Eps u * (u * u) := by
  have ht2 := hd.t_mul_self
  have hFt : ∀ f ∈ d.F, f * d.t = d.t * f := fun f hf => hd.L_comm_t (s56_F_le_L d hf)
  have hsq : ∀ f ∈ d.F, f * f = 1 := fun f hf => by
    rw [← sq]
    exact hd.B_facts.2.2.1.2 f (s56_F_le_B d hf)
  rcases (Data.mem_sup_zpowers_iff ht2 hFt).1 hb with hbF | hbF
  · left
    calc (u * b) * (u * b) = u * (b * u) * b := by group
      _ = u * (u * b) * b := by rw [← huF b hbF]
      _ = u * u * (b * b) := by group
      _ = u * u := by rw [hsq b hbF, mul_one]
  · right
    obtain ⟨f, hf, rfl⟩ : ∃ f ∈ d.F, b = d.t * f :=
      ⟨d.t * b, hbF, by rw [← mul_assoc, ht2, one_mul]⟩
    have htut : d.t * u * d.t = d.s56Eps u * u := by
      calc d.t * u * d.t = d.t * (u * d.t * u⁻¹) * u := by group
        _ = (d.t * d.t) * d.s56Eps u * u := by rw [hd.s56_conj_t u]; group
        _ = d.s56Eps u * u := by rw [ht2, one_mul]
    calc (u * (d.t * f)) * (u * (d.t * f)) = u * d.t * (f * u) * d.t * f := by group
      _ = u * d.t * (u * f) * d.t * f := by rw [huF f hf]
      _ = u * d.t * u * (f * d.t) * f := by group
      _ = u * d.t * u * (d.t * f) * f := by rw [hFt f hf]
      _ = u * (d.t * u * d.t) * (f * f) := by group
      _ = (u * d.s56Eps u) * u := by rw [htut, hsq f hf, mul_one]; group
      _ = (d.s56Eps u * u) * u := by rw [huF _ hεF]
      _ = d.s56Eps u * (u * u) := by group

theorem comm_sq_of_pow_three (h49 : d.Thm49Statement) (hd : d.Hyp) {u y : G}
    (huF : ∀ f ∈ d.F, u * f = f * u) (hεF : d.s56Eps u ∈ d.F)
    (hy : y ∈ d.N ⊓ centralizer ({d.t} : Set G)) (hy3 : y ^ 3 = 1)
    (hyε : y * d.s56Eps u = d.s56Eps u * y) : y * (u * u) * y⁻¹ = u * u := by
  obtain ⟨b, hb, hfix⟩ := exists_fixed_coset hy3 (by rw [hd.B_facts.2.2.2.1]; decide)
    (fun b hb => (mem_normalizer_iff.1 (mem_inf.1 hy).1 b).1 hb)
    (inv_mul_conj_mem_B h49 hd huF hy hyε)
  have hsq : y * ((u * b) * (u * b)) * y⁻¹ = (u * b) * (u * b) := by
    calc y * ((u * b) * (u * b)) * y⁻¹ = (y * (u * b) * y⁻¹) * (y * (u * b) * y⁻¹) := by group
      _ = (u * b) * (u * b) := by rw [hfix]
  rcases mul_mul_self_cases hd huF hεF hb with h | h
  · rwa [h] at hsq
  · rw [h] at hsq
    calc y * (u * u) * y⁻¹ = (y * d.s56Eps u * y⁻¹)⁻¹ * (y * (d.s56Eps u * (u * u)) * y⁻¹) := by
          group
      _ = u * u := by rw [mul_inv_eq_iff_eq_mul.2 hyε, hsq]; group

theorem y_comm_sq (h49 : d.Thm49Statement) (hd : d.Hyp) {u : G}
    (huF : ∀ f ∈ d.F, u * f = f * u) (hε : d.s56Eps u = d.pv 10) :
    d.s56Y * (u * u) * d.s56Y⁻¹ = u * u := by
  obtain ⟨hy, -, hy3, -, hy10, -, -⟩ := hd.s56_Y_facts
  refine comm_sq_of_pow_three h49 hd huF ?_ hy hy3 ?_
  · rw [hε]
    exact s56_pv10_mem_F d
  · rw [hε]
    exact hy10

end Tits

end CFSG.LocalAnalysis.EvenBN.Tits.N.PZ
