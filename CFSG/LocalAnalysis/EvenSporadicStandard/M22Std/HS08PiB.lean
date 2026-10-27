module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.HS08Pi
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.HS08Syl2

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup

namespace PiData

variable {Hh : Type*} [Group Hh] [Finite Hh] {Y : Type*} [Group Y] {π : Hh →* MulAut Y} {t : Hh}
  (h : PiData π t)
include h

omit [Finite Hh] in
theorem card_ker : Nat.card π.ker = 2 := by
  have hset : (π.ker : Set Hh) = {1, t} := by
    ext x
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_insert_iff, Set.mem_singleton_iff]
    exact h.ker x
  have : Nat.card π.ker = (π.ker : Set Hh).ncard := (Nat.card_coe_set_eq _).symm
  rw [this, hset, Set.ncard_pair (Ne.symm h.t_ne)]

omit [Finite Hh] in
theorem card_Hh : Nat.card Hh = Nat.card (MulAut Y) * 2 := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup π.ker, h.card_ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective π h.surj).toEquiv]

theorem card_comap (B : Subgroup (MulAut Y)) : Nat.card (B.comap π) = 2 * Nat.card B := by
  have h1 := (B.comap π).card_mul_index
  have h2 := B.card_mul_index
  rw [B.index_comap_of_surjective h.surj, h.card_Hh] at h1
  have hpos : 0 < B.index := by
    have : Finite (MulAut Y) := Finite.of_surjective π h.surj
    exact Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  rw [← h2] at h1
  have : Nat.card (B.comap π) * B.index = (2 * Nat.card B) * B.index := by rw [h1]; ring
  exact Nat.eq_of_mul_eq_mul_right hpos this

end PiData

namespace PiData

variable {Hh : Type*} [Group Hh] [Finite Hh] {Y : Type*} [Group Y] {π : Hh →* MulAut Y} {t : Hh}
  {S J : Subgroup (MulAut Y)} (h : PiData π t) (A : AutHyp Y S J)
include h A

theorem card_comap_S : Nat.card (S.comap π) = 512 := by
  rw [h.card_comap, A.card_S]

theorem isPGroup_comap_S : IsPGroup 2 (S.comap π) :=
  IsPGroup.of_card (n := 9) (by rw [h.card_comap_S A]; norm_num)

theorem index_comap_S_odd : ¬ 2 ∣ (S.comap π).index := by
  have h1 := (S.comap π).card_mul_index
  rw [h.card_comap_S A, h.card_Hh, A.card_A] at h1
  omega

omit [Finite Hh] in
theorem central_lift {ζ : MulAut Y} (hζsq : ζ * ζ = 1)
    (hζc : ∀ β ∈ S, β * ζ = ζ * β) {z : Hh} (hz : π z = ζ) :
    ∀ x, π x ∈ S → z * x = x * z := by
  have hzz : z * z = 1 := h.mul_self_of_pi_sq A z (by rw [hz]; exact hζsq)
  have hle : closure {x : MulAut Y | x ∈ S ∧ x * x = 1} ≤
      (centralizer ({z} : Set Hh)).map π := by
    rw [Subgroup.closure_le]
    rintro β ⟨hβS, hβsq⟩
    obtain ⟨w, rfl⟩ := h.surj β
    refine ⟨w, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    have hw1 : w * w = 1 := h.mul_self_of_pi_sq A w hβsq
    have hcomm : π w * ζ = ζ * π w := hζc _ hβS
    have hwz : π (w * z) * π (w * z) = 1 := by
      rw [map_mul, hz]
      calc π w * ζ * (π w * ζ) = π w * (ζ * π w) * ζ := by group
        _ = π w * (π w * ζ) * ζ := by rw [hcomm]
        _ = (π w * π w) * (ζ * ζ) := by group
        _ = 1 := by rw [hβsq, hζsq, one_mul]
    have h2 := h.mul_self_of_pi_sq A (w * z) hwz
    have h3 : w * z = (w * z)⁻¹ := (inv_eq_of_mul_eq_one_right h2).symm
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hzz, inv_eq_of_mul_eq_one_right hw1] at h3
    exact h3
  intro x hx
  have hx' : π x ∈ (centralizer ({z} : Set Hh)).map π := by
    apply hle
    rw [A.data.gen_involutions]
    exact hx
  obtain ⟨c, hc, hcx⟩ := hx'
  have hcz : c * z = z * c := Subgroup.mem_centralizer_singleton_iff.1 hc
  rcases h.eq_or_eq_mul_t hcx.symm with h1 | h1
  · rw [h1]; exact hcz.symm
  · rw [h1]
    calc z * (c * t) = (z * c) * t := by group
      _ = (c * z) * t := by rw [hcz]
      _ = c * (z * t) := by group
      _ = c * (t * z) := by rw [h.t_central z]
      _ = c * t * z := by group

omit h A in
theorem isPGroup_zpowers_of_sq {G : Type*} [Group G] {w z : G} (hwz : w * w = z)
    (hz : z * z = 1) : IsPGroup 2 (zpowers w) := by
  have h4 : w ^ 4 = 1 := by
    calc w ^ 4 = w ^ 2 * w ^ 2 := by rw [← pow_add]
      _ = (w * w) * (w * w) := by rw [pow_two]
      _ = 1 := by rw [hwz, hz]
  have hdvd : orderOf w ∣ 2 ^ 2 := orderOf_dvd_of_pow_eq_one (by simpa using h4)
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])

theorem exists_sqData : ∃ z : Hh, SqData t (S.comap π) z (z * t) ∧ π z ∈ J ∧
    π z ∈ innerImage Y ⊤ ∧ π z ≠ 1 ∧ z * z = 1 := by
  obtain ⟨ζ, hζS, hζ1, hζsq, hζinn, hζc⟩ := A.center_S
  have hζcen : ∀ β ∈ S, β * ζ = ζ * β := (hζc ζ hζS).2 (Or.inr rfl)
  have hζJ : ζ ∈ J := A.data.centralizer_le ζ fun x hx => (hζcen x (A.J_le hx)).symm
  obtain ⟨z, hz⟩ := h.surj ζ
  have hzz : z * z = 1 := h.mul_self_of_pi_sq A z (by rw [hz]; exact hζsq)
  have hzc := h.central_lift A hζsq hζcen hz
  have hztc : ∀ x, π x ∈ S → (z * t) * x = x * (z * t) := by
    intro x hx
    calc z * t * x = z * (t * x) := by group
      _ = z * (x * t) := by rw [h.t_central x]
      _ = (z * x) * t := by group
      _ = (x * z) * t := by rw [hzc x hx]
      _ = x * (z * t) := by group
  have hπzt : π (z * t) = ζ := by rw [map_mul, h.pi_t, mul_one, hz]
  have hTodd := h.index_comap_S_odd A
  have hTp := h.isPGroup_comap_S A
  refine ⟨z, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hz ▸ hζJ, hz ▸ hζinn, hz ▸ hζ1, hzz⟩
  · show π t ∈ S
    rw [h.pi_t]; exact S.one_mem
  · show π z ∈ S
    rw [hz]; exact hζS
  · show π (z * t) ∈ S
    rw [hπzt]; exact hζS
  · intro heq
    exact h.t_ne (mul_left_cancel (a := z) (by rw [mul_one]; exact heq.symm))
  · calc z * (z * t) = (z * z) * t := by group
      _ = t := by rw [hzz, one_mul]
  · intro h1
    apply hζ1
    rw [← hz, h1, map_one]
  · intro h1
    apply hζ1
    rw [← hπzt, h1, map_one]
  · intro x hx
    exact hzc x hx
  · intro x hx
    exact hztc x hx
  ·
    obtain ⟨w, hw⟩ := h.sq_of_lift z (by rw [hz]; exact hζinn) (by rw [hz]; exact hζsq)
      (by rw [hz]; exact hζ1)
    exact exists_sq_mem_sylow hTp hTodd (u := z) (fun x hx => hzc x hx)
      (isPGroup_zpowers_of_sq hw hzz) hw
  · obtain ⟨w, hw⟩ := h.sq_of_lift (z * t) (by rw [hπzt]; exact hζinn) (by rw [hπzt]; exact hζsq)
      (by rw [hπzt]; exact hζ1)
    have hztt : (z * t) * (z * t) = 1 := by
      calc z * t * (z * t) = (z * z) * (t * t) := by
            calc z * t * (z * t) = z * (t * z) * t := by group
              _ = z * (z * t) * t := by rw [h.t_central z]
              _ = (z * z) * (t * t) := by group
        _ = 1 := by rw [hzz, h.t_sq, one_mul]
    exact exists_sq_mem_sylow hTp hTodd (u := z * t) (fun x hx => hztc x hx)
      (isPGroup_zpowers_of_sq hw hztt) hw
  · intro u huT hu hu1 ⟨w, hwT, hww⟩
    have hπu : π u ∈ ({1, ζ} : Set (MulAut Y)) := by
      have hcen : π u * π u = π u * π u := rfl
      have hcomm : ∀ β ∈ S, β * π u = π u * β := by
        intro β hβ
        obtain ⟨x, rfl⟩ := h.surj β
        rw [← map_mul, ← map_mul, hu x hβ |>.symm]
      have := (hζc (π u) huT).1 (fun β hβ => hcomm β hβ)
      rcases this with h1 | h1
      · exact Or.inl h1
      · exact Or.inr h1
    rcases hπu with h1 | h1
    · rcases (h.ker u).1 h1 with h2 | h2
      · exact absurd h2 hu1
      · exfalso
        subst h2
        have := h.mul_self_of_pi_sq A w (by
          rw [← map_mul, hww, h.pi_t])
        rw [hww] at this
        exact h.t_ne this
    · have h2 : π u = π z := by rw [h1, hz]
      rcases h.eq_or_eq_mul_t h2 with h3 | h3
      · exact Or.inl h3
      · exact Or.inr h3

end PiData

end CFSG.EvenSporadicStandard.M22Std
