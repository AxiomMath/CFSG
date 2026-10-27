module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.SuzONAut
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.CanLoc
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.AutBoundConj

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup Cover

section Generic

variable {H : Type} [Group H] {L K : Subgroup H}

theorem mem_of_q_mem {R : Subgroup H} (hodd : Odd (Nat.card ↥(center ↥L))) {k : ℕ}
    (hR : ∀ r : ↥L, (r : H) ∈ R → r ^ 2 ^ k = 1) {x : ↥L} (hx : x ^ 2 ^ k = 1)
    (hq : q ↥L x ∈ (R.subgroupOf L).map (q ↥L)) : (x : H) ∈ R := by
  obtain ⟨r', hr', hrq⟩ := hq
  have hr'R : (r' : H) ∈ R := Subgroup.mem_subgroupOf.1 hr'
  have hz : r'⁻¹ * x ∈ center ↥L := by
    rw [← q_eq_one_iff, map_mul, map_inv, hrq, inv_mul_cancel]
  have hcomm : Commute r' (r'⁻¹ * x) := (Subgroup.mem_center_iff.1 hz r').symm.symm
  have hxz : x = r' * (r'⁻¹ * x) := by group
  have hpow : x ^ 2 ^ k = r' ^ 2 ^ k * (r'⁻¹ * x) ^ 2 ^ k := by
    conv_lhs => rw [hxz]
    exact hcomm.mul_pow _
  have hz1 : (r'⁻¹ * x) ^ 2 ^ k = 1 := by
    rw [hR r' hr'R, one_mul] at hpow
    rw [← hpow, hx]
  have hord : orderOf (r'⁻¹ * x) = 1 := by
    have h1 : orderOf (r'⁻¹ * x) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hz1
    have h2 : orderOf (r'⁻¹ * x) ∣ Nat.card ↥(center ↥L) := by
      have := orderOf_dvd_natCard (⟨r'⁻¹ * x, hz⟩ : ↥(center ↥L))
      rwa [Subgroup.orderOf_mk] at this
    have hcop : Nat.Coprime (2 ^ k) (Nat.card ↥(center ↥L)) :=
      Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hodd)
    exact Nat.eq_one_of_dvd_one (hcop.gcd_eq_one ▸ Nat.dvd_gcd h1 h2)
  have hz2 : r'⁻¹ * x = 1 := orderOf_eq_one_iff.1 hord
  have : x = r' := by
    rw [hxz, hz2, mul_one]
  rw [this]
  exact hr'R

theorem card_q_image_of_card_two_pow (hodd : Odd (Nat.card ↥(center ↥L))) {R : Subgroup H}
    (hRL : R ≤ L) {a : ℕ} (hRc : Nat.card ↥R = 2 ^ a) :
    Nat.card ↥((R.subgroupOf L).map (q ↥L)) = 2 ^ a := by
  have hR' : Nat.card ↥(R.subgroupOf L) = 2 ^ a := by
    rw [← hRc]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRL).toEquiv
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 ↥(R.subgroupOf L) := IsPGroup.of_card hR'
  have hinj : Function.Injective ((q ↥L).subgroupMap (R.subgroupOf L)) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : q ↥L (x : ↥L) = 1 := congrArg Subtype.val hx
    have hz : (x : ↥L) ∈ center ↥L := q_eq_one_iff.1 h1
    obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.1 hp) x
    have h2 : orderOf x ∣ Nat.card ↥(center ↥L) := by
      have := orderOf_dvd_natCard (⟨(x : ↥L), hz⟩ : ↥(center ↥L))
      rwa [Subgroup.orderOf_mk, Subgroup.orderOf_coe] at this
    have hj0 : j = 0 := by
      by_contra hne
      have : 2 ∣ Nat.card ↥(center ↥L) := by
        rw [hj] at h2
        exact (dvd_pow_self 2 hne).trans h2
      exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 this)
    rw [hj0, pow_zero, orderOf_eq_one_iff] at hj
    exact hj
  rw [← hR']
  exact (Nat.card_congr (Equiv.ofBijective _ ⟨hinj, (q ↥L).subgroupMap_surjective _⟩)).symm

theorem card_eq_two_pow_mul_odd (hodd : Odd (Nat.card ↥(center ↥L))) (hKL : K ≤ L) {a m : ℕ}
    (hm : Odd m) (hc : Nat.card ↥((K.subgroupOf L).map (q ↥L)) = 2 ^ a * m) :
    (Nat.card ↥K).factorization 2 = a := by
  obtain ⟨π, hπ, -, hker⟩ := exists_oddCentralCover hodd hKL
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup π.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective π hπ).toEquiv, hc] at h1
  rw [h1, show 2 ^ a * m * Nat.card ↥π.ker = 2 ^ a * (m * Nat.card ↥π.ker) by ring]
  exact AutBound.factorization_two_of_odd (hm.mul hker)

theorem canLoc_conj_elts [Finite H] {N₀ : Subgroup H} (hodd : Odd (Nat.card ↥(center ↥L)))
    (hKL : K ≤ L) (hcan : CanLoc K N₀) {G : Type} [Group G] [Finite G]
    (Ψ : (↥L ⧸ center ↥L) →* G) (hΨ : Function.Injective Ψ) {a m : ℕ} (hm : Odd m)
    (hc : Nat.card ↥((K.subgroupOf L).map (q ↥L)) = 2 ^ a * m) (RR : Subgroup G)
    (hRR : RR ≤ ((K.subgroupOf L).map (q ↥L)).map Ψ) (hRRc : Nat.card ↥RR = 2 ^ a)
    (X : Set G) (hXK : ∀ x ∈ X, x ∈ ((K.subgroupOf L).map (q ↥L)).map Ψ)
    (hXN : ∀ x ∈ X, ∀ y ∈ RR, x * y * x⁻¹ ∈ RR) :
    ∃ d ∈ ((K.subgroupOf L).map (q ↥L)).map Ψ, ∀ x ∈ X,
      ∃ n ∈ (N₀.subgroupOf L).map (q ↥L), Ψ n = d * x * d⁻¹ := by
  set Kh : Subgroup G := ((K.subgroupOf L).map (q ↥L)).map Ψ with hKh
  have hlift : ∀ y ∈ Kh, ∃ k : ↥L, (k : H) ∈ K ∧ Ψ (q ↥L k) = y := by
    rintro y ⟨_, ⟨k, hk, rfl⟩, rfl⟩
    exact ⟨k, Subgroup.mem_subgroupOf.1 hk, rfl⟩
  rcases hcan with ⟨-, hN⟩ | ⟨-, R, -, hRK, hRc, hN⟩
  · refine ⟨1, Kh.one_mem, fun x hx => ?_⟩
    obtain ⟨k, hkK, hk⟩ := hlift x (hXK x hx)
    refine ⟨q ↥L k, ⟨k, ?_, rfl⟩, ?_⟩
    · rw [hN]
      exact Subgroup.mem_subgroupOf.2 hkK
    · rw [hk]
      group
  · rw [card_eq_two_pow_mul_odd hodd hKL hm hc] at hRc
    have hRL : R ≤ L := hRK.trans hKL
    set Rt : Subgroup (↥L ⧸ center ↥L) := (R.subgroupOf L).map (q ↥L) with hRt
    set Rh : Subgroup G := Rt.map Ψ with hRh
    have hRhc : Nat.card ↥Rh = 2 ^ a := by
      rw [hRh, Subgroup.card_map_of_injective hΨ]
      exact card_q_image_of_card_two_pow hodd hRL hRc
    have hRhK : Rh ≤ Kh :=
      Subgroup.map_mono (Subgroup.map_mono (fun x hx => Subgroup.mem_subgroupOf.2
        (hRK (Subgroup.mem_subgroupOf.1 hx))))
    have hKhc : Nat.card ↥Kh = 2 ^ a * m := by
      rw [hKh, Subgroup.card_map_of_injective hΨ]
      exact hc
    obtain ⟨p, hp, hconj⟩ := AutBound.exists_conj_of_card_eq Kh RR Rh hRR hRhK hm hKhc hRRc hRhc
    have hR : ∀ r : ↥L, (r : H) ∈ R → r ^ 2 ^ a = 1 := by
      intro r hr
      have h1 := pow_card_eq_one' (G := ↥R) (x := ⟨(r : H), hr⟩)
      rw [hRc] at h1
      have h2 := congrArg Subtype.val h1
      exact Subtype.ext (by simpa using h2)
    refine ⟨p, hp, fun x hx => ?_⟩
    have hy : p * x * p⁻¹ ∈ Kh := Kh.mul_mem (Kh.mul_mem hp (hXK x hx)) (Kh.inv_mem hp)
    obtain ⟨k, hkK, hk⟩ := hlift _ hy
    refine ⟨q ↥L k, ⟨k, ?_, rfl⟩, hk⟩
    rw [hN]
    refine Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨?_, hkK⟩)
    refine AutBound.mem_normalizer_of_map_le R (k : H) ?_
    rintro _ ⟨r, hr, rfl⟩
    have hrL : r ∈ L := hRL hr
    let ρ : ↥L := ⟨r, hrL⟩
    have hρ : ρ ∈ R.subgroupOf L := Subgroup.mem_subgroupOf.2 hr
    have e1 : Ψ (q ↥L (k * ρ * k⁻¹)) = (p * x * p⁻¹) * Ψ (q ↥L ρ) * (p * x * p⁻¹)⁻¹ := by
      simp only [map_mul, map_inv, hk]
    have hρRh : Ψ (q ↥L ρ) ∈ Rh := ⟨q ↥L ρ, ⟨ρ, hρ, rfl⟩, rfl⟩
    have h1 := (hconj _).1 hρRh
    have h2 := hXN x hx _ h1
    have h3 : p⁻¹ * Ψ (q ↥L (k * ρ * k⁻¹)) * p = x * (p⁻¹ * Ψ (q ↥L ρ) * p) * x⁻¹ := by
      rw [e1]
      group
    have hmem : Ψ (q ↥L (k * ρ * k⁻¹)) ∈ Rh := (hconj _).2 (h3 ▸ h2)
    obtain ⟨ρ'', hρ'', he⟩ := hmem
    have hq : q ↥L (k * ρ * k⁻¹) ∈ Rt := by
      rw [← hΨ he]
      exact hρ''
    have hx2 : (k * ρ * k⁻¹) ^ 2 ^ a = 1 := by
      rw [conj_pow, hR ρ hr, mul_one, mul_inv_cancel]
    have := mem_of_q_mem hodd hR hx2 hq
    have e2 : (MulAut.conj (k : H)).toMonoidHom r = ((k * ρ * k⁻¹ : ↥L) : H) := by
      simp [MulAut.conj_apply, ρ]
    rw [e2]
    exact this

end Generic

end CFSG.EvenSporadicStandard.Induction
