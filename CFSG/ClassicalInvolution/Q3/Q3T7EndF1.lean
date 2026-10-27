module

public import CFSG.ClassicalInvolution.Q3.Q3T8Bend

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.ClassicalInvolution
open scoped MatrixGroups

section Member

variable {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G}

private theorem sl2Three_sq_eq_one : ∀ y : SL(2, ZMod 3), y * y = 1 → y = 1 ∨ y = -1 := by
  decide +kernel

private theorem odd_orderOf_oddCore {Y : Type} [Group Y] [Finite Y]
    (a : classicalInvolutionOddCore Y) : Odd (orderOf a) :=
  Odd.of_dvd_nat (CFSG.ComponentClassification.OddCore.odd_card Y) (orderOf_dvd_natCard a)

private theorem IsClassicalMember3.not_mem_oddCore {u : G} (hu : u ∈ K) (hu2 : u * u = 1)
    (hu1 : u ≠ 1) : (⟨u, hu⟩ : ↥K) ∉ classicalInvolutionOddCore ↥K := by
  intro h
  have hodd := odd_orderOf_oddCore (Y := ↥K) ⟨⟨u, hu⟩, h⟩
  have h2 : orderOf (⟨u, hu⟩ : ↥K) = 2 := by
    apply orderOf_eq_prime
    · apply Subtype.ext
      show u ^ 2 = 1
      rw [pow_two]
      exact hu2
    · intro h1
      exact hu1 (congrArg Subtype.val h1)
  have : orderOf (⟨⟨u, hu⟩, h⟩ : classicalInvolutionOddCore ↥K) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact h2
  rw [this] at hodd
  exact absurd hodd (by decide)

theorem IsClassicalMember3.eq_of_sq_eq_one (hK : Q3.IsClassicalMember3 K z) {u v : G} (hu : u ∈ K)
    (hv : v ∈ K) (hu2 : u * u = 1) (hv2 : v * v = 1) (hu1 : u ≠ 1) (hv1 : v ≠ 1)
    (huv : u * v = v * u) : u = v := by
  obtain ⟨e⟩ := hK.nonempty_equiv
  set N := classicalInvolutionOddCore ↥K with hN
  set mk : ↥K →* ↥K ⧸ N := QuotientGroup.mk' N with hmk
  have key : ∀ w : G, ∀ hw : w ∈ K, w * w = 1 → w ≠ 1 → e (mk ⟨w, hw⟩) = -1 := by
    intro w hw hw2 hw1
    have hsq : e (mk ⟨w, hw⟩) * e (mk ⟨w, hw⟩) = 1 := by
      rw [← map_mul, ← map_mul]
      have : (⟨w, hw⟩ : ↥K) * ⟨w, hw⟩ = 1 := Subtype.ext (by simpa using hw2)
      rw [this, map_one, map_one]
    rcases sl2Three_sq_eq_one _ hsq with h | h
    · exfalso
      have h1 : mk ⟨w, hw⟩ = 1 := by
        apply e.injective
        rw [h, map_one]
      exact IsClassicalMember3.not_mem_oddCore hw hw2 hw1 ((QuotientGroup.eq_one_iff _).mp h1)
    · exact h
  have hmkeq : mk ⟨u, hu⟩ = mk ⟨v, hv⟩ := by
    apply e.injective
    rw [key u hu hu2 hu1, key v hv hv2 hv1]
  have hmem : (⟨u, hu⟩ : ↥K)⁻¹ * ⟨v, hv⟩ ∈ N := QuotientGroup.eq.mp hmkeq
  have hord : orderOf (⟨⟨u, hu⟩⁻¹ * ⟨v, hv⟩, hmem⟩ : N) ∣ 2 := by
    rw [Subgroup.orderOf_mk]
    apply orderOf_dvd_of_pow_eq_one
    apply Subtype.ext
    have h1 : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
    show (u⁻¹ * v) ^ 2 = 1
    rw [h1, pow_two]
    calc u * v * (u * v) = u * (v * u) * v := by group
      _ = u * (u * v) * v := by rw [huv]
      _ = (u * u) * (v * v) := by group
      _ = 1 := by rw [hu2, hv2, one_mul]
  have hodd := odd_orderOf_oddCore (Y := ↥K) ⟨⟨u, hu⟩⁻¹ * ⟨v, hv⟩, hmem⟩
  have h1 : orderOf (⟨⟨u, hu⟩⁻¹ * ⟨v, hv⟩, hmem⟩ : N) = 1 := by
    have hcop : Nat.Coprime (orderOf (⟨⟨u, hu⟩⁻¹ * ⟨v, hv⟩, hmem⟩ : N)) 2 :=
      Nat.Coprime.symm ((Nat.coprime_two_left).mpr hodd)
    exact Nat.Coprime.eq_one_of_dvd hcop hord
  rw [orderOf_eq_one_iff] at h1
  have h2 : (⟨u, hu⟩ : ↥K)⁻¹ * ⟨v, hv⟩ = 1 := congrArg Subtype.val h1
  have h3 : (⟨u, hu⟩ : ↥K) = ⟨v, hv⟩ := inv_mul_eq_one.mp h2
  exact congrArg Subtype.val h3

theorem IsClassicalMember3.exists_orderOf_three (hK : Q3.IsClassicalMember3 K z) :
    ∃ x ∈ K, orderOf x = 3 := by
  obtain ⟨e₀⟩ := hK.nonempty_equiv
  have hcardK : Nat.card K = 24 * Nat.card (classicalInvolutionOddCore ↥K) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (classicalInvolutionOddCore ↥K),
      Nat.card_congr e₀.toEquiv, natCard_sl2Three]
  have h3 : 3 ∣ Nat.card K := by rw [hcardK]; exact Dvd.dvd.mul_right (by norm_num) _
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x₁, hx₁⟩ := exists_prime_orderOf_dvd_card' 3 h3
  exact ⟨(x₁ : G), x₁.2, by rw [Subgroup.orderOf_coe]; exact hx₁⟩

theorem IsClassicalMember3.card_inf_le_eight (hK : Q3.IsClassicalMember3 K z) {P : Subgroup G}
    (hP : IsPGroup 2 P) : Nat.card ↥(K ⊓ P) ≤ 8 := by
  obtain ⟨e₀⟩ := hK.nonempty_equiv
  have hcardK : Nat.card K = 24 * Nat.card (classicalInvolutionOddCore ↥K) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (classicalInvolutionOddCore ↥K),
      Nat.card_congr e₀.toEquiv, natCard_sl2Three]
  have hOodd : Odd (Nat.card (classicalInvolutionOddCore ↥K)) :=
    CFSG.ComponentClassification.OddCore.odd_card ↥K
  have hT0p : IsPGroup 2 ↥(K ⊓ P) := hP.to_le inf_le_right
  obtain ⟨k, hk⟩ := hT0p.exists_card_eq
  have hT0K : Nat.card ↥(K ⊓ P) ∣ Nat.card K := Subgroup.card_dvd_of_le inf_le_left
  by_contra hgt
  push Not at hgt
  have hk4 : 4 ≤ k := by
    by_contra hk3
    push Not at hk3
    have : 2 ^ k ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have h16 : 16 ∣ Nat.card K := by
    refine dvd_trans ?_ (hk ▸ hT0K)
    calc 16 = 2 ^ 4 := by norm_num
      _ ∣ 2 ^ k := pow_dvd_pow 2 hk4
  rw [hcardK] at h16
  obtain ⟨r, hr⟩ := hOodd
  rw [hr] at h16
  omega

end Member

section Nilpotent

variable {G : Type} [Group G]

theorem comm_of_sq_eq_one {G : Type} [Group G] {Z : Subgroup G} (hZsq : ∀ c ∈ Z, c * c = 1) :
    ∀ c₁ ∈ Z, ∀ c₂ ∈ Z, c₁ * c₂ = c₂ * c₁ := by
  intro c₁ h₁ c₂ h₂
  have h12 := hZsq _ (Z.mul_mem h₁ h₂)
  have e1 : c₁⁻¹ = c₁ := inv_eq_of_mul_eq_one_right (hZsq _ h₁)
  have e2 : c₂⁻¹ = c₂ := inv_eq_of_mul_eq_one_right (hZsq _ h₂)
  have : c₁ * c₂ = (c₁ * c₂)⁻¹ := (inv_eq_of_mul_eq_one_right h12).symm
  rw [this, mul_inv_rev, e1, e2]

theorem centralizes_of_ψ_nilpotent {Z : Subgroup G} {x : G} (hx3 : x ^ 3 = 1)
    (hZsq : ∀ c ∈ Z, c * c = 1) (hZnorm : ∀ c ∈ Z, x * c * x⁻¹ ∈ Z) (N : ℕ)
    (hN : ∀ c ∈ Z, (fun y : G => x * y * x⁻¹ * y⁻¹)^[N] c = 1) : ∀ c ∈ Z, x * c * x⁻¹ = c := by
  have hψZ : ∀ c ∈ Z, x * c * x⁻¹ * c⁻¹ ∈ Z := fun c hc => Z.mul_mem (hZnorm c hc) (Z.inv_mem hc)
  have hcomm : ∀ c₁ ∈ Z, ∀ c₂ ∈ Z, c₁ * c₂ = c₂ * c₁ := comm_of_sq_eq_one hZsq
  have hx3' : x * x * x = 1 := by
    calc x * x * x = x ^ 3 := (pow_three' x).symm
      _ = 1 := hx3
  have step : ∀ c ∈ Z, x * (x * c * x⁻¹ * c⁻¹) * x⁻¹ * (x * c * x⁻¹ * c⁻¹)⁻¹ = 1 →
      x * c * x⁻¹ * c⁻¹ = 1 := by
    intro c hc hψψ
    set b := x * c * x⁻¹ with hbdef
    set d := x * b * x⁻¹ with hddef
    have hb : b ∈ Z := hZnorm c hc
    have hd : d ∈ Z := hZnorm b hb
    have hb2 : b * b = 1 := hZsq b hb
    have hb1 : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
    have hc1 : c⁻¹ = c := inv_eq_of_mul_eq_one_right (hZsq c hc)
    have hbc : b * c = c * b := hcomm b hb c hc
    have e : x * (b * c⁻¹) * x⁻¹ = d * b⁻¹ := by
      rw [hddef, hbdef]
      group
    rw [e, hb1, hc1, mul_inv_rev, hb1] at hψψ
    have hdc : d * c = 1 := by
      calc d * c = d * c * (b * b) := by rw [hb2, mul_one]
        _ = d * (c * b) * b := by group
        _ = d * (b * c) * b := by rw [hbc]
        _ = (d * b) * (c * b) := by group
        _ = 1 := by simpa [hb1, hc1] using hψψ
    have hdeq : d = c := by
      have : d = c⁻¹ := eq_inv_of_mul_eq_one_left hdc
      rw [this, hc1]
    have hbd : x * d * x⁻¹ = c := by
      calc x * d * x⁻¹ = (x * x * x) * c * (x * x * x)⁻¹ := by rw [hddef, hbdef]; group
        _ = c := by rw [hx3', one_mul, inv_one, mul_one]
    have hbc' : b = c := by
      rw [hdeq] at hbd
      exact hbd
    rw [hbc', mul_inv_cancel]
  have hS : ∀ M : ℕ, ∀ c ∈ Z, (fun y : G => x * y * x⁻¹ * y⁻¹)^[M] c = 1 →
      x * c * x⁻¹ * c⁻¹ = 1 := by
    intro M
    induction M with
    | zero =>
      intro c hc h0
      simp only [Function.iterate_zero, id_eq] at h0
      rw [h0]
      group
    | succ M ih =>
      intro c hc h0
      rw [Function.iterate_succ_apply] at h0
      have h1 := ih _ (hψZ c hc) h0
      exact step c hc h1
  intro c hc
  have h := hS N c hc (hN c hc)
  exact mul_inv_eq_one.mp h

end Nilpotent

section Subnormal

variable {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G}

theorem IsClassicalMember3.centralizes_of_subnormal (hK : Q3.IsClassicalMember3 K z)
    {Q Z : Subgroup G} {x : G}
    (hQ : ∀ g ∈ Subgroup.centralizer ({z} : Set G), ∀ w ∈ Q, g * w * g⁻¹ ∈ Q)
    (hQX : Q ≤ Subgroup.centralizer ({z} : Set G)) (hZQ : Z ≤ Q) (hzZ : z ∈ Z)
    (hZsq : ∀ c ∈ Z, c * c = 1) (hZnorm : ∀ c ∈ Z, x * c * x⁻¹ ∈ Z) (hx : x ∈ K)
    (hx3 : x ^ 3 = 1) : ∀ c ∈ Z, x * c * x⁻¹ = c := by
  obtain ⟨m, hm⟩ := Q3T8.exists_iterate_comm_mem hK.subnormal hQ hx
  have hKX : K ≤ Subgroup.centralizer ({z} : Set G) := isSubnormal_le hK.subnormal
  have hxz : x * z * x⁻¹ = z := by
    have := Subgroup.mem_centralizer_singleton_iff.mp (hKX hx)
    rw [this]
    group
  have hψZ : ∀ c ∈ Z, x * c * x⁻¹ * c⁻¹ ∈ Z := fun c hc => Z.mul_mem (hZnorm c hc) (Z.inv_mem hc)
  have hiter : ∀ (k : ℕ), ∀ c ∈ Z, (fun y : G => x * y * x⁻¹ * y⁻¹)^[k] c ∈ Z := by
    intro k
    induction k with
    | zero => intro c hc; exact hc
    | succ k ih =>
      intro c hc
      rw [Function.iterate_succ_apply]
      exact ih _ (hψZ c hc)
  have hcomm := comm_of_sq_eq_one hZsq
  refine centralizes_of_ψ_nilpotent hx3 hZsq hZnorm (m + 1) (fun c hc => ?_)
  rw [Function.iterate_succ_apply']
  set u := (fun y : G => x * y * x⁻¹ * y⁻¹)^[m] c with hu
  have huZ : u ∈ Z := hiter m c hc
  have huK : u ∈ K := hm c (hZQ hc) (hQX (hZQ hc))
  by_cases hu1 : u = 1
  · rw [hu1]
    group
  · have huz : u = z :=
      hK.eq_of_sq_eq_one huK hK.mem (hZsq u huZ) (hZsq z hzZ) hu1 hK.ne_one (hcomm u huZ z hzZ)
    rw [huz, hxz]
    group

end Subnormal

end CFSG.ClassicalInvolution.Q3
