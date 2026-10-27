module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAL2Dih
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAL2Aut
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAL2Tr
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAL2Num
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL2Bridge

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GorensteinWalter
open CFSG.GH74.GLS.Stage2.Signalizer.Odd87

section Facts
variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] [Finite K]

theorem kaL2_two_ne_zero (h : Odd (Nat.card F)) : (2 : F) ≠ 0 := by
  intro h2
  have : Fintype F := Fintype.ofFinite F
  have hc : ((2 : ℕ) : F) = 0 := by exact_mod_cast h2
  have hdvd : ringChar F ∣ 2 := (ringChar.spec F 2).mp hc
  have hp : ringChar F = 2 := by
    have hpr : (ringChar F).Prime := CharP.prime_ringChar F
    exact (Nat.prime_dvd_prime_iff_eq hpr Nat.prime_two).mp hdvd
  have h0 : Fintype.card F % 2 = 0 := FiniteField.even_card_iff_char_two.mp hp
  rw [← Nat.card_eq_fintype_card] at h0
  have h1 := Nat.odd_iff.mp h
  omega

omit [Finite K] in
theorem kaL2_fixSub_eq (α : MulAut K) : fixSub α = fixedSubgroup K α := rfl

theorem kaL2_inndiag_dihedral (hF : L2Field F) (e : K ≃* L2 F) (α : MulAut K) (hα : α * α = 1)
    (hα1 : α ≠ 1) (hαD : α ∈ innDiagSub e) :
    ∃ d : ℕ, IsDihedralOrder ↥(fixedSubgroup K α) d ∧
      (d + 1 = Nat.card F ∨ d = Nat.card F + 1) := by
  classical
  have hα2 : orderOf α = 2 := orderOf_eq_prime (by rw [sq]; exact hα) hα1
  obtain ⟨d₁, d₂, ε, hε, hmod, hd₁, hd₂, hd₁'', hd₂''⟩ :=
    exists_eps_d (Nat.card F) hF.1 hF.2
  by_cases hin : α ∈ innAut K
  · obtain ⟨u, hu⟩ := hin
    have hu2 : u * u = 1 := by
      have h1 : MulAut.conj (u * u) = (1 : MulAut K) := by rw [map_mul, hu]; exact hα
      exact (conj_injective_of_L2 e) (h1.trans (map_one _).symm)
    have hu1 : u ≠ 1 := by
      rintro rfl
      exact hα1 (by rw [← hu]; simp)
    have hordu : orderOf u = 2 := orderOf_eq_prime (by rw [sq]; exact hu2) hu1
    have hdih := (ivk_1_3a F hF K e ε hε hmod d₁ hd₁ u hordu).2.1
    refine ⟨d₁, ?_, hd₁''⟩
    rw [← hu, fixedSubgroup_conj_eq_centralizer]
    exact hdih
  · have hdih := (ivk_1_3b F hF K e ε hε hmod d₂ hd₂ α hαD hin hα2).2.1
    exact ⟨d₂, hdih, hd₂''⟩

end Facts

section Main
variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] [Finite K]

omit [Finite K] in
theorem kaL2_comm_conj (e : MulAut K) (c : K) :
    MulAut.conj c * e * (MulAut.conj c)⁻¹ * e⁻¹ = MulAut.conj (c * (e c)⁻¹) := by
  have h := conj_apply_aut e c
  calc MulAut.conj c * e * (MulAut.conj c)⁻¹ * e⁻¹
      = MulAut.conj c * (e * (MulAut.conj c)⁻¹ * e⁻¹) := by group
    _ = MulAut.conj c * (e * MulAut.conj c * e⁻¹)⁻¹ := by group
    _ = MulAut.conj c * (MulAut.conj (e c))⁻¹ := by rw [h]
    _ = MulAut.conj (c * (e c)⁻¹) := by rw [map_mul, map_inv]

theorem kaL2_dihedral_mem_innDiag (hF : L2Field F) (e : K ≃* L2 F) (α : MulAut K)
    (hdih : ∃ d : ℕ, IsDihedralOrder ↥(fixedSubgroup K α) d ∧
      (d + 1 = Nat.card F ∨ d = Nat.card F + 1))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {P : Subgroup (MulAut K)} (hPp : IsPGroup p ↥P)
    (hcomm : ∀ e' ∈ P, e' * α = α * e')
    (hnorm : ∀ c ∈ fixSub α, Odd (orderOf c) → MulAut.conj c ∈ normalizer (P : Set (MulAut K))) :
    ∀ e' ∈ P, e' ∈ innDiagSub e := by
  intro e' he'
  obtain ⟨g, σ, hdec, hσord⟩ := kaL2_aut_decomp e e'
  by_cases hσ : σ = 1
  · rw [hdec, hσ, map_one, mul_one]
    exact ⟨g, rfl⟩
  exfalso
  have hodd' : Odd (orderOf e') := ka_odd_of_mem_pGroup hp hp2 hPp he'
  have hσodd : Odd (orderOf σ) := Odd.of_dvd_nat hodd' hσord
  have hℓ1 : orderOf σ ≠ 1 := fun h => hσ (orderOf_eq_one_iff.mp h)
  have hℓ3 : 3 ≤ orderOf σ := by
    have h1 := Nat.odd_iff.mp hσodd
    have h2 := orderOf_pos σ
    omega
  have hpσ : p ∣ orderOf σ := by
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.mp hPp) ⟨e', he'⟩
    have hm' : orderOf e' = p ^ m := by rw [← hm]; exact (Subgroup.orderOf_mk e' he').symm
    have hd : orderOf σ ∣ p ^ m := hm' ▸ hσord
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp hd
    have hj0 : j ≠ 0 := by
      rintro rfl
      exact hℓ1 (by simpa using hj)
    rw [hj]
    exact dvd_pow_self p hj0
  obtain ⟨d, hdD, hdq⟩ := hdih
  have hq : Nat.card (fixedField σ) ^ orderOf σ = Nat.card F := fixedField_card_pow σ
  have hq₁odd : Odd (Nat.card (fixedField σ)) := odd_card_fixedField σ hF.1
  have hq₁3 : 3 ≤ Nat.card (fixedField σ) := by
    have h1 := Nat.odd_iff.mp hq₁odd
    have h2 := one_lt_card_fixedField σ
    omega
  rw [← hq] at hdq
  obtain ⟨r, hr, hrd, hr2, hrp, hrN⟩ := kaL2_ppd hq₁3 hq₁odd hℓ3 hp hpσ hdq
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨k, hdk, hk2, ⟨φ⟩⟩ := hdD
  have : NeZero k := ⟨by omega⟩
  have hcard : Nat.card ↥(fixedSubgroup K α) = d := by
    rw [Nat.card_congr φ.toEquiv, Nat.card_eq_fintype_card, DihedralGroup.card, hdk]
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' r (hcard ▸ hrd)
  set c₀ : K := (c : K) with hc₀
  have hc₀ord : orderOf c₀ = r := by rw [hc₀, Subgroup.orderOf_coe]; exact hc
  have hc₀fix : c₀ ∈ fixSub α := c.2
  have hrodd : Odd r := hr.odd_of_ne_two hr2
  have hN := hnorm c₀ hc₀fix (by rw [hc₀ord]; exact hrodd)
  have hinj : Function.Injective (MulAut.conj : K →* MulAut K) := conj_injective_of_L2 e
  set x₀ : K := c₀ * (e' c₀)⁻¹ with hx₀
  have hx₀P : x₀ ∈ kaInner P := by
    rw [mem_kaInner, hx₀, ← kaL2_comm_conj]
    exact P.mul_mem ((Subgroup.mem_normalizer_iff.mp hN e').mp he') (P.inv_mem he')
  have hx₀ord : ∃ m : ℕ, orderOf x₀ = p ^ m := by
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.mp (kaInner_isPGroup hinj hPp)) ⟨x₀, hx₀P⟩
    exact ⟨m, by rw [← hm]; exact (Subgroup.orderOf_mk x₀ hx₀P).symm⟩
  have hwfix : e' c₀ ∈ fixedSubgroup K α := by
    show α (e' c₀) = e' c₀
    have h1 : (α * e') c₀ = (e' * α) c₀ := by rw [hcomm e' he']
    have h2 : α c₀ = c₀ := hc₀fix
    calc α (e' c₀) = (α * e') c₀ := rfl
      _ = (e' * α) c₀ := h1
      _ = e' (α c₀) := rfl
      _ = e' c₀ := by rw [h2]
  have hword : orderOf (e' c₀) = r := by
    rw [← hc₀ord]
    exact orderOf_injective (e' : K →* K) e'.injective c₀
  have hcomm₀ : c₀ * e' c₀ = e' c₀ * c₀ :=
    odd_commute_of_dihedral (fixedSubgroup K α) φ c.2 hwfix (by rw [hc₀ord]; exact hrodd)
      (by rw [hword]; exact hrodd)
  have hxr : x₀ ^ r = 1 := by
    have hc : Commute c₀ (e' c₀)⁻¹ := Commute.inv_right hcomm₀
    have h1 : c₀ ^ r = 1 := by rw [← hc₀ord]; exact pow_orderOf_eq_one c₀
    have h2 : (e' c₀) ^ r = 1 := by rw [← hword]; exact pow_orderOf_eq_one (e' c₀)
    rw [hx₀, hc.mul_pow, inv_pow, h1, h2, inv_one, one_mul]
  have hx1 : x₀ = 1 := by
    obtain ⟨m, hm⟩ := hx₀ord
    have hdvd1 : orderOf x₀ ∣ r := orderOf_dvd_of_pow_eq_one hxr
    have hdvd2 : orderOf x₀ ∣ p ^ m := by rw [hm]
    have hcop : Nat.Coprime r (p ^ m) :=
      Nat.Coprime.pow_right m ((Nat.coprime_primes hr hp).mpr hrp)
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hdvd1 hdvd2)
  have hfix : e' c₀ = c₀ := by
    have : c₀ * (e' c₀)⁻¹ = 1 := hx1
    exact (mul_inv_eq_one.mp this).symm
  have hchar : (2 : F) ≠ 0 := kaL2_two_ne_zero hF.1
  have hy1 : toPSL e c₀ ≠ 1 := by
    intro h
    have h3 : c₀ = 1 := (toPSL e).injective (by rw [h, map_one])
    rw [h3, orderOf_one] at hc₀ord
    exact hr.one_lt.ne hc₀ord
  have hrel : g * pgl2FieldAut F σ
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (toPSL e c₀)) * g⁻¹ =
      Matrix.ProjectiveSpecialLinearGroup.toPGL (toPSL e c₀) := by
    have h1 := kaL2_toPGL_apply e g σ c₀
    rw [← hdec, hfix] at h1
    exact h1.symm
  have hdvd := kaL2_order_dvd hchar σ hσodd g (toPSL e c₀) hy1 hrel
  rw [MulEquiv.orderOf_eq, hc₀ord] at hdvd
  exact hrN hdvd

theorem kaL2_dihedral_thm (hF : L2Field F) (e : K ≃* L2 F) (α : MulAut K) (hα : α * α = 1)
    (hα1 : α ≠ 1) (hαD : α ∈ innDiagSub e) : KAAll α := by
  intro p hp hp2 P hP
  obtain ⟨hPp, hP1, hcomm, hnorm⟩ := hP
  have hdih := kaL2_inndiag_dihedral hF e α hα hα1 hαD
  have hinn : ∀ e' ∈ P, e' ∈ innAut K := fun e' he' =>
    kaL2_odd_mem_innAut hF e
      (kaL2_dihedral_mem_innDiag hF e α hdih hp hp2 hPp hcomm hnorm e' he')
      (ka_odd_of_mem_pGroup hp hp2 hPp he')
  refine ⟨fun x => commutator_mem_innAut hF e x α, ?_⟩
  obtain ⟨d, hdD, -⟩ := hdih
  obtain ⟨k, hdk, hk2, ⟨φ⟩⟩ := hdD
  have : NeZero k := ⟨by omega⟩
  have hinj : Function.Injective (MulAut.conj : K →* MulAut K) := conj_injective_of_L2 e
  have hX0p := kaInner_isPGroup hinj hPp
  have hX0C : kaInner P ≤ fixSub α := kaInner_le_fixSub hinj hcomm
  have hX0cyc : IsCyclic ↥(kaInner P) :=
    isCyclic_of_odd_le_dihedral (fixedSubgroup K α) φ hX0C
      (fun x hx => ka_odd_of_mem_pGroup hp hp2 hX0p hx)
  let ψ : ↥(kaInner P) →* ↥P :=
    ((MulAut.conj : K →* MulAut K).comp (kaInner P).subtype).codRestrict P (fun y => y.2)
  have hsurj : Function.Surjective ψ := by
    rintro ⟨e', he'⟩
    obtain ⟨y, hy⟩ := hinn e' he'
    exact ⟨⟨y, by rw [mem_kaInner, hy]; exact he'⟩, Subtype.ext hy⟩
  exact isCyclic_of_surjective ψ hsurj

end Main

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
