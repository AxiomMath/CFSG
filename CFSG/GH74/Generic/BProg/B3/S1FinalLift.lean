module

public import CFSG.GH74.Generic.BProg.B3.S1FinalDefs

public section

namespace CFSG.GH74.Generic.BProg.B3

namespace S1FinalLift

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.TwoThin CFSG.GH74.GLS.C3.Layer1 CFSG.GH74.Generic
  CFSG.GH74.Generic.BProg CFSG.Blueprint Subgroup
open CFSG.GH74.Generic.BProg.B3.S1FinalDefs
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {a : G} {J : Subgroup G}

theorem eq_one_of_Pi0_eq_one (hJa : J ≤ centralizer ({a} : Set G))
    (hodd : Odd (Nat.card (center ↥(PumpCalc.bar a J)))) {n : ↥J} (hn : Pi0 hJa n = 1)
    (hn2 : n * n = 1) : n = 1 := by
  have hz : barJ hJa n ∈ center ↥(PumpCalc.bar a J) := (QuotientGroup.eq_one_iff _).1 hn
  have hz2 : barJ hJa n * barJ hJa n = 1 := by rw [← map_mul, hn2, map_one]
  have h1 : barJ hJa n = 1 := by
    set z : ↥(center ↥(PumpCalc.bar a J)) := ⟨barJ hJa n, hz⟩ with hzdef
    have hord : orderOf z ∣ Nat.card ↥(center ↥(PumpCalc.bar a J)) := orderOf_dvd_natCard _
    have hord2 : orderOf z ∣ 2 := by
      apply orderOf_dvd_of_pow_eq_one
      apply Subtype.ext
      simpa [pow_two] using hz2
    have hgcd : orderOf z ∣ Nat.gcd (Nat.card ↥(center ↥(PumpCalc.bar a J))) 2 :=
      Nat.dvd_gcd hord hord2
    rw [Nat.Coprime.gcd_eq_one hodd.coprime_two_right] at hgcd
    have : orderOf z = 1 := Nat.dvd_one.1 hgcd
    have hz1 : z = 1 := orderOf_eq_one_iff.1 this
    exact congrArg Subtype.val hz1
  have h2 : (Subgroup.inclusion hJa n : ↥(centralizer ({a} : Set G))) ∈
      pPrimeCore 2 ↥(centralizer ({a} : Set G)) := by
    apply (QuotientGroup.eq_one_iff _).1
    exact congrArg Subtype.val h1
  have h3 : Subgroup.inclusion hJa n * Subgroup.inclusion hJa n = 1 := by
    rw [← map_mul, hn2, map_one]
  have h4 := Th2.Bal.eq_one_of_sq_of_mem_pPrimeCore h3 h2
  exact Subgroup.inclusion_injective hJa (by rw [h4, map_one])

theorem odd_card_ker_Pi0 (hJa : J ≤ centralizer ({a} : Set G))
    (hodd : Odd (Nat.card (center ↥(PumpCalc.bar a J)))) : Odd (Nat.card (Pi0 hJa).ker) := by
  by_contra hne
  have h2 : 2 ∣ Nat.card (Pi0 hJa).ker := by
    rw [Nat.not_odd_iff_even] at hne
    exact even_iff_two_dvd.1 hne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := (Pi0 hJa).ker) 2 h2
  have hz2 : (z : ↥J) * z = 1 := by
    have := pow_orderOf_eq_one (z : ↥J)
    rwa [Subgroup.orderOf_coe, hz, pow_two] at this
  have hz1 : (z : ↥J) = 1 := eq_one_of_Pi0_eq_one hJa hodd z.2 hz2
  have : z = 1 := Subtype.ext hz1
  rw [this, orderOf_one] at hz
  omega

omit [Finite G] in
theorem J_le_NJ (hJa : J ≤ centralizer ({a} : Set G)) : J ≤ NJ a J :=
  le_inf Subgroup.le_normalizer hJa

@[expose] noncomputable def N0 (hJa : J ≤ centralizer ({a} : Set G)) : Subgroup ↥(NJ a J) :=
  (Pi0 hJa).ker.map (Subgroup.inclusion (J_le_NJ hJa))

omit [Finite G] in
theorem mem_N0 (hJa : J ≤ centralizer ({a} : Set G)) {x : ↥(NJ a J)} :
    x ∈ N0 hJa ↔ ∃ hxJ : (x : G) ∈ J, Pi0 hJa ⟨(x : G), hxJ⟩ = 1 := by
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k.2, hk⟩
  · rintro ⟨hxJ, h⟩
    exact ⟨⟨(x : G), hxJ⟩, h, Subtype.ext rfl⟩

omit [Finite G] in
theorem N0_normal (hJa : J ≤ centralizer ({a} : Set G)) : (N0 hJa).Normal :=
  ⟨fun n hn g => by
    obtain ⟨hnJ, hn1⟩ := (mem_N0 hJa).1 hn
    refine (mem_N0 hJa).2 ⟨mem_normalizer_conj g.2.1 ⟨(n : G), hnJ⟩, ?_⟩
    have h := rho_Pi0 hJa g ⟨(n : G), hnJ⟩
    rw [hn1, map_one] at h
    exact h.symm⟩

omit [Finite G] in
theorem card_N0 (hJa : J ≤ centralizer ({a} : Set G)) :
    Nat.card (N0 hJa) = Nat.card (Pi0 hJa).ker :=
  Subgroup.card_map_of_injective (Subgroup.inclusion_injective (J_le_NJ hJa))

theorem exists_lift_Pi0 (hJa : J ≤ centralizer ({a} : Set G))
    (hodd : Odd (Nat.card (center ↥(PumpCalc.bar a J)))) {E : Subgroup G} (hE : E ≤ NJ a J)
    (hE2 : ∀ e ∈ E, e * e = 1) {y : J0 a J}
    (hy : ∀ (e : G) (he : e ∈ E), rho hJa ⟨e, hE he⟩ y = y) :
    ∃ g : ↥J, Pi0 hJa g = y ∧ ∀ e ∈ E, e * (g : G) = g * e := by
  classical
  have hNn : (N0 hJa).Normal := N0_normal hJa
  obtain ⟨j, hj⟩ := Pi0_surjective hJa y
  have hN : Odd (Nat.card (N0 hJa)) := by
    rw [card_N0 hJa]
    exact odd_card_ker_Pi0 hJa hodd
  set ι : ↥J →* ↥(NJ a J) := Subgroup.inclusion (J_le_NJ hJa) with hι
  have hA : IsPGroup 2 ↥(E.subgroupOf (NJ a J)) := fun g => ⟨1, by
    have h1 := hE2 (g : ↥(NJ a J)) (Subgroup.mem_subgroupOf.1 g.2)
    apply Subtype.ext
    apply Subtype.ext
    simpa [pow_two] using h1⟩
  have hc : ∀ e ∈ E.subgroupOf (NJ a J), QuotientGroup.mk' (N0 hJa) e *
      QuotientGroup.mk' (N0 hJa) (ι j) = QuotientGroup.mk' (N0 hJa) (ι j) *
        QuotientGroup.mk' (N0 hJa) e := by
    intro e he
    have heE : (e : G) ∈ E := Subgroup.mem_subgroupOf.1 he
    have hinv : ((e⁻¹ : ↥(NJ a J)) : G) ∈ E := by
      have : (e : G)⁻¹ ∈ E := E.inv_mem heE
      exact this
    show (QuotientGroup.mk (e * ι j) : ↥(NJ a J) ⧸ N0 hJa) = QuotientGroup.mk (ι j * e)
    have hmem : (e : G)⁻¹ * (j : G) * (e : G) ∈ J := by
      have := mem_normalizer_conj (J := J) (e⁻¹ : ↥(NJ a J)).2.1 j
      simpa using this
    set k : ↥J := j⁻¹ * ⟨(e : G)⁻¹ * (j : G) * (e : G), hmem⟩ with hk
    have hke : ((e * ι j)⁻¹ * (ι j * e) : ↥(NJ a J)) = ι k := by
      apply Subtype.ext
      simp [hι, hk, mul_assoc]
    rw [QuotientGroup.eq, hke]
    have h1 := rho_Pi0 hJa (e⁻¹) j
    have h2 := hy ((e⁻¹ : ↥(NJ a J)) : G) hinv
    have h3 : rho hJa ⟨((e⁻¹ : ↥(NJ a J)) : G), hE hinv⟩ = rho hJa (e⁻¹) := rfl
    rw [h3, ← hj] at h2
    have h4 : (⟨(e : G)⁻¹ * (j : G) * (e : G), hmem⟩ : ↥J) =
        ⟨((e⁻¹ : ↥(NJ a J)) : G) * (j : G) * ((e⁻¹ : ↥(NJ a J)) : G)⁻¹,
          mem_normalizer_conj (e⁻¹ : ↥(NJ a J)).2.1 j⟩ := by
      apply Subtype.ext
      simp
    have h5 : Pi0 hJa k = 1 := by
      rw [hk, map_mul, map_inv, h4, ← h1, h2, inv_mul_cancel]
    exact ⟨k, h5, rfl⟩
  obtain ⟨g, hg1, hg2⟩ := B1.centralizer_quotient_of_pGroup (N0 hJa) hN hA hc
  have hw := QuotientGroup.eq.1 hg1
  obtain ⟨hwJ, hw1⟩ := (mem_N0 hJa).1 hw
  have hgj : (g : G) = (j : G) * ((g⁻¹ * ι j : ↥(NJ a J)) : G)⁻¹ := by
    simp [hι]
  have hgJ : (g : G) ∈ J := by
    rw [hgj]
    exact J.mul_mem j.2 (J.inv_mem hwJ)
  refine ⟨⟨(g : G), hgJ⟩, ?_, fun e he => ?_⟩
  · have : (⟨(g : G), hgJ⟩ : ↥J) = j * (⟨((g⁻¹ * ι j : ↥(NJ a J)) : G), hwJ⟩ : ↥J)⁻¹ :=
      Subtype.ext hgj
    rw [this, map_mul, map_inv, hw1, inv_one, mul_one, hj]
  · have := hg2 ⟨e, hE he⟩ (Subgroup.mem_subgroupOf.2 he)
    exact congrArg Subtype.val this

theorem exists_lift_invol (hJa : J ≤ centralizer ({a} : Set G))
    (hodd : Odd (Nat.card (center ↥(PumpCalc.bar a J)))) {E : Subgroup G} (hE : E ≤ NJ a J)
    (hE2 : ∀ e ∈ E, e * e = 1) {y : J0 a J} (hy2 : y * y = 1) (hy1 : y ≠ 1)
    (hy : ∀ (e : G) (he : e ∈ E), rho hJa ⟨e, hE he⟩ y = y) :
    ∃ d : ↥J, d * d = 1 ∧ d ≠ 1 ∧ Pi0 hJa d = y ∧ ∀ e ∈ E, e * (d : G) = d * e := by
  obtain ⟨g, hg1, hg2⟩ := exists_lift_Pi0 hJa hodd hE hE2 hy
  have hker : g * g ∈ (Pi0 hJa).ker := by
    rw [MonoidHom.mem_ker, map_mul, hg1, hy2]
  have hodd' := odd_card_ker_Pi0 hJa hodd
  set m := orderOf (⟨g * g, hker⟩ : (Pi0 hJa).ker) with hm
  have hmodd : Odd m := Odd.of_dvd_nat hodd' (orderOf_dvd_natCard _)
  have hgm : (g * g) ^ m = 1 := by simp [hm]
  obtain ⟨k, hk⟩ := hmodd
  have hyp : y ^ m = y := by
    rw [hk, pow_succ, pow_mul, pow_two, hy2, one_pow, one_mul]
  refine ⟨g ^ m, ?_, ?_, ?_, fun e he => ?_⟩
  · rw [← pow_two, ← pow_mul, mul_comm, pow_mul, pow_two, hgm]
  · intro h
    have := congrArg (Pi0 hJa) h
    rw [map_pow, hg1, hyp, map_one] at this
    exact hy1 this
  · rw [map_pow, hg1, hyp]
  · have hc : Commute (e : G) (g : G) := hg2 e he
    show (e : G) * ((g : G) ^ m) = ((g : G) ^ m) * e
    exact hc.pow_right m

end S1FinalLift

end CFSG.GH74.Generic.BProg.B3
