module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.HardMathSupport.Timmesfeld.Tables.T1b

theorem dvd_mul_of_dvd_sq_mul {p g a : ℕ} (hp : p.Prime) (hg : ¬ p ^ 2 ∣ g)
    (h : g ∣ p ^ 2 * a) : g ∣ p * a := by
  by_cases hpg : p ∣ g
  · obtain ⟨g', rfl⟩ := hpg
    have hpg' : ¬ p ∣ g' := by
      rintro ⟨c, rfl⟩
      exact hg ⟨c, by ring⟩
    have h1 : g' ∣ p * a := by
      have : p * g' ∣ p * (p * a) := by
        have e : p ^ 2 * a = p * (p * a) := by ring
        rwa [e] at h
      exact Nat.dvd_of_mul_dvd_mul_left hp.pos this
    have hc : Nat.Coprime g' p := ((Nat.Prime.coprime_iff_not_dvd hp).2 hpg').symm
    have h2 : g' ∣ a := hc.dvd_of_dvd_mul_left h1
    exact mul_dvd_mul_left p h2
  · have hc : Nat.Coprime g p := ((Nat.Prime.coprime_iff_not_dvd hp).2 hpg).symm
    have hc2 : Nat.Coprime g (p ^ 2) := hc.pow_right 2
    exact Dvd.dvd.mul_left (hc2.dvd_of_dvd_mul_left h) p

theorem exists_pow_eq_of_pow_sq_eq {Z : Type*} [CommGroup Z] [Finite Z] [IsCyclic Z] {p n : ℕ}
    (hp : p.Prime) (hg : ¬ p ^ 2 ∣ Nat.gcd n (Nat.card Z)) {ν u : Z}
    (h : ν ^ (p ^ 2) = u ^ n) : ∃ μ : Z, μ ^ n = ν ^ p := by
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := Z)
  have hord : orderOf γ = Nat.card Z := orderOf_eq_card_of_forall_mem_zpowers hγ
  obtain ⟨a, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hγ ν)
  obtain ⟨b, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hγ u)
  set N := Nat.card Z with hN
  set G := Nat.gcd n N with hG
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, zpow_eq_zpow_iff_modEq, hord] at h
  have hdvd : (N : ℤ) ∣ b * n - a * (p ^ 2 : ℕ) := (Int.modEq_iff_dvd.1 h)
  have hGN : (G : ℤ) ∣ N := Int.natCast_dvd_natCast.2 (Nat.gcd_dvd_right n N)
  have hGn : (G : ℤ) ∣ n := Int.natCast_dvd_natCast.2 (Nat.gcd_dvd_left n N)
  have h2 : (G : ℤ) ∣ a * (p ^ 2 : ℕ) := by
    have : (G : ℤ) ∣ b * n - a * (p ^ 2 : ℕ) := hGN.trans hdvd
    have h3 : (G : ℤ) ∣ b * n := Dvd.dvd.mul_left hGn b
    have := dvd_sub h3 this
    simpa using this
  have h4 : G ∣ p * a.natAbs := by
    have : G ∣ (a * (p ^ 2 : ℕ)).natAbs := Int.natCast_dvd.1 h2
    rw [Int.natAbs_mul, Int.natAbs_natCast] at this
    apply dvd_mul_of_dvd_sq_mul hp hg
    rwa [mul_comm] at this
  have h5 : (G : ℤ) ∣ a * p := by
    have : (G : ℤ) ∣ (p : ℤ) * a := by
      apply (Int.natCast_dvd).2
      rw [Int.natAbs_mul, Int.natAbs_natCast]
      exact h4
    rwa [mul_comm] at this
  obtain ⟨c, hc⟩ := h5
  have hbez : (G : ℤ) = n * Nat.gcdA n N + N * Nat.gcdB n N := Nat.gcd_eq_gcd_ab n N
  refine ⟨γ ^ (Nat.gcdA n N * c), ?_⟩
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, zpow_eq_zpow_iff_modEq, hord]
  apply Int.modEq_iff_dvd.2
  refine ⟨Nat.gcdB n N * c, ?_⟩
  have : (a * p : ℤ) = G * c := hc
  have e : (a * (p : ℤ)) = (n * Nat.gcdA n N + N * Nat.gcdB n N) * c := by rw [this, hbez]
  linear_combination e

private theorem exists_pow_eq_of_pow_eq_one {G : Type*} [CommGroup G] [Finite G] [IsCyclic G]
    {n m : ℕ} (hcard : Nat.card G = n * m) {x : G} (hx : x ^ m = 1) : ∃ t : G, t ^ n = x := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  have hord : orderOf g = n * m := (orderOf_eq_card_of_forall_mem_zpowers hg).trans hcard
  have hm : m ≠ 0 := by
    rintro rfl
    have : 0 < Nat.card G := Nat.card_pos
    rw [hcard] at this
    simp at this
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hg x)
  have h1 : (orderOf g : ℤ) ∣ j * m := by
    rw [orderOf_dvd_iff_zpow_eq_one, zpow_mul, zpow_natCast]
    exact hx
  rw [hord] at h1
  push_cast at h1
  have h2 : (n : ℤ) ∣ j := by
    have hm' : (m : ℤ) ≠ 0 := by exact_mod_cast hm
    rw [mul_comm (n : ℤ) m, mul_comm j m] at h1
    exact (mul_dvd_mul_iff_left hm').1 h1
  obtain ⟨k, rfl⟩ := h2
  exact ⟨g ^ k, by rw [← zpow_natCast, ← zpow_mul, mul_comm]⟩

theorem fixed_unit_isPow {K : Type*} [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (_hp2 : p ≠ 2)
    (σ : K ≃+* K) (hσ : orderOf σ = p) (hpK : p ∣ Nat.card K - 1) :
    ∀ x : K, σ x = x → x ≠ 0 → ∃ y : K, y ^ p = x := by
  intro x hx hx0
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype K := Fintype.ofFinite K
  have : Finite (K ≃+* K) := Finite.of_injective (fun f : K ≃+* K => (f : K → K)) DFunLike.coe_injective
  let H : Subgroup (K ≃+* K) := Subgroup.zpowers σ
  have hH : Nat.card H = p := by rw [Nat.card_zpowers, hσ]
  have : Fintype H := Fintype.ofFinite H
  have hfr : Module.finrank (FixedPoints.subfield H K) K = p := by
    rw [FixedPoints.finrank_eq_card H K, Fintype.card_eq_nat_card, hH]
  set K0 := FixedPoints.subfield H K with hK0
  have hcard : Nat.card K = Nat.card K0 ^ p := by
    rw [Module.natCard_eq_pow_finrank (K := K0) (V := K), hfr]
  have hxK0 : x ∈ K0 := by
    have hst : σ ∈ MulAction.stabilizer (K ≃+* K) x := by
      rw [MulAction.mem_stabilizer_iff]; exact hx
    have hle : H ≤ MulAction.stabilizer (K ≃+* K) x := Subgroup.zpowers_le.2 hst
    intro h
    exact MulAction.mem_stabilizer_iff.1 (hle h.2)
  set Q0 := Nat.card K0 with hQ0
  have hQpos : 0 < Q0 := Nat.card_pos
  have hxpow : x ^ (Q0 - 1) = 1 := by
    have : Fintype K0 := Fintype.ofFinite K0
    have h1 := FiniteField.pow_card_sub_one_eq_one (⟨x, hxK0⟩ : K0) (fun h => hx0 (congrArg Subtype.val h))
    have h2 := congrArg Subtype.val h1
    simpa [hQ0, Nat.card_eq_fintype_card] using h2
  have hQK : 1 ≤ Q0 ^ p := Nat.one_le_pow _ _ hQpos
  have hdvd : p ∣ Q0 ^ p - 1 := by rwa [hcard] at hpK
  have hmodp : ((Q0 : ℕ) : ZMod p) = 1 := by
    have h1 : ((Q0 ^ p : ℕ) : ZMod p) = 1 := by
      have := (Nat.modEq_iff_dvd' hQK).2 hdvd
      have h3 := (ZMod.natCast_eq_natCast_iff _ _ _).2 this
      simpa using h3.symm
    have h2 : ((Q0 : ℕ) : ZMod p) ^ p = (Q0 : ZMod p) := ZMod.pow_card _
    push_cast at h1
    rw [← h2]; exact h1
  have hS : p ∣ ∑ i ∈ Finset.range p, Q0 ^ i := by
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    simp [hmodp]
  obtain ⟨S', hS'⟩ := hS
  have hgeom : Nat.card K - 1 = (Q0 - 1) * (∑ i ∈ Finset.range p, Q0 ^ i) := by
    rw [hcard]
    zify [hQpos, hQK]
    rw [mul_comm]
    rw [geom_sum_mul]
  have hcardU : Nat.card Kˣ = p * ((Q0 - 1) * S') := by
    rw [Nat.card_units, hgeom, hS']; ring
  have hu : (Units.mk0 x hx0) ^ ((Q0 - 1) * S') = 1 := by
    rw [pow_mul]
    have : (Units.mk0 x hx0) ^ (Q0 - 1) = 1 := by
      ext; simpa using hxpow
    rw [this, one_pow]
  obtain ⟨t, ht⟩ := exists_pow_eq_of_pow_eq_one hcardU hu
  exact ⟨(t : K), by
    have := congrArg Units.val ht
    simpa using this⟩

theorem card_le_mul_card_inf_of_cyclic {G : Type*} [Group G] [Finite G] (N : Subgroup G)
    [N.Normal] [IsCyclic (G ⧸ N)] {p : ℕ} (hp : p.Prime) (E : Subgroup G)
    (hE : CFSG.Open.IsElemAbelian p E) : Nat.card E ≤ p * Nat.card ↥(E ⊓ N) := by
  let φ : E →* G ⧸ N := (QuotientGroup.mk' N).comp E.subtype
  have hker : Nat.card φ.ker = Nat.card ↥(E ⊓ N) := by
    have : φ.ker = (E ⊓ N).subgroupOf E := by
      ext x
      simp [φ, MonoidHom.mem_ker, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    rw [this]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hrange : Nat.card φ.range ≤ p := by
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := φ.range)
    have h1 : Nat.card φ.range = orderOf g :=
      (orderOf_eq_card_of_forall_mem_zpowers hg).symm
    have h2 : g ^ p = 1 := by
      obtain ⟨x, hx⟩ := g.2
      apply Subtype.ext
      have hxp : x ^ p = 1 := Subtype.ext (hE.2 x x.2)
      simp only [Subgroup.coe_pow, OneMemClass.coe_one]
      rw [← hx, ← map_pow, hxp, map_one]
    rw [h1]
    exact Nat.le_of_dvd hp.pos (orderOf_dvd_of_pow_eq_one h2)
  calc Nat.card E = Nat.card φ.ker * Nat.card φ.range :=
        (Subgroup.card_ker_mul_card_range φ).symm
    _ ≤ Nat.card ↥(E ⊓ N) * p := by rw [hker]; exact Nat.mul_le_mul_left _ hrange
    _ = p * Nat.card ↥(E ⊓ N) := mul_comm _ _

end CFSG.HardMathSupport.Timmesfeld.Tables.T1b
