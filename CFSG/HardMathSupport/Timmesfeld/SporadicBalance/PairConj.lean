module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.CommutingPair
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.FiLocal
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3ThreeKit
public import CFSG.LocalAnalysis.SectionRank.Sporadic.LocalWitness
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Reduction

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.CommutingPair

open CFSG.Open
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem oPrimeCoreTrivialAt_of_pair [Finite G] {p : ℕ} [hp : Fact p.Prime] {x y z : G}
    (hcomm : x * y = y * x) (hx : x ^ p = 1) (hy : y ^ p = 1) (hx1 : x ≠ 1)
    (hpow : ∀ k < p, y ≠ x ^ k) (hfac : (Nat.card G).factorization p = 2)
    (hconj : ∀ i j : ℕ, i < p → j < p → i + j ≠ 0 → ∃ m : G, m * (x ^ i * y ^ j) = z * m)
    (hcore : GLAPPrimeCoreOf p (Subgroup.centralizer ({z} : Set G)) = ⊥) :
    OPrimeCoreTrivialAt p G := by
  have hG : ¬ p ^ 3 ∣ Nat.card G := by
    intro h
    have h0 : Nat.card G ≠ 0 := Nat.card_pos.ne'
    have := (hp.out.pow_dvd_iff_le_factorization h0).1 h
    omega
  have hQ := card_closure_pair_eq_sq hcomm hx hy hx1 hpow hG
  have hQfull : Nat.card (Subgroup.closure ({x, y} : Set G)) =
      p ^ (Nat.card (⊤ : Subgroup G)).factorization p := by
    rw [hQ, Subgroup.card_top, hfac]
  intro s hs
  obtain ⟨g, -, hgQ⟩ := Co3T.exists_conj_mem_of_full le_top hQfull (Subgroup.mem_top s) hs
  obtain ⟨i, hi, j, hj, hw⟩ := exists_pow_mul_pow_of_mem hp.out.pos hcomm hx hy hgQ
  have hwo : orderOf (g⁻¹ * s * g) = p := by rw [orderOf_inv_mul_mul, hs]
  have hij : i + j ≠ 0 := by
    intro h0
    have hi0 : i = 0 := by omega
    have hj0 : j = 0 := by omega
    rw [hi0, hj0, pow_zero, pow_zero, mul_one] at hw
    rw [hw, orderOf_one] at hwo
    exact hp.out.one_lt.ne hwo
  obtain ⟨m, hm⟩ := hconj i j hi hj hij
  have hconjs : (m * g⁻¹) * s * (m * g⁻¹)⁻¹ = z := by
    rw [← hw] at hm
    calc (m * g⁻¹) * s * (m * g⁻¹)⁻¹ = (m * (g⁻¹ * s * g)) * m⁻¹ := by group
      _ = z := by rw [hm]; group
  rw [eq_bot_iff]
  intro u hu
  rw [Subgroup.mem_bot]
  have hu' := conj_mem_gLAPPrimeCoreOf_centralizer (m * g⁻¹) s u hu
  rw [hconjs, hcore, Subgroup.mem_bot] at hu'
  calc u = (m * g⁻¹)⁻¹ * ((m * g⁻¹) * u * (m * g⁻¹)⁻¹) * (m * g⁻¹) := by group
    _ = 1 := by rw [hu']; group

theorem commutatorElement_eq_of_pow {p : ℕ} (hp : 0 < p) {x y : G} (hx : x ^ p = 1)
    (hy : y ^ p = 1) : ⁅x, y⁆ = x * y * x ^ (p - 1) * y ^ (p - 1) := by
  have hinv : ∀ a : G, a ^ p = 1 → a⁻¹ = a ^ (p - 1) := fun a ha =>
    inv_eq_of_mul_eq_one_right (by rw [← pow_succ', Nat.sub_add_cancel hp, ha])
  rw [commutatorElement_def, hinv x hx, hinv y hy]

theorem oPrimeCoreTrivialAt_of_cube [Finite G] {p : ℕ} [hp : Fact p.Prime] {x y c : G}
    (hx : x ^ p = 1) (hy : y ^ p = 1) (hc : c = x * y * x ^ (p - 1) * y ^ (p - 1))
    (hcx : c * x = x * c) (hcy : c * y = y * c)
    (hinj : ∀ i j k i' j' k' : ℕ, i < p → j < p → k < p → i' < p → j' < p → k' < p →
      x ^ i * y ^ j * c ^ k = x ^ i' * y ^ j' * c ^ k' → i = i' ∧ j = j' ∧ k = k')
    (hfac : (Nat.card G).factorization p = 3)
    (hconj : ∀ i j k : ℕ, i < p → j < p → k < p → i + j + k ≠ 0 →
      ∃ m : G, m * (x ^ i * y ^ j * c ^ k) = c * m)
    (hcore : GLAPPrimeCoreOf p (Subgroup.centralizer ({c} : Set G)) = ⊥) :
    OPrimeCoreTrivialAt p G := by
  have hp0 : 0 < p := hp.out.pos
  have hxy : ⁅x, y⁆ = c := by rw [hc, commutatorElement_eq_of_pow hp0 hx hy]
  have hzx : Commute ⁅x, y⁆ x := by rw [hxy]; exact hcx
  have hzy : Commute ⁅x, y⁆ y := by rw [hxy]; exact hcy
  have hQ : Nat.card (Subgroup.closure ({x, y} : Set G)) = p ^ 3 := by
    refine CFSG.SectionRank.LocalWitness.card_closure_eq_cube hp0 hx hy hzx hzy ?_
    rintro ⟨i, j, k⟩ ⟨i', j', k'⟩ h
    simp only [hxy] at h
    obtain ⟨h1, h2, h3⟩ := hinj i j k i' j' k' i.2 j.2 k.2 i'.2 j'.2 k'.2 h
    exact Prod.ext (Fin.ext h1) (Prod.ext (Fin.ext h2) (Fin.ext h3))
  have hQfull : Nat.card (Subgroup.closure ({x, y} : Set G)) =
      p ^ (Nat.card (⊤ : Subgroup G)).factorization p := by
    rw [hQ, Subgroup.card_top, hfac]
  intro s hs
  obtain ⟨g, -, hgQ⟩ := Co3T.exists_conj_mem_of_full le_top hQfull (Subgroup.mem_top s) hs
  obtain ⟨i, j, k, hi, hj, hk, hw⟩ :=
    CFSG.SectionRank.LocalWitness.mem_closure_normalForm hp0 hx hy hzx hzy hgQ
  rw [hxy] at hw
  have hwo : orderOf (g⁻¹ * s * g) = p := by rw [orderOf_inv_mul_mul, hs]
  have hijk : i + j + k ≠ 0 := by
    intro h0
    have hi0 : i = 0 := by omega
    have hj0 : j = 0 := by omega
    have hk0 : k = 0 := by omega
    rw [hi0, hj0, hk0, pow_zero, pow_zero, pow_zero, mul_one, mul_one] at hw
    rw [hw, orderOf_one] at hwo
    exact hp.out.one_lt.ne hwo
  obtain ⟨m, hm⟩ := hconj i j k hi hj hk hijk
  have hconjs : (m * g⁻¹) * s * (m * g⁻¹)⁻¹ = c := by
    rw [← hw] at hm
    calc (m * g⁻¹) * s * (m * g⁻¹)⁻¹ = (m * (g⁻¹ * s * g)) * m⁻¹ := by group
      _ = c := by rw [hm]; group
  rw [eq_bot_iff]
  intro u hu
  rw [Subgroup.mem_bot]
  have hu' := conj_mem_gLAPPrimeCoreOf_centralizer (m * g⁻¹) s u hu
  rw [hconjs, hcore, Subgroup.mem_bot] at hu'
  calc u = (m * g⁻¹)⁻¹ * ((m * g⁻¹) * u * (m * g⁻¹)⁻¹) * (m * g⁻¹) := by group
    _ = 1 := by rw [hu']; group

theorem oPrimeCoreTrivialAt_of_cube_reps [Finite G] {p : ℕ} [hp : Fact p.Prime] {x y c : G}
    (hx : x ^ p = 1) (hy : y ^ p = 1) (hc : c = x * y * x ^ (p - 1) * y ^ (p - 1))
    (hcx : c * x = x * c) (hcy : c * y = y * c)
    (hinj : ∀ i j k i' j' k' : ℕ, i < p → j < p → k < p → i' < p → j' < p → k' < p →
      x ^ i * y ^ j * c ^ k = x ^ i' * y ^ j' * c ^ k' → i = i' ∧ j = j' ∧ k = k')
    (hfac : (Nat.card G).factorization p = 3) (reps : List G)
    (hconj : ∀ i j k : ℕ, i < p → j < p → k < p → i + j + k ≠ 0 →
      ∃ m : G, ∃ r ∈ reps, m * (x ^ i * y ^ j * c ^ k) = r * m)
    (hcore : ∀ r ∈ reps, GLAPPrimeCoreOf p (Subgroup.centralizer ({r} : Set G)) = ⊥) :
    OPrimeCoreTrivialAt p G := by
  have hp0 : 0 < p := hp.out.pos
  have hxy : ⁅x, y⁆ = c := by rw [hc, commutatorElement_eq_of_pow hp0 hx hy]
  have hzx : Commute ⁅x, y⁆ x := by rw [hxy]; exact hcx
  have hzy : Commute ⁅x, y⁆ y := by rw [hxy]; exact hcy
  have hQ : Nat.card (Subgroup.closure ({x, y} : Set G)) = p ^ 3 := by
    refine CFSG.SectionRank.LocalWitness.card_closure_eq_cube hp0 hx hy hzx hzy ?_
    rintro ⟨i, j, k⟩ ⟨i', j', k'⟩ h
    simp only [hxy] at h
    obtain ⟨h1, h2, h3⟩ := hinj i j k i' j' k' i.2 j.2 k.2 i'.2 j'.2 k'.2 h
    exact Prod.ext (Fin.ext h1) (Prod.ext (Fin.ext h2) (Fin.ext h3))
  have hQfull : Nat.card (Subgroup.closure ({x, y} : Set G)) =
      p ^ (Nat.card (⊤ : Subgroup G)).factorization p := by
    rw [hQ, Subgroup.card_top, hfac]
  intro s hs
  obtain ⟨g, -, hgQ⟩ := Co3T.exists_conj_mem_of_full le_top hQfull (Subgroup.mem_top s) hs
  obtain ⟨i, j, k, hi, hj, hk, hw⟩ :=
    CFSG.SectionRank.LocalWitness.mem_closure_normalForm hp0 hx hy hzx hzy hgQ
  rw [hxy] at hw
  have hwo : orderOf (g⁻¹ * s * g) = p := by rw [orderOf_inv_mul_mul, hs]
  have hijk : i + j + k ≠ 0 := by
    intro h0
    have hi0 : i = 0 := by omega
    have hj0 : j = 0 := by omega
    have hk0 : k = 0 := by omega
    rw [hi0, hj0, hk0, pow_zero, pow_zero, pow_zero, mul_one, mul_one] at hw
    rw [hw, orderOf_one] at hwo
    exact hp.out.one_lt.ne hwo
  obtain ⟨m, r, hr, hm⟩ := hconj i j k hi hj hk hijk
  have hconjs : (m * g⁻¹) * s * (m * g⁻¹)⁻¹ = r := by
    rw [← hw] at hm
    calc (m * g⁻¹) * s * (m * g⁻¹)⁻¹ = (m * (g⁻¹ * s * g)) * m⁻¹ := by group
      _ = r := by rw [hm]; group
  rw [eq_bot_iff]
  intro u hu
  rw [Subgroup.mem_bot]
  have hu' := conj_mem_gLAPPrimeCoreOf_centralizer (m * g⁻¹) s u hu
  rw [hconjs, hcore r hr, Subgroup.mem_bot] at hu'
  calc u = (m * g⁻¹)⁻¹ * ((m * g⁻¹) * u * (m * g⁻¹)⁻¹) * (m * g⁻¹) := by group
    _ = 1 := by rw [hu']; group

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.CommutingPair
