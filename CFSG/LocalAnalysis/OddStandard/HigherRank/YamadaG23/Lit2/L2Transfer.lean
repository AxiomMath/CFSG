module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit2.L2Defs

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

theorem l2_pauli_transfer {G H J : Type} [Group G] [Group H] [Group J] [Finite G]
    (α : G →* H) (hα : Function.Surjective α) (ρ : H →* J)
    (hρk : ρ.ker = center H) (hH2 : IsPGroup 2 ↥(center H))
    {A : Subgroup J} (hE : IsE 4 ↥A) (hP : L2Pauli ρ A)
    {m : G} (hm1 : m ≠ 1) (hm2 : m * m = 1) (hmk : m ∈ (ρ.comp α).ker)
    (hmu : ∀ u ∈ (ρ.comp α).ker, u * u = 1 → u = 1 ∨ u = m)
    (hcen : ∀ u ∈ (ρ.comp α).ker, ∀ x : G, u * x = x * u) :
    (∀ x y : G, (ρ.comp α) x ∈ A → (ρ.comp α) y ∈ A → ⁅x, y⁆ = 1 ∨ ⁅x, y⁆ = m) ∧
    (∀ x : G, (ρ.comp α) x ∈ A → (ρ.comp α) x ≠ 1 →
      ∃ y : G, (ρ.comp α) y ∈ A ∧ ⁅x, y⁆ = m) ∧
    (∀ e ∈ A, ∃ x : G, (ρ.comp α) x = e ∧ ∃ k ∈ (ρ.comp α).ker, Odd (orderOf k) ∧
      (x * x = k ∨ x * x = m * k)) := by
  obtain ⟨hEab, hEcard⟩ := hE
  obtain ⟨hEcomm, hEsq⟩ := hEab
  rw [isMulCommutative_iff_of_setLike] at hEcomm
  have E1 : ∀ e ∈ A, e * e = 1 := by
    intro e he
    have h : (⟨e, he⟩ : ↥A) * ⟨e, he⟩ = 1 := by
      simpa [pow_two] using hEsq ⟨e, he⟩ (Subgroup.mem_top _)
    simpa using congrArg Subtype.val h
  have E2 : ∀ e ∈ A, ∀ f ∈ A, e * f = f * e := by
    intro e he f hf
    have h : (⟨e, he⟩ : ↥A) * ⟨f, hf⟩ = ⟨f, hf⟩ * ⟨e, he⟩ :=
      hEcomm ⟨e, he⟩ (Subgroup.mem_top _) ⟨f, hf⟩ (Subgroup.mem_top _)
    simpa using congrArg Subtype.val h
  have E3 : ∃ e ∈ A, e ≠ 1 := by
    by_contra h
    push_neg at h
    have hbot : A = ⊥ := (Subgroup.eq_bot_iff_forall A).mpr h
    rw [hbot, Subgroup.card_bot] at hEcard
    norm_num at hEcard
  obtain ⟨e, he, hene⟩ := E3
  obtain ⟨z, _hz_center, hz_order, _hP1, hP2, hP3⟩ := hP
  have hz_ne : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz_order
    norm_num at hz_order
  have hz_sq : z * z = 1 := by
    simpa [hz_order, pow_two] using pow_orderOf_eq_one z
  have sq_mem_ker : ∀ x : G, (ρ.comp α) x ∈ A → x * x ∈ (ρ.comp α).ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    change ρ (α (x * x)) = 1
    rw [map_mul, map_mul]
    exact E1 ((ρ.comp α) x) hx
  have comm_mem_ker : ∀ x y : G, (ρ.comp α) x ∈ A → (ρ.comp α) y ∈ A →
      ⁅x, y⁆ ∈ (ρ.comp α).ker := by
    intro x y hx hy
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr
      (E2 ((ρ.comp α) x) hx ((ρ.comp α) y) hy)
  have step1 : ∀ x y : G, (ρ.comp α) x ∈ A → (ρ.comp α) y ∈ A →
      ⁅x, y⁆ = 1 ∨ ⁅x, y⁆ = m := by
    intro x y hx hy
    have hc_mem := comm_mem_ker x y hx hy
    have hc_comm : ∀ t : G, ⁅x, y⁆ * t = t * ⁅x, y⁆ := hcen ⁅x, y⁆ hc_mem
    have hxx_mem := sq_mem_ker x hx
    have hxx_comm : ∀ t : G, (x * x) * t = t * (x * x) := hcen (x * x) hxx_mem
    have hcomm2 : ⁅x * x, y⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr (hxx_comm y)
    have hpow : ⁅x, y⁆ ^ 2 = ⁅x ^ 2, y⁆ :=
      Commute.commutatorElement_pow_left (a := x) (b := y)
        ((commute_iff_eq x ⁅x, y⁆).mpr (hc_comm x).symm) 2
    have hsq : ⁅x, y⁆ * ⁅x, y⁆ = 1 := by
      rw [← pow_two, hpow]
      simpa [pow_two] using hcomm2
    exact hmu ⁅x, y⁆ hc_mem hsq
  have hαm : α m = z := by
    obtain ⟨xH, hxH_rho, -⟩ := hP3 e he
    have hxH_A : ρ xH ∈ A := by rw [hxH_rho]; exact he
    have hxH_ne : ρ xH ≠ 1 := by rw [hxH_rho]; exact hene
    obtain ⟨yH, hyH_A, hyH_comm⟩ := hP2 xH hxH_A hxH_ne
    obtain ⟨x, hx⟩ := hα xH
    obtain ⟨y, hy⟩ := hα yH
    have hpx : (ρ.comp α) x ∈ A := by
      change ρ (α x) ∈ A
      rw [hx]; exact hxH_A
    have hpy : (ρ.comp α) y ∈ A := by
      change ρ (α y) ∈ A
      rw [hy]; exact hyH_A
    have hαc : α ⁅x, y⁆ = z := by
      rw [map_commutatorElement, hx, hy]
      exact hyH_comm
    rcases step1 x y hpx hpy with h | h
    · rw [h, map_one] at hαc
      exact absurd hαc.symm hz_ne
    · rw [h] at hαc
      exact hαc
  have step4 : ∀ u ∈ α.ker, Odd (orderOf u) := by
    intro u hu
    by_contra hodd
    rw [Nat.not_odd_iff_even] at hodd
    obtain ⟨r, hr⟩ := even_iff_exists_two_mul.mp hodd
    have hrpos : 0 < r := by
      have := orderOf_pos u
      omega
    have hαu : α u = 1 := MonoidHom.mem_ker.mp hu
    have hw2 : (u ^ r) * (u ^ r) = 1 := by
      rw [← pow_two, ← pow_mul, Nat.mul_comm r 2, ← hr, pow_orderOf_eq_one]
    have hw_ne : u ^ r ≠ 1 := by
      intro hw
      have hdvd : orderOf u ∣ r := by
        rw [orderOf_dvd_iff_pow_eq_one]
        exact hw
      rw [hr] at hdvd
      have := Nat.le_of_dvd hrpos hdvd
      omega
    have hw_mem : u ^ r ∈ (ρ.comp α).ker := by
      rw [MonoidHom.mem_ker]
      change ρ (α (u ^ r)) = 1
      rw [map_pow, hαu, one_pow, map_one]
    rcases hmu (u ^ r) hw_mem hw2 with h | h
    · exact hw_ne h
    · have hm1eq : α m = 1 := by
        rw [← h, map_pow, hαu, one_pow]
      exact absurd (hαm ▸ hm1eq) hz_ne
  have step3 : ∀ x : G, (ρ.comp α) x ∈ A → (ρ.comp α) x ≠ 1 →
      ∃ y : G, (ρ.comp α) y ∈ A ∧ ⁅x, y⁆ = m := by
    intro x hx hxne
    have hxHA : ρ (α x) ∈ A := hx
    have hxHne : ρ (α x) ≠ 1 := hxne
    obtain ⟨yH, hyH_A, hyH_comm⟩ := hP2 (α x) hxHA hxHne
    obtain ⟨y, hy⟩ := hα yH
    have hpy : (ρ.comp α) y ∈ A := by
      change ρ (α y) ∈ A
      rw [hy]; exact hyH_A
    have hαc : α ⁅x, y⁆ = z := by
      rw [map_commutatorElement, hy]
      exact hyH_comm
    rcases step1 x y hx hpy with h | h
    · rw [h, map_one] at hαc
      exact absurd hαc.symm hz_ne
    · exact ⟨y, hpy, h⟩
  have step5 : ∀ e ∈ A, ∃ x : G, (ρ.comp α) x = e ∧ ∃ k ∈ (ρ.comp α).ker, Odd (orderOf k) ∧
      (x * x = k ∨ x * x = m * k) := by
    intro e he
    obtain ⟨xH, hxH_rho, hxH_sq⟩ := hP3 e he
    obtain ⟨x, hx⟩ := hα xH
    have hpx : (ρ.comp α) x = e := by
      change ρ (α x) = e
      rw [hx, hxH_rho]
    have hxHsq : α (x * x) = xH ^ 2 := by
      rw [map_mul, hx, pow_two]
    have hxx_pker : x * x ∈ (ρ.comp α).ker := sq_mem_ker x (by rw [hpx]; exact he)
    rcases hxH_sq with h1 | h2
    · refine ⟨x, hpx, x * x, hxx_pker, ?_, Or.inl rfl⟩
      have : α (x * x) = 1 := by rw [hxHsq, h1]
      exact step4 (x * x) (MonoidHom.mem_ker.mpr this)
    · have hk_aker : m * (x * x) ∈ α.ker := by
        rw [MonoidHom.mem_ker, map_mul, hαm, hxHsq, h2, hz_sq]
      have hk_pker : m * (x * x) ∈ (ρ.comp α).ker := by
        rw [MonoidHom.mem_ker]
        change ρ (α (m * (x * x))) = 1
        rw [MonoidHom.mem_ker.mp hk_aker, map_one]
      have hmk_eq : x * x = m * (m * (x * x)) := by
        rw [← mul_assoc, hm2, one_mul]
      exact ⟨x, hpx, m * (x * x), hk_pker, step4 (m * (x * x)) hk_aker, Or.inr hmk_eq⟩
  exact ⟨step1, step3, step5⟩

end CFSG.OddStandard.HigherRank.YamadaG23
