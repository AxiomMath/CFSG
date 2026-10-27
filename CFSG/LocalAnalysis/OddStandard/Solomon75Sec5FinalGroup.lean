module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5DefsModel

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.GH74.GLS

section InvConj

variable {G : Type} [Group G]

theorem exists_conj_of_inv_mul_mem_odd {O : Subgroup G} (hodd : Odd (Nat.card O)) {x y : G}
    (hx : x * x = 1) (hy : y * y = 1) (hxy : x⁻¹ * y ∈ O) : ∃ q ∈ O, y = q⁻¹ * x * q := by
  obtain ⟨j, hj⟩ := hodd
  set p := x⁻¹ * y with hp
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hyx : y = x * p := by rw [hp]; group
  have hpinv : x * p * x⁻¹ = p⁻¹ := by
    have h2 : x * p * x * p = 1 := by
      have := hy
      rw [hyx] at this
      simpa [mul_assoc] using this
    calc x * p * x⁻¹ = x * p * x := by rw [hxi]
      _ = x * p * x * (p * p⁻¹) := by group
      _ = (x * p * x * p) * p⁻¹ := by group
      _ = p⁻¹ := by rw [h2]; group
  have hpow : p ^ (2 * j + 1) = 1 := by
    have h1 : (⟨p, hxy⟩ : O) ^ Nat.card O = 1 := pow_card_eq_one'
    have h2 := congrArg (fun w : O => (w : G)) h1
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at h2
    rwa [hj] at h2
  set q := p ^ (j + 1) with hq
  have hqO : q ∈ O := O.pow_mem hxy _
  have hq2 : q * q = p := by
    calc q * q = p ^ (2 * j + 1) * p := by rw [hq, ← pow_add, ← pow_succ]; congr 1; ring
      _ = p := by rw [hpow, one_mul]
  have hxq : x * q * x⁻¹ = q⁻¹ := by
    rw [hq, ← conj_pow, hpinv, inv_pow]
  refine ⟨q, hqO, ?_⟩
  have h5 : x * q = q⁻¹ * x := by
    calc x * q = (x * q * x⁻¹) * x := by group
      _ = q⁻¹ * x := by rw [hxq]
  have h6 : q⁻¹ * q⁻¹ = p⁻¹ := by rw [← mul_inv_rev, hq2]
  calc y = x * p := hyx
    _ = p⁻¹ * x := by
      calc x * p = (x * p * x⁻¹) * x := by group
        _ = p⁻¹ * x := by rw [hpinv]
    _ = q⁻¹ * q⁻¹ * x := by rw [h6]
    _ = q⁻¹ * (q⁻¹ * x) := by group
    _ = q⁻¹ * (x * q) := by rw [h5]
    _ = q⁻¹ * x * q := by group

theorem pow_card_sq_eq_one {O : Subgroup G} {t : G} (ht : t * t ∈ O) :
    t ^ Nat.card O * t ^ Nat.card O = 1 := by
  have h1 : (⟨t * t, ht⟩ : O) ^ Nat.card O = 1 := pow_card_eq_one'
  have h2 := congrArg (fun w : O => (w : G)) h1
  simp only [Subgroup.coe_pow, Subgroup.coe_one] at h2
  rw [← pow_add, ← two_mul, pow_mul, sq]
  exact h2

theorem eq_one_of_sq_eq_one_of_mem_odd {O : Subgroup G} (hodd : Odd (Nat.card O)) {x : G}
    (hxO : x ∈ O) (hx : x * x = 1) : x = 1 := by
  have h1 : orderOf (⟨x, hxO⟩ : O) ∣ Nat.card O := orderOf_dvd_natCard _
  have h2 : orderOf (⟨x, hxO⟩ : O) ∣ 2 := by
    apply orderOf_dvd_of_pow_eq_one
    apply Subtype.ext
    simpa [sq] using hx
  have h3 : Nat.Coprime 2 (Nat.card O) := Nat.coprime_two_left.2 hodd
  have h4 : orderOf (⟨x, hxO⟩ : O) = 1 := Nat.eq_one_of_dvd_coprimes h3 h2 h1
  have h5 := orderOf_eq_one_iff.1 h4
  exact congrArg (fun w : O => (w : G)) h5

end InvConj

section Quot

variable {X : Type} [Group X] [Finite X]

theorem oddCoreOf_eq_inf {A N : Subgroup X} (hAN : A ≤ N) (hNA : N ≤ normalizer (A : Set X)) :
    oddCoreOf A = A ⊓ oddCoreOf N := by
  apply le_antisymm
  · refine le_inf (oddCoreOf_le A) ?_
    refine le_oddCoreOf_of_normalized (oddCoreOf_le A |>.trans hAN) ?_ (odd_card_oddCoreOf A)
    intro c hc
    exact mem_normalizer_oddCoreOf_of_mem_normalizer (hNA hc)
  · have hodd : Odd (Nat.card ↥(A ⊓ oddCoreOf N)) :=
      Odd.of_dvd_nat (odd_card_oddCoreOf N) (Subgroup.card_dvd_of_le inf_le_right)
    refine le_oddCoreOf_of_normalized inf_le_left ?_ hodd
    intro a ha
    exact mem_normalizer_inf (Subgroup.le_normalizer ha)
      (le_normalizer_oddCoreOf N (hAN ha))

theorem quotOddCore_equiv {A N : Subgroup X} (hAN : A ≤ N) (hNA : N ≤ normalizer (A : Set X))
    (hsurj : ∀ c ∈ N, ∃ a ∈ A, ∃ o ∈ oddCoreOf N, c = a * o) :
    Nonempty ((↥A ⧸ pPrimeCore 2 ↥A) ≃* (↥N ⧸ pPrimeCore 2 ↥N)) := by
  let f : ↥A →* ↥N ⧸ pPrimeCore 2 ↥N :=
    (QuotientGroup.mk' (pPrimeCore 2 ↥N)).comp (Subgroup.inclusion hAN)
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨a, ha, o, ho, hc⟩ := hsurj c c.2
    refine ⟨⟨a, ha⟩, ?_⟩
    obtain ⟨hoN, hoP⟩ := mem_oddCoreOf_iff.1 ho
    have h1 : (⟨a, hAN ha⟩ : ↥N) = c * (⟨o, hoN⟩ : ↥N)⁻¹ := by
      apply Subtype.ext
      simp [hc]
    show (QuotientGroup.mk (⟨a, hAN ha⟩ : ↥N) : ↥N ⧸ pPrimeCore 2 ↥N) = QuotientGroup.mk c
    rw [h1, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    have : (QuotientGroup.mk (⟨o, hoN⟩ : ↥N) : ↥N ⧸ pPrimeCore 2 ↥N) = 1 :=
      (QuotientGroup.eq_one_iff _).2 hoP
    rw [this]
    simp
  have hker : f.ker = pPrimeCore 2 ↥A := by
    ext a
    rw [MonoidHom.mem_ker]
    show (QuotientGroup.mk (⟨a.1, hAN a.2⟩ : ↥N) : ↥N ⧸ pPrimeCore 2 ↥N) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff]
    have h1 : (a : X) ∈ oddCoreOf A ↔ (a : X) ∈ A ⊓ oddCoreOf N := by
      rw [oddCoreOf_eq_inf hAN hNA]
    constructor
    · intro h
      have h2 : (a : X) ∈ oddCoreOf N := mem_oddCoreOf_iff.2 ⟨hAN a.2, h⟩
      obtain ⟨_, hP⟩ := mem_oddCoreOf_iff.1 (h1.2 ⟨a.2, h2⟩)
      exact hP
    · intro h
      have h2 : (a : X) ∈ oddCoreOf A := mem_oddCoreOf_iff.2 ⟨a.2, h⟩
      have h3 : (a : X) ∈ oddCoreOf N := (h1.1 h2).2
      obtain ⟨_, hP⟩ := mem_oddCoreOf_iff.1 h3
      exact hP
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf))⟩

end Quot

end CFSG.OddStandard.Solomon75
