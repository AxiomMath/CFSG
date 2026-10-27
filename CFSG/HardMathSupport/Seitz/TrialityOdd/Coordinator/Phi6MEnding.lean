module

public import CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator.Phi6TorusFull

set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator

open Subgroup CFSG.LieType.Steinberg.TwistedD4 CFSG.ClassicalInvolution.G2D4Models
open scoped MatrixGroups

theorem exists_mul_of_mem_sup {G : Type*} [Group G] {X A : Subgroup G}
    (hXA : X ≤ Subgroup.normalizer (A : Set G)) {g : G} (hg : g ∈ X ⊔ A) :
    ∃ x ∈ X, ∃ a ∈ A, g = x * a := by
  let S : Subgroup G :=
    { carrier := {g | ∃ x ∈ X, ∃ a ∈ A, g = x * a}
      mul_mem' := by
        rintro _ _ ⟨x, hx, a, ha, rfl⟩ ⟨x', hx', a', ha', rfl⟩
        refine ⟨x * x', X.mul_mem hx hx', x'⁻¹ * a * x' * a', A.mul_mem ?_ ha', by group⟩
        have := (Subgroup.mem_normalizer_iff.1 (hXA (X.inv_mem hx')) a).1 ha
        simpa using this
      one_mem' := ⟨1, X.one_mem, 1, A.one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨x, hx, a, ha, rfl⟩
        refine ⟨x⁻¹, X.inv_mem hx, x * a⁻¹ * x⁻¹, ?_, by group⟩
        exact (Subgroup.mem_normalizer_iff.1 (hXA hx) a⁻¹).1 (A.inv_mem ha) }
  have hle : X ⊔ A ≤ S := sup_le (fun x hx => ⟨x, hx, 1, A.one_mem, by simp⟩)
    (fun a ha => ⟨1, X.one_mem, a, ha, by simp⟩)
  exact hle hg

theorem le_normalizer_of_commute {G : Type*} [Group G] {A B : Subgroup G}
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) : B ≤ Subgroup.normalizer (A : Set G) := by
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro a
  constructor
  · intro ha
    have h : y * a * y⁻¹ = a := by rw [← hcomm a ha y hy]; group
    rw [h]
    exact ha
  · intro ha
    have h := hcomm _ ha y hy
    have h' : y * a = y * (y * a * y⁻¹) := by
      calc y * a = y * a * y⁻¹ * y := by group
        _ = y * (y * a * y⁻¹) := h
    rw [mul_left_cancel h']
    exact ha

theorem sup_le_of_normalizer_of_rclosure {G : Type*} [Group G] {A B X H : Subgroup G}
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hXN : X ≤ Subgroup.normalizer (A : Set G))
    (hXH : X ≤ H) (hBX : B ≤ X ⊔ A) {r : ℕ} (hrA : ¬ r ∣ Nat.card A) {b : G} (hbB : b ∈ B)
    (hbr : orderOf b = r)
    (hR : ∀ c ∈ H, c ^ r = 1 → c ≠ 1 → Subgroup.centralizer ({c} : Set G) ≤ H) :
    A ⊔ B ≤ H := by
  obtain ⟨x, hx, a, ha, hbxa⟩ := exists_mul_of_mem_sup hXN (hBX hbB)
  have hxba : x = b * a⁻¹ := by rw [hbxa]; group
  have hapow : a⁻¹ ^ Nat.card A = 1 := by
    have h := congrArg Subtype.val (pow_card_eq_one' (G := ↥A) (x := ⟨a⁻¹, A.inv_mem ha⟩))
    rwa [Subgroup.coe_pow, Subgroup.coe_one] at h
  have hxc : x ^ Nat.card A = b ^ Nat.card A := by
    have hc : Commute b a⁻¹ := (hcomm _ (A.inv_mem ha) b hbB).symm
    rw [hxba, hc.mul_pow, hapow, mul_one]
  have hcH : b ^ Nat.card A ∈ H := hxc ▸ hXH (X.pow_mem hx _)
  have hcr : (b ^ Nat.card A) ^ r = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, ← hbr, pow_orderOf_eq_one, one_pow]
  have hc1 : b ^ Nat.card A ≠ 1 := fun h => hrA (hbr ▸ orderOf_dvd_of_pow_eq_one h)
  have hAH : A ≤ H := fun a' ha' => hR _ hcH hcr hc1
    (Subgroup.mem_centralizer_singleton_iff.2 (hcomm a' ha' _ (B.pow_mem hbB _)))
  exact sup_le hAH (hBX.trans (sup_le hXH hAH))

theorem sup_le_of_le_sup_of_rclosure {G : Type*} [Group G] {A B X H : Subgroup G}
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hXle : X ≤ A ⊔ B) (hXH : X ≤ H)
    (hBX : B ≤ X ⊔ A) {r : ℕ} (hrA : ¬ r ∣ Nat.card A) {b : G} (hbB : b ∈ B)
    (hbr : orderOf b = r)
    (hR : ∀ c ∈ H, c ^ r = 1 → c ≠ 1 → Subgroup.centralizer ({c} : Set G) ≤ H) :
    A ⊔ B ≤ H :=
  sup_le_of_normalizer_of_rclosure hcomm
    (hXle.trans (sup_le Subgroup.le_normalizer (le_normalizer_of_commute hcomm))) hXH hBX hrA hbB
    hbr hR


variable {K : Type} [Field K] [Finite K] {σ : K →+* K} (hσ : ∀ c, σ (σ (σ c)) = c)

include hσ in
theorem invCentGroup_le_of_slB_le {r : ℕ} [Fact r.Prime] (hrK2 : r ∣ Nat.card K ^ 2 - 1)
    (hrF : ¬ r ∣ Nat.card (SL(2, fixedField σ))) {X H : Subgroup (twistedGroup σ)}
    (hXle : X ≤ invCentGroup σ hσ) (hXH : X ≤ H)
    (hBX : (slB σ hσ).range ≤ X ⊔ (slLong σ hσ).range)
    (hR : ∀ c ∈ H, c ^ r = 1 → c ≠ 1 → Subgroup.centralizer ({c} : Set (twistedGroup σ)) ≤ H) :
    invCentGroup σ hσ ≤ H := by
  obtain ⟨m₀, hm₀⟩ := exists_orderOf_eq_prime_SL2 (K := K) hrK2
  have hcard : Nat.card (slLong σ hσ).range = Nat.card (SL(2, fixedField σ)) :=
    Nat.card_congr (MonoidHom.ofInjective (slLong_injective hσ)).toEquiv.symm
  refine sup_le_of_le_sup_of_rclosure (A := (slLong σ hσ).range) (B := (slB σ hσ).range)
    ?_ hXle hXH hBX (by rw [hcard]; exact hrF) ⟨m₀, rfl⟩ ?_ hR
  · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    exact slLong_comm_slB hσ a b
  · rw [orderOf_injective (slB σ hσ) (slB_injective hσ) m₀, hm₀]

end CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator
