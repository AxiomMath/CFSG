module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeKRStrict
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4HeldLift

public section

namespace CFSG.ComponentClassification.GrSLit.GrS4

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.GH74.Uniqueness.Bender

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem autFixed_eq_fixedSubgroup {Q : Type*} [Group Q] (α : MulAut Q) :
    autFixed α = FixedCommutingProduct.fixedSubgroup α := by
  ext x
  exact Iff.rfl

theorem exists_twist
    {K : Subgroup G} {a : G} (e : ↥K ⧸ pPrimeCore 2 ↥K ≃* Blueprint.NativeSporadic.He)
    (haN : a ∈ normalizer (K : Set G)) (haa : a * a = 1)
    (hcard : Nat.card ↥(autFixed (heldQuotConj K ⟨a, haN⟩)) ≠ 15120) :
    ∃ n ∈ K, n * a = a * n ∧ n * n = 1 ∧ a * n ∈ coreActionKernel K ∧
      ∀ j ∈ K, j * a = a * j → j⁻¹ * (n * j * n⁻¹) ∈ oddIn K := by
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  set α := heldQuotConj K ⟨a, haN⟩ with hα
  have hαα : α * α = 1 := by
    rw [hα, ← map_mul, show (⟨a, haN⟩ : ↥(normalizer (K : Set G))) * ⟨a, haN⟩ = 1 from
      Subtype.ext haa, map_one]
  obtain ⟨ν, hνν, hαν⟩ := HeKR.exists_conj_of_card_ne e α hαα
    (by rwa [← autFixed_eq_fixedSubgroup])
  set q : ↥K →* ↥K ⧸ pPrimeCore 2 ↥K := QuotientGroup.mk' (pPrimeCore 2 ↥K) with hq
  have hqa : ∀ (y : G) (hy : y ∈ K),
      q ⟨a * y * a⁻¹, (mem_normalizer_iff.mp haN y).mp hy⟩ = ν * q ⟨y, hy⟩ * ν⁻¹ := by
    intro y hy
    have h1 : α (q ⟨y, hy⟩) = q ⟨a * y * a⁻¹, (mem_normalizer_iff.mp haN y).mp hy⟩ := rfl
    rw [← h1, hαν, MulAut.conj_apply]
  have hqeq : ∀ (x y : G) (hx : x ∈ K) (hy : y ∈ K), q ⟨x, hx⟩ = q ⟨y, hy⟩ →
      x⁻¹ * y ∈ oddIn K := by
    intro x y hx hy h
    exact ⟨_, QuotientGroup.eq.mp h, rfl⟩
  have hqo : ∀ o : ↥K, o ∈ pPrimeCore 2 ↥K → q o = 1 := fun o ho =>
    (QuotientGroup.eq_one_iff o).mpr ho
  obtain ⟨⟨k, hk⟩, hkν⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥K) ν
  have hk1 : k⁻¹ * (a * k * a⁻¹) ∈ oddIn K := by
    refine hqeq k (a * k * a⁻¹) hk ((mem_normalizer_iff.mp haN k).mp hk) ?_
    rw [hqa k hk, hkν]
    group
  obtain ⟨o, ho, hko⟩ := exists_commute_mul_mem (odd_card_map_pPrimeCore K) haa hk1
  obtain ⟨o', ho', rfl⟩ := mem_map.mp ho
  set n₁ : G := k * (o' : G) with hn₁
  have hn₁K : n₁ ∈ K := mul_mem hk o'.2
  have hqn₁ : q ⟨n₁, hn₁K⟩ = ν := by
    have h1 : (⟨n₁, hn₁K⟩ : ↥K) = ⟨k, hk⟩ * o' := rfl
    rw [h1, map_mul, hkν, hqo o' ho', mul_one]
  have hn₁a : n₁ * a = a * n₁ := hko.symm
  set d := Nat.card (pPrimeCore 2 ↥K) with hd
  have hdodd : Odd d := Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hsq : (⟨n₁, hn₁K⟩ : ↥K) * ⟨n₁, hn₁K⟩ ∈ pPrimeCore 2 ↥K := by
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, ← hq, map_mul, hqn₁, hνν]
  have hsqd : ((⟨n₁, hn₁K⟩ : ↥K) * ⟨n₁, hn₁K⟩) ^ d = 1 := by
    have h1 : (⟨_, hsq⟩ : ↥(pPrimeCore 2 ↥K)) ^ Nat.card ↥(pPrimeCore 2 ↥K) = 1 :=
      pow_card_eq_one'
    exact congrArg Subtype.val h1
  set n : G := n₁ ^ d with hn
  have hnK : n ∈ K := pow_mem hn₁K d
  have hna : n * a = a * n := (Commute.pow_left hn₁a d).eq
  have hnn : n * n = 1 := by
    have h1 : ((((⟨n₁, hn₁K⟩ : ↥K) * ⟨n₁, hn₁K⟩) ^ d : ↥K) : G) = 1 := by
      rw [hsqd]
      rfl
    rw [← h1, hn, ← (Commute.refl n₁).mul_pow d]
    rfl
  have hqn : q ⟨n, hnK⟩ = ν := by
    obtain ⟨j, hj⟩ := hdodd
    have h1 : (⟨n, hnK⟩ : ↥K) = ⟨n₁, hn₁K⟩ ^ d := Subtype.ext (by rw [SubgroupClass.coe_pow])
    rw [h1, map_pow, hqn₁, hj, pow_succ, pow_mul, sq, hνν, one_pow, one_mul]
  have hqconj : ∀ (g y : G) (hg : g ∈ K) (hy : y ∈ K),
      q ⟨g * y * g⁻¹, mul_mem (mul_mem hg hy) (inv_mem hg)⟩ = q ⟨g, hg⟩ * q ⟨y, hy⟩ *
        (q ⟨g, hg⟩)⁻¹ := by
    intro g y hg hy
    have h1 : (⟨g * y * g⁻¹, mul_mem (mul_mem hg hy) (inv_mem hg)⟩ : ↥K) =
        ⟨g, hg⟩ * ⟨y, hy⟩ * (⟨g, hg⟩ : ↥K)⁻¹ := rfl
    rw [h1, map_mul, map_mul, map_inv]
  refine ⟨n, hnK, hna, hnn, ⟨mul_mem haN (le_normalizer hnK), fun j hj => ?_⟩, fun j hj hja => ?_⟩
  ·
    have hw : a * j * a⁻¹ ∈ K := (mem_normalizer_iff.mp haN j).mp hj
    have hninv : n⁻¹ ∈ K := inv_mem hnK
    have hy : n⁻¹ * (a * j * a⁻¹) * n⁻¹⁻¹ ∈ K := mul_mem (mul_mem hninv hw) (inv_mem hninv)
    have h1 := hqeq j (n⁻¹ * (a * j * a⁻¹) * n⁻¹⁻¹) hj hy (by
      rw [hqconj n⁻¹ (a * j * a⁻¹) hninv hw, hqa j hj]
      have h2 : q ⟨n⁻¹, hninv⟩ = ν⁻¹ := by
        have h3 : (⟨n⁻¹, hninv⟩ : ↥K) = (⟨n, hnK⟩ : ↥K)⁻¹ := rfl
        rw [h3, map_inv, hqn]
      rw [h2]
      group)
    have h4 : j⁻¹ * (a * n)⁻¹ * j * (a * n) = j⁻¹ * (n⁻¹ * (a * j * a⁻¹) * n⁻¹⁻¹) := by
      simp only [mul_inv_rev, hai, inv_inv]
      group
    rw [h4]
    exact h1
  ·
    have hjj : a * j * a⁻¹ = j := by rw [← hja, mul_inv_cancel_right]
    have hqj : q ⟨j, hj⟩ = ν * q ⟨j, hj⟩ * ν⁻¹ := by
      have h1 := hqa j hj
      have h2 : (⟨a * j * a⁻¹, (mem_normalizer_iff.mp haN j).mp hj⟩ : ↥K) = ⟨j, hj⟩ :=
        Subtype.ext hjj
      rwa [h2] at h1
    refine hqeq j (n * j * n⁻¹) hj (mul_mem (mul_mem hnK hj) (inv_mem hnK)) ?_
    rw [hqconj n j hnK hj, hqn, ← hqj]

end CFSG.ComponentClassification.GrSLit.GrS4
