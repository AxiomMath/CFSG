module

public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
public import CFSG.GH74.GLS.Bg.Local.Transfer1515

public section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup CFSG.ABGLocalTools

variable {X : Type*} [Group X] [Finite X]

theorem isSylowIn_iff_isSylowOf {P K : Subgroup X} :
    CFSG.GH74.GLS.Bg.Thompson.IsSylowIn 2 P K ↔ IsSylowOf 2 P K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [isSylowOf_iff]
  rfl

omit [Finite X] in
theorem exists_isSylowOf_le {K B : Subgroup X} (hBK : B ≤ K) (hB : IsPGroup 2 B) :
    ∃ P : Subgroup X, IsSylowOf 2 P K ∧ B ≤ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := (hB.comap_of_injective K.subtype K.subtype_injective :
    IsPGroup 2 (B.subgroupOf K)).exists_le_sylow
  exact ⟨(S : Subgroup ↥K).map K.subtype, ⟨S, rfl⟩, fun b hb => ⟨⟨b, hBK hb⟩, hS hb, rfl⟩⟩

theorem IsSylowOf.card_le {P K B : Subgroup X} (hP : IsSylowOf 2 P K) (hBK : B ≤ K)
    (hB : IsPGroup 2 B) : Nat.card B ≤ Nat.card P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P', hP', hBP'⟩ := exists_isSylowOf_le hBK hB
  rw [hP.card_eq, ← hP'.card_eq]
  exact Subgroup.card_le_of_le hBP'

theorem IsSylowOf.exists_conj_le {P K B : Subgroup X} (hP : IsSylowOf 2 P K) (hBK : B ≤ K)
    (hB : IsPGroup 2 B) : ∃ k ∈ K, ∀ x ∈ B, k⁻¹ * x * k ∈ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P', hP', hBP'⟩ := exists_isSylowOf_le hBK hB
  obtain ⟨k, hk, hk'⟩ := hP.exists_mem_conj hP'
  exact ⟨k, hk, fun x hx => (hk' x).mp (hBP' hx)⟩

theorem isPGroup_zpowers_of_pow {c : X} {n : ℕ} (hcn : c ^ 2 ^ n = 1) :
    IsPGroup 2 (zpowers c) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [IsPGroup.iff_card, Nat.card_zpowers]
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hcn)
  exact ⟨k, hk⟩

theorem IsSylowOf.mem_of_central {P K : Subgroup X} (hP : IsSylowOf 2 P K) {c : X} (hcK : c ∈ K)
    (hc : ∀ k ∈ K, k * c = c * k) {n : ℕ} (hcn : c ^ 2 ^ n = 1) : c ∈ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPK : P ≤ K := hP.le
  have hcN : zpowers c ≤ normalizer (P : Set X) := by
    rw [zpowers_le, mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rw [← hc x (hPK hx), mul_inv_cancel_right]
      exact hx
    · intro hx
      have hxK : x ∈ K := by
        have h1 : c * x * c⁻¹ ∈ K := hPK hx
        have h2 : x = c⁻¹ * (c * x * c⁻¹) * c := by group
        rw [h2]
        exact mul_mem (mul_mem (inv_mem hcK) h1) hcK
      rwa [← hc x hxK, mul_inv_cancel_right] at hx
  have hsup : IsPGroup 2 ↥(P ⊔ zpowers c) :=
    IsPGroup.to_sup_of_normal_left' hP.isPGroup (isPGroup_zpowers_of_pow hcn) hcN
  have hle : P ⊔ zpowers c ≤ K := sup_le hPK (zpowers_le.mpr hcK)
  have heq := hP.eq_of_le le_sup_left hle hsup
  rw [← heq]
  exact mem_sup_right (mem_zpowers c)

omit [Finite X] in
theorem eq_one_of_two_pow_of_odd {N : Subgroup X} (hN : Odd (Nat.card N)) {x : X} (hxN : x ∈ N)
    {n : ℕ} (hxn : x ^ 2 ^ n = 1) : x = 1 := by
  have h1 : orderOf x ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hxn
  have h2 : orderOf x ∣ Nat.card N := by
    rw [← Subgroup.orderOf_mk x hxN]
    exact orderOf_dvd_natCard _
  have hcop : Nat.Coprime (2 ^ n) (Nat.card N) :=
    Nat.Coprime.pow_left n (Nat.coprime_two_left.mpr hN)
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hcop) h2)

theorem card_le_two_mul_inf {R Q : Subgroup X} {c : X} (hcQ : ∀ q ∈ Q, c⁻¹ * q * c ∈ Q)
    (hR : ∀ r ∈ R, r ∈ Q ∨ r * c⁻¹ ∈ Q) : Nat.card R ≤ 2 * Nat.card ↥(R ⊓ Q) := by
  classical
  by_cases hall : ∀ r ∈ R, r ∈ Q
  · have : R ⊓ Q = R := inf_eq_left.mpr hall
    rw [this]
    omega
  · push Not at hall
    obtain ⟨r₀, hr₀R, hr₀Q⟩ := hall
    have hr₀c : r₀ * c⁻¹ ∈ Q := (hR r₀ hr₀R).resolve_left hr₀Q
    let φ : ↥R → ↥(R ⊓ Q) ⊕ ↥(R ⊓ Q) := fun r =>
      if hr : (r : X) ∈ Q then Sum.inl ⟨r, mem_inf.mpr ⟨r.2, hr⟩⟩
      else Sum.inr ⟨r₀⁻¹ * r, mem_inf.mpr ⟨mul_mem (inv_mem hr₀R) r.2, by
        have hrc : (r : X) * c⁻¹ ∈ Q := (hR r r.2).resolve_left hr
        have h1 : r₀⁻¹ * r = c⁻¹ * ((r₀ * c⁻¹)⁻¹ * ((r : X) * c⁻¹)) * c := by group
        rw [h1]
        exact hcQ _ (mul_mem (inv_mem hr₀c) hrc)⟩⟩
    have hφ : Function.Injective φ := by
      intro a b hab
      by_cases ha : (a : X) ∈ Q <;> by_cases hb : (b : X) ∈ Q <;>
        simp only [φ, ha, hb, dite_true, dite_false, Sum.inl.injEq, Sum.inr.injEq,
          reduceCtorEq] at hab
      · exact Subtype.ext (congrArg (fun w : ↥(R ⊓ Q) => (w : X)) hab)
      · exact Subtype.ext (mul_left_cancel (congrArg (fun w : ↥(R ⊓ Q) => (w : X)) hab))
    have h1 := Nat.card_le_card_of_injective φ hφ
    rw [Nat.card_sum] at h1
    omega

end CFSG.ComponentClassification.HarrisLit.T1
