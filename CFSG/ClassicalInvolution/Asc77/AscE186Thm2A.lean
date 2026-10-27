module

public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.ClassicalInvolution.Asc77.AscE186

open scoped commutatorElement

variable {G : Type*} [Group G] [Finite G]

theorem perfect_centralizes_of_centralizes_cent {K : Subgroup G} {z : G}
    (hK : Group.IsPerfect ↥K) (hzK : z ∈ K) (hzc : ∀ k ∈ K, k * z = z * k) :
    ∀ (n : ℕ) (Q : Subgroup G), Nat.card Q = n → IsPGroup 2 ↥Q → z ∈ Q →
      (∀ k ∈ K, ∀ x ∈ Q, k * x * k⁻¹ ∈ Q) →
      (∀ k ∈ K, ∀ x ∈ Q, x * z = z * x → k * x = x * k) →
      ∀ k ∈ K, ∀ x ∈ Q, k * x = x * k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro Q hn hQ2 hzQ hKQ hcent
  by_cases hC : Q ≤ Subgroup.centralizer ({z} : Set G)
  · intro k hk x hx
    exact hcent k hk x hx (Subgroup.mem_centralizer_singleton_iff.mp (hC hx))
  set Q₁ : Subgroup G := Q ⊓ Subgroup.centralizer ({z} : Set G) with hQ₁
  have hQ₁Q : Q₁ ≤ Q := inf_le_left
  have hzQ₁ : z ∈ Q₁ := ⟨hzQ, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have hKQ₁ : ∀ k ∈ K, ∀ c ∈ Q₁, k * c * k⁻¹ ∈ Q₁ := by
    intro k hk c hc
    refine ⟨hKQ k hk c (hQ₁Q hc), Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have h1 : c * z = z * c := Subgroup.mem_centralizer_singleton_iff.mp hc.2
    have h2 : k * z = z * k := hzc k hk
    calc k * c * k⁻¹ * z = k * c * (k⁻¹ * z) := by group
      _ = k * c * (z * k⁻¹) := by
          congr 1
          have : k⁻¹ * z = z * k⁻¹ := by
            have := congrArg (fun w => k⁻¹ * w * k⁻¹) h2.symm
            simpa [mul_assoc] using this
          exact this
      _ = k * (c * z) * k⁻¹ := by group
      _ = k * (z * c) * k⁻¹ := by rw [h1]
      _ = (k * z) * c * k⁻¹ := by group
      _ = (z * k) * c * k⁻¹ := by rw [h2]
      _ = z * (k * c * k⁻¹) := by group
  have hgrow : ∃ x ∈ Q, x ∉ Q₁ ∧ ∀ c ∈ Q₁, x * c * x⁻¹ ∈ Q₁ := by
    have : Group.IsNilpotent ↥Q := hQ2.isNilpotent
    have hH : Q₁.subgroupOf Q ≠ ⊤ := by
      intro h
      apply hC
      intro x hx
      have : (⟨x, hx⟩ : ↥Q) ∈ Q₁.subgroupOf Q := by
        rw [h]
        exact Subgroup.mem_top _
      exact (Subgroup.mem_subgroupOf.mp this).2
    have hlt := Group.normalizerCondition_of_isNilpotent (Q₁.subgroupOf Q)
      (lt_top_iff_ne_top.mpr hH)
    obtain ⟨y, hy, hyn⟩ := IsConcreteLE.exists_of_lt hlt
    refine ⟨(y : G), y.2, fun h => hyn (Subgroup.mem_subgroupOf.mpr h), fun c hc => ?_⟩
    have hcQ : c ∈ Q := hQ₁Q hc
    have h1 := (Subgroup.mem_normalizer_iff.mp hy ⟨c, hcQ⟩).mp (Subgroup.mem_subgroupOf.mpr hc)
    exact Subgroup.mem_subgroupOf.mp h1
  obtain ⟨x, hxQ, hxQ₁, hxn⟩ := hgrow
  by_cases hM : Q ≤ Subgroup.normalizer (Q₁ : Set G)
  ·
    have hcomm : ⁅K, Q⁆ ≤ Subgroup.centralizer (K : Set G) := by
      rw [Subgroup.commutator_le]
      intro k hk q hq
      have hzq : q⁻¹ * z * q ∈ Q₁ := by
        have := (Subgroup.mem_normalizer_iff.mp (hM (Q.inv_mem hq)) z).mp hzQ₁
        simpa using this
      have hzqc : q⁻¹ * z * q * z = z * (q⁻¹ * z * q) :=
        Subgroup.mem_centralizer_singleton_iff.mp hzq.2
      have hkq : k * (q⁻¹ * z * q) = (q⁻¹ * z * q) * k :=
        hcent k hk _ hzq.1 hzqc
      have hkz : k * z * k⁻¹ = z := by
        rw [hzc k hk]
        group
      have hkc : k * (q⁻¹ * z * q) * k⁻¹ = q⁻¹ * z * q := by
        rw [hkq]
        group
      have hxz : (k * q * k⁻¹ * q⁻¹) * z = z * (k * q * k⁻¹ * q⁻¹) := by
        calc (k * q * k⁻¹ * q⁻¹) * z
            = k * q * k⁻¹ * (q⁻¹ * z * q) * q⁻¹ := by group
          _ = k * q * k⁻¹ * (k * (q⁻¹ * z * q) * k⁻¹) * q⁻¹ := by rw [hkc]
          _ = k * q * (q⁻¹ * z * q) * (k⁻¹ * q⁻¹) := by group
          _ = k * z * (q * k⁻¹ * q⁻¹) := by group
          _ = (k * z * k⁻¹) * k * (q * k⁻¹ * q⁻¹) := by group
          _ = z * (k * q * k⁻¹ * q⁻¹) := by rw [hkz]; group
      have hxQ' : k * q * k⁻¹ * q⁻¹ ∈ Q :=
        Q.mul_mem (hKQ k hk q hq) (Q.inv_mem hq)
      rw [Subgroup.mem_centralizer_iff]
      intro k' hk'
      have := hcent k' hk' _ hxQ' hxz
      rw [commutatorElement_def]
      exact this
    have h1 : ⁅⁅K, Q⁆, K⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hcomm
    have h2 : ⁅⁅Q, K⁆, K⁆ = ⊥ := by
      rw [Subgroup.commutator_comm Q K]
      exact h1
    have h3 : ⁅⁅K, K⁆, Q⁆ = ⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
    rw [Subgroup.isPerfect_iff.mp hK] at h3
    intro k hk q hq
    have h4 : ⁅k, q⁆ ∈ (⊥ : Subgroup G) := by
      rw [← h3]
      exact Subgroup.commutator_mem_commutator hk hq
    rw [Subgroup.mem_bot, commutatorElement_def] at h4
    calc k * q = k * q * k⁻¹ * q⁻¹ * q * k := by group
      _ = q * k := by rw [h4]; group
  ·
    exfalso
    set M : Subgroup G := Q ⊓ Subgroup.normalizer (Q₁ : Set G) with hMdef
    have hMQ : M ≤ Q := inf_le_left
    have hMne : M ≠ Q := fun h => hM (by rw [← h]; exact inf_le_right)
    have hMlt : Nat.card M < n := by
      rw [← hn]
      exact lt_of_le_of_ne (Subgroup.card_le_of_le hMQ)
        (fun h => hMne (Subgroup.eq_of_le_of_card_ge hMQ h.ge))
    have hxn' : x ∈ Subgroup.normalizer (Q₁ : Set G) :=
      Subgroup.mem_normalizer_fintype fun c hc => hxn c hc
    have hxM : x ∈ M := ⟨hxQ, hxn'⟩
    have hzM : z ∈ M := ⟨hzQ, Subgroup.le_normalizer hzQ₁⟩
    have hKM : ∀ k ∈ K, ∀ y ∈ M, k * y * k⁻¹ ∈ M := by
      intro k hk y hy
      refine ⟨hKQ k hk y hy.1, Subgroup.mem_normalizer_fintype fun c hc => ?_⟩
      have hc' : k⁻¹ * c * k⁻¹⁻¹ ∈ Q₁ := hKQ₁ k⁻¹ (K.inv_mem hk) c hc
      have h1 := (Subgroup.mem_normalizer_iff.mp hy.2 _).mp hc'
      have h2 := hKQ₁ k hk _ h1
      have : k * (y * (k⁻¹ * c * k⁻¹⁻¹) * y⁻¹) * k⁻¹ = (k * y * k⁻¹) * c * (k * y * k⁻¹)⁻¹ := by
        group
      rw [this] at h2
      exact h2
    have hcM : ∀ k ∈ K, ∀ y ∈ M, y * z = z * y → k * y = y * k := fun k hk y hy hyz =>
      hcent k hk y (hMQ hy) hyz
    have hres := ih (Nat.card M) hMlt M rfl (hQ2.to_le hMQ) hzM hKM hcM
    have hxz : x * z = z * x := (hres z hzK x hxM).symm
    exact hxQ₁ ⟨hxQ, Subgroup.mem_centralizer_singleton_iff.mpr hxz⟩

end CFSG.ClassicalInvolution.Asc77.AscE186
