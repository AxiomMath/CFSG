module

public import CFSG.LocalAnalysis.ComponentClassification.Sp4RecTransport

public noncomputable section

namespace CFSG.ComponentClassification.Sp4Rec

open CFSG Subgroup

variable {M : Type*} [Group M] [Finite M] {x : M} {K K' : Subgroup M}

omit [Finite M] in
theorem le_centralizer_sup' {T : Subgroup M} (h : T ≤ centralizer (K : Set M))
    (h' : T ≤ centralizer (K' : Set M)) : T ≤ centralizer ((K ⊔ K' : Subgroup M) : Set M) := by
  rw [le_centralizer_iff] at h h' ⊢
  exact sup_le h h'

omit [Finite M] in
theorem zpowers_le_centralizer {z : M} (hz : ∀ k ∈ K, z * k = k * z) :
    zpowers z ≤ centralizer (K : Set M) := by
  rw [zpowers_le, mem_centralizer_iff]
  intro k hk
  exact (hz k hk).symm

theorem PairConfig.false_of_order_four (hc : PairConfig M x K K') {z : M} (hz4 : z ^ 4 = 1)
    (hz2 : z ^ 2 ≠ 1) (hzK : ∀ k ∈ K, z * k = k * z) (hzK' : ∀ k ∈ K', z * k = k * z) :
    False := by
  have hord : orderOf z = 2 ^ 2 := orderOf_eq_prime_pow (p := 2) (n := 1) (by simpa using hz2)
    (by simpa using hz4)
  have hT : IsPGroup 2 (zpowers z) := IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hord])
  have hcard := hc.sylow _ hT
    (le_centralizer_sup' (zpowers_le_centralizer hzK) (zpowers_le_centralizer hzK'))
  rw [Nat.card_zpowers, hord] at hcard
  norm_num at hcard

theorem PairConfig.false_of_klein (hc : PairConfig M x K K') {z : M} (hz2 : z ^ 2 = 1)
    (hz1 : z ≠ 1) (hzx : z ≠ x) (hxz : z * x = x * z) (hzK : ∀ k ∈ K, z * k = k * z)
    (hzK' : ∀ k ∈ K', z * k = k * z) : False := by
  classical
  have hx1 : x ≠ 1 := by
    intro h
    have := hc.orderOf_x
    rw [h, orderOf_one] at this
    exact absurd this (by norm_num)
  have hzo : orderOf z = 2 := orderOf_eq_prime hz2 hz1
  have hX : IsPGroup 2 (zpowers x) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, hc.orderOf_x, pow_one])
  have hZ : IsPGroup 2 (zpowers z) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, hzo, pow_one])
  have hc' : ∀ k : ℤ, z * x ^ k * z⁻¹ = x ^ k := fun k => by
    rw [(Commute.zpow_right hxz k).eq, mul_inv_cancel_right]
  have hZX : zpowers z ≤ normalizer ((zpowers x : Subgroup M) : Set M) := by
    rw [zpowers_le, mem_normalizer_iff]
    intro g
    rw [mem_zpowers_iff, mem_zpowers_iff]
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨k, (hc' k).symm⟩
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_⟩
      have h2 : z * g * z⁻¹ = z * x ^ k * z⁻¹ := by rw [← hk, hc' k]
      exact (mul_left_cancel (mul_right_cancel h2)).symm
  set T := zpowers x ⊔ zpowers z with hTdef
  have hT : IsPGroup 2 T := IsPGroup.to_sup_of_normal_left' hX hZ hZX
  have hxK : ∀ k ∈ K, x * k = k * x := fun k hk =>
    (mem_centralizer_singleton_iff.mp (hc.K_le hk)).symm
  have hxK' : ∀ k ∈ K', x * k = k * x := fun k hk =>
    (mem_centralizer_singleton_iff.mp (hc.K'_le hk)).symm
  have hTC : T ≤ centralizer ((K ⊔ K' : Subgroup M) : Set M) :=
    sup_le (le_centralizer_sup' (zpowers_le_centralizer hxK) (zpowers_le_centralizer hxK'))
      (le_centralizer_sup' (zpowers_le_centralizer hzK) (zpowers_le_centralizer hzK'))
  have hcard := hc.sylow T hT hTC
  have : Fintype T := Fintype.ofFinite T
  have hxT : x ∈ T := mem_sup_left (mem_zpowers x)
  have hzT : z ∈ T := mem_sup_right (mem_zpowers z)
  have h3 : ({1, ⟨x, hxT⟩, ⟨z, hzT⟩} : Finset T).card = 3 := by
    rw [Finset.card_eq_three]
    refine ⟨1, ⟨x, hxT⟩, ⟨z, hzT⟩, ?_, ?_, ?_, rfl⟩
    · intro h
      exact hx1 (congrArg Subtype.val h).symm
    · intro h
      exact hz1 (congrArg Subtype.val h).symm
    · intro h
      exact hzx (congrArg Subtype.val h).symm
  have h4 := Finset.card_le_univ ({1, ⟨x, hxT⟩, ⟨z, hzT⟩} : Finset T)
  rw [h3, ← Nat.card_eq_fintype_card] at h4
  omega

end CFSG.ComponentClassification.Sp4Rec
