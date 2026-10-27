module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOrbitContainmentTransfer

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

theorem le_normalizer_of_conj {G : Type*} [Group G] {N C : Subgroup G}
    (hNC : ∀ y ∈ N, ∀ w ∈ C, y * w * y⁻¹ ∈ C) : N ≤ normalizer (C : Set G) := by
  intro y hy
  rw [mem_normalizer_iff]
  intro w
  refine ⟨hNC y hy w, fun hw => ?_⟩
  have := hNC y⁻¹ (inv_mem hy) _ hw
  rwa [show y⁻¹ * (y * w * y⁻¹) * y⁻¹⁻¹ = w by group] at this

namespace Eight

theorem card_conjugate_eq {G₁ : Type*} [Group G₁] (A : Subgroup G₁) (g : G₁) :
    Nat.card (conjugate A g) = Nat.card A :=
  card_map_of_injective (MulAut.conj g⁻¹).injective

theorem mem_normalizer_of_conj_mem {G : Type*} [Group G] [Finite G] {C : Subgroup G} {s : G}
    (hs : ∀ c ∈ C, s⁻¹ * c * s ∈ C) : s ∈ normalizer (C : Set G) := by
  apply mem_normalizer_of_conjugate_eq
  have hle : conjugate C s ≤ C := by
    intro y hy
    rw [mem_conjugate_iff] at hy
    have := hs _ hy
    rwa [show s⁻¹ * (s * y * s⁻¹) * s = y by group] at this
  exact eq_of_le_of_card_ge hle (card_conjugate_eq C s).ge

theorem card_le_two_mul_card_inf {G : Type*} [Group G] [Finite G] {A K : Subgroup G}
    (hAK : ∀ y ∈ A, ∀ y' ∈ A, y ∉ K → y' ∉ K → y⁻¹ * y' ∈ K) :
    Nat.card A ≤ 2 * Nat.card ↥(A ⊓ K) := by
  classical
  by_cases hex : ∃ y₀ ∈ A, y₀ ∉ K
  · obtain ⟨y₀, hy₀, hy₀K⟩ := hex
    let f : ↥A → Bool × ↥(A ⊓ K) := fun y =>
      if hy : (y : G) ∈ K then (true, ⟨y, Subgroup.mem_inf.mpr ⟨y.2, hy⟩⟩)
      else (false, ⟨y₀⁻¹ * y, Subgroup.mem_inf.mpr
        ⟨mul_mem (inv_mem hy₀) y.2, hAK y₀ hy₀ y y.2 hy₀K hy⟩⟩)
    have hf : Function.Injective f := by
      intro u v huv
      simp only [f] at huv
      by_cases hu : (u : G) ∈ K <;> by_cases hv : (v : G) ∈ K <;>
        simp only [hu, hv, dite_true, dite_false, Prod.mk.injEq, Bool.false_eq_true,
          Bool.true_eq_false, false_and] at huv
      · have h1 := congrArg Subtype.val huv.2
        exact Subtype.ext h1
      · have h1 := congrArg Subtype.val huv.2
        exact Subtype.ext (mul_left_cancel h1)
    have := Nat.card_le_card_of_injective f hf
    rwa [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at this
  · push Not at hex
    calc Nat.card A ≤ Nat.card ↥(A ⊓ K) := card_le_of_le (le_inf le_rfl hex)
      _ ≤ 2 * Nat.card ↥(A ⊓ K) := by omega

theorem comm_of_mul_self {G : Type*} [Group G] {A : Subgroup G} (hA : ∀ y ∈ A, y * y = 1)
    {y y' : G} (hy : y ∈ A) (hy' : y' ∈ A) : y * y' = y' * y := by
  rw [(inv_eq_of_mul_eq_one_right (hA _ (mul_mem hy hy'))).symm, mul_inv_rev,
    inv_eq_of_mul_eq_one_right (hA _ hy), inv_eq_of_mul_eq_one_right (hA _ hy')]

theorem exists_mem_normalizer_not_mem {G : Type*} [Group G] [Finite G] {T N : Subgroup G}
    (hT : IsPGroup 2 T) (hNT : N ≤ T) (hne : N ≠ T) :
    ∃ t ∈ T, t ∉ N ∧ ∀ n ∈ N, t * n * t⁻¹ ∈ N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent ↥T := hT.isNilpotent
  have hNC := Group.normalizerCondition_of_isNilpotent (G := ↥T)
  have hlt : N.subgroupOf T < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun h1 => hne (le_antisymm hNT fun t ht => ?_)
    have : (⟨t, ht⟩ : ↥T) ∈ N.subgroupOf T := h1 ▸ mem_top _
    exact this
  obtain ⟨t, htN, htN'⟩ := IsConcreteLE.exists_of_lt (hNC _ hlt)
  refine ⟨t, t.2, htN', fun n hn => ?_⟩
  have := (mem_normalizer_iff.mp htN ⟨n, hNT hn⟩).mp hn
  exact this

end Eight

end CFSG.ComponentClassification.GSThmB
