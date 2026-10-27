module

public import CFSG.CGT.Timmesfeld75.Sec6Five

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open

variable {G : Type} [Group G] {T T₁ : Subgroup G} {n m : ℕ}

theorem Sec6Ctx.one_le_m (hc : Sec6Ctx T T₁ n m) : 1 ≤ m := by
  by_contra h
  have hm0 : m = 0 := by omega
  have hT := hc.hT
  rw [hm0] at hT
  simp only [pow_zero, one_pow] at hT
  have := hc.hy.card
  omega

theorem conjSubgroup_conj_conj (k y : G) (T : Subgroup G) :
    conjSubgroup (k⁻¹ * y * k) T = conjSubgroup k⁻¹ (conjSubgroup y (conjSubgroup k T)) := by
  rw [conjSubgroup_conjSubgroup, conjSubgroup_conjSubgroup, mul_assoc]

theorem mem_normalizer_conj_iff {k y : G} {T : Subgroup G} :
    y ∈ Subgroup.normalizer (conjSubgroup k T : Set G) ↔
      k⁻¹ * y * k ∈ Subgroup.normalizer (T : Set G) := by
  rw [mem_normalizer_iff_conjSubgroup_eq, mem_normalizer_iff_conjSubgroup_eq,
    conjSubgroup_conj_conj]
  constructor
  · intro h
    rw [h, conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one]
  · intro h
    have h' := congrArg (conjSubgroup k) h
    rw [conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one] at h'
    exact h'

theorem mem_normD_conj {k y : G} (hy : y ∈ classD T)
    (hyN : y ∈ Subgroup.normalizer (conjSubgroup k T : Set G)) : k⁻¹ * y * k ∈ normD T :=
  ⟨classD_conj hy k, mem_normalizer_conj_iff.1 hyN⟩

theorem Sec6Ctx.eq_conj_of_mem_coset_conj (h62 : Sec62) (h63 : Sec63) (hc : Sec6Ctx T T₁ n m)
    {k y t : G} (hy : y ∈ classD T) (hyN : y ∈ Subgroup.normalizer (conjSubgroup k T : Set G))
    (hyS : y ∉ conjSubgroup k T) (ht : t ∈ conjSubgroup k T) (hyt : y * t ∈ classD T) :
    ∃ s ∈ conjSubgroup k T, y * t = s⁻¹ * y * s := by
  have hy' := mem_normD_conj hy hyN
  have hyT : k⁻¹ * y * k ∉ T := fun h => hyS (mem_conjSubgroup.2 h)
  have ht' : k⁻¹ * t * k ∈ T := mem_conjSubgroup.1 ht
  have hyt' : k⁻¹ * (y * t) * k ∈ classD T := classD_conj hyt k
  obtain ⟨s', hs', hs⟩ := hc.eq_conj_of_mem_coset h62 h63 hy' hyT hyt' ht'
    (by group)
  refine ⟨k * s' * k⁻¹, mem_conjSubgroup.2 (by simpa [mul_assoc] using hs'), ?_⟩
  have e : y * t = k * (k⁻¹ * (y * t) * k) * k⁻¹ := by group
  rw [e, hs]
  group

theorem card_inf_centralizer_conj (k y : G) (T : Subgroup G) :
    Nat.card ↥(conjSubgroup k T ⊓ Subgroup.centralizer ({y} : Set G)) =
      Nat.card ↥(T ⊓ Subgroup.centralizer ({k⁻¹ * y * k} : Set G)) := by
  have e : conjSubgroup k T ⊓ Subgroup.centralizer ({y} : Set G) =
      conjSubgroup k (T ⊓ Subgroup.centralizer ({k⁻¹ * y * k} : Set G)) := by
    rw [conjSubgroup_inf_eq_inf, ← centralizer_conj_singleton]
    congr 3
    group
  rw [e, card_conjSubgroup]

theorem Sec6Ctx.card_centralizer_conj (h63 : Sec63) (hc : Sec6Ctx T T₁ n m) {k y : G}
    (hy : y ∈ classD T) (hyN : y ∈ Subgroup.normalizer (conjSubgroup k T : Set G))
    (hyS : y ∉ conjSubgroup k T) :
    Nat.card ↥(conjSubgroup k T ⊓ Subgroup.centralizer ({y} : Set G)) =
        Nat.card ↥(normIn T T₁) ∨
      (Nat.card T = 16 ∧ Nat.card ↥(normIn T T₁) = 8 ∧
        Nat.card ↥(conjSubgroup k T ⊓ Subgroup.centralizer ({y} : Set G)) = 4) := by
  have hyT : k⁻¹ * y * k ∉ T := fun h => hyS (mem_conjSubgroup.2 h)
  rw [card_inf_centralizer_conj]
  exact h63 G T T₁ n m hc _ (mem_normD_conj hy hyN) hyT

end CFSG.CGT.Timmesfeld75
