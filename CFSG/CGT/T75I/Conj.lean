module

public import CFSG.CGT.Timmesfeld75.Sec6Five
public import CFSG.CGT.T75I.HatData

public section

namespace CFSG.CGT.T75I

open CFSG.Open CFSG.CGT.Timmesfeld75

variable {G : Type} [Group G] {T T₁ : Subgroup G}

theorem normIn_le_normalizer' : normIn T₁ T ≤ Subgroup.normalizer (T : Set G) :=
  fun _ hx => (mem_normIn.1 hx).2

theorem hSub_le_normalizer' : hSub T (normIn T₁ T) ≤ Subgroup.normalizer (T : Set G) :=
  hSub_le_normalizer normIn_le_normalizer'

theorem normD_le_hSub_of_ctx (h1 : Sec4NoA) (h63 : Sec63) (hc : Sec6Ctx T T₁ 2 2) {x : G}
    (hx : x ∈ normD T) : x ∈ hSub T (normIn T₁ T) :=
  hc.normD_le_hSub_of_not_a8 h1 h63 (by omega) hx

theorem exists_hSub_conj_of_normD (h1 : Sec4NoA) (h62 : Sec62) (h63 : Sec63)
    (hc : Sec6Ctx T T₁ 2 2) [hnorm : (T.subgroupOf (hSub T (normIn T₁ T))).Normal]
    (hhat : IsHatA 6 (↥(hSub T (normIn T₁ T)) ⧸ T.subgroupOf (hSub T (normIn T₁ T))) ∨
      IsHatA 7 (↥(hSub T (normIn T₁ T)) ⧸ T.subgroupOf (hSub T (normIn T₁ T))))
    {x y : G} (hx : x ∈ normD T) (hxT : x ∉ T) (hy : y ∈ normD T) (hyT : y ∉ T) :
    ∃ h ∈ hSub T (normIn T₁ T), y = h * x * h⁻¹ := by
  classical
  have : Finite G := hc.finite
  have hTab := hc.hy.pair.wc.1
  set H := hSub T (normIn T₁ T) with hH
  have hxH : x ∈ H := normD_le_hSub_of_ctx h1 h63 hc hx
  have hyH : y ∈ H := normD_le_hSub_of_ctx h1 h63 hc hy
  have hxx : x * x = 1 := mul_self_eq_one_of_mem_classD hTab hx.1
  have hyy : y * y = 1 := mul_self_eq_one_of_mem_classD hTab hy.1
  let π : ↥H →* ↥H ⧸ T.subgroupOf H := QuotientGroup.mk' (T.subgroupOf H)
  let x' : ↥H := ⟨x, hxH⟩
  let y' : ↥H := ⟨y, hyH⟩
  have hπ1 : ∀ z : ↥H, π z = 1 → (z : G) ∈ T := fun z hz =>
    Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff z).1 hz)
  have hx1 : π x' ≠ 1 := fun h => hxT (hπ1 x' h)
  have hy1 : π y' ≠ 1 := fun h => hyT (hπ1 y' h)
  have hxx' : π x' * π x' = 1 := by
    rw [← map_mul]
    have : x' * x' = 1 := Subtype.ext hxx
    rw [this, map_one]
  have hyy' : π y' * π y' = 1 := by
    rw [← map_mul]
    have : y' * y' = 1 := Subtype.ext hyy
    rw [this, map_one]
  obtain ⟨k, hk, Z, f, hd⟩ : ∃ k : ℕ, (k = 6 ∨ k = 7) ∧ ∃ (Z : Subgroup (↥H ⧸ T.subgroupOf H))
      (f : (↥H ⧸ T.subgroupOf H) →* alternatingGroup (Fin k)), HatData k Z f := by
    rcases hhat with h | h
    · obtain ⟨-, Z, f, hd⟩ := IsHatA.exists_data h
      exact ⟨6, Or.inl rfl, Z, f, hd⟩
    · obtain ⟨-, Z, f, hd⟩ := IsHatA.exists_data h
      exact ⟨7, Or.inr rfl, Z, f, hd⟩
  obtain ⟨γ, hγ⟩ := hd.exists_conj_of_involutions hk hx1 hxx' hy1 hyy'
  obtain ⟨h₀, rfl⟩ := QuotientGroup.mk_surjective γ
  have hh₀N : (h₀ : G) ∈ Subgroup.normalizer (T : Set G) := hSub_le_normalizer' h₀.2
  have hconj : π (h₀ * x' * h₀⁻¹) = π y' := by
    rw [map_mul, map_mul, map_inv]
    exact hγ
  have hty : ((h₀ * x' * h₀⁻¹ : ↥H) : G)⁻¹ * y ∈ T := by
    have : (h₀ * x' * h₀⁻¹)⁻¹ * y' ∈ T.subgroupOf H := by
      rw [← QuotientGroup.eq]
      exact hconj
    exact Subgroup.mem_subgroupOf.1 this
  set x₂ : G := (h₀ : G) * x * (h₀ : G)⁻¹ with hx₂
  have hx₂' : ((h₀ * x' * h₀⁻¹ : ↥H) : G) = x₂ := rfl
  rw [hx₂'] at hty
  have hx₂D : x₂ ∈ classD T := by
    have := classD_conj hx.1 (h₀ : G)⁻¹
    simpa [hx₂] using this
  have hx₂N : x₂ ∈ Subgroup.normalizer (T : Set G) :=
    (Subgroup.normalizer (T : Set G)).mul_mem
      ((Subgroup.normalizer (T : Set G)).mul_mem hh₀N hx.2)
      ((Subgroup.normalizer (T : Set G)).inv_mem hh₀N)
  have hx₂T : x₂ ∉ T := by
    intro hT'
    apply hxT
    have := conj_mem_of_mem_normalizer ((Subgroup.normalizer (T : Set G)).inv_mem hh₀N) hT'
    simpa [hx₂, mul_assoc] using this
  have hyt : y = x₂ * (x₂⁻¹ * y) := by group
  obtain ⟨s, hsT, hys⟩ := hc.eq_conj_of_mem_coset h62 h63 ⟨hx₂D, hx₂N⟩ hx₂T hy.1 hty hyt
  refine ⟨s⁻¹ * h₀, H.mul_mem (H.inv_mem (left_le_hSub hsT)) h₀.2, ?_⟩
  rw [hys, hx₂]
  group

end CFSG.CGT.T75I
