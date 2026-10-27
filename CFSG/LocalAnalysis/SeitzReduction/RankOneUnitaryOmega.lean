module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryClosure

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup
open scoped commutatorElement

theorem exists_normalizer_not_mem_of_not_isSylow {D : Type*} [Group D] [Finite D]
    {S : Subgroup D} (hS : IsPGroup 2 S) (hns : ¬ ∃ P : Sylow 2 D, (P : Subgroup D) = S) :
    ∃ z ∈ normalizer (S : Set D), z ∉ S ∧ ∃ P : Subgroup D, IsPGroup 2 P ∧ S ≤ P ∧ z ∈ P := by
  classical
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hSQ⟩ := hS.exists_le_sylow
  have hlt : S < Q := lt_of_le_of_ne hSQ fun h => hns ⟨Q, h.symm⟩
  have := Q.isPGroup'.isNilpotent
  have htop : S.subgroupOf Q < ⊤ :=
    lt_top_iff_ne_top.mpr fun h => hlt.ne (le_antisymm hlt.le (subgroupOf_eq_top.mp h))
  obtain ⟨z, hz, hzS⟩ :=
    IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ htop)
  refine ⟨z, mem_normalizer_of_forall_inv_mul_mul_mem fun x hx => ?_,
    fun h => hzS (mem_subgroupOf.mpr h), Q, Q.isPGroup', hSQ, z.2⟩
  have h1 := (mem_normalizer_iff''.mp hz ⟨x, hSQ hx⟩).mp (mem_subgroupOf.mpr hx)
  rw [mem_subgroupOf] at h1
  simpa using h1

namespace U3Start

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}

theorem szA₁_eq_commutator_sup_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f) :
    szA₁ (szT₁ L T) = ⁅szT₁ L T ⊔ R₂, szT₁ L T ⊔ R₂⁆ := by
  obtain ⟨-, -, hA₁, -⟩ := h.facts_of_card_sylow hS2
  apply le_antisymm
  · rw [hA₁]
    exact commutator_mono le_sup_left le_sup_left
  · rw [commutator_le]
    intro g₁ hg₁ g₂ hg₂
    obtain ⟨y₁, hy₁, r₁, hr₁, rfl⟩ := hR.mem_sup_iff.mp hg₁
    obtain ⟨y₂, hy₂, r₂, hr₂, rfl⟩ := hR.mem_sup_iff.mp hg₂
    have c1 : r₁ * y₂ = y₂ * r₁ := (hR.commT₁ y₂ hy₂ r₁ hr₁).symm
    have c2 : r₂ * y₁⁻¹ = y₁⁻¹ * r₂ := (hR.commT₁ _ (inv_mem hy₁) r₂ hr₂).symm
    have c3 : r₁ * r₂ * r₁⁻¹ = r₂ := by rw [hR.comm _ hr₁ _ hr₂, mul_inv_cancel_right]
    have e : ⁅y₁ * r₁, y₂ * r₂⁆ = ⁅y₁, y₂⁆ := by
      calc ⁅y₁ * r₁, y₂ * r₂⁆ = y₁ * (r₁ * y₂) * r₂ * r₁⁻¹ * y₁⁻¹ * r₂⁻¹ * y₂⁻¹ := by
            rw [commutatorElement_def]; group
        _ = y₁ * y₂ * (r₁ * r₂ * r₁⁻¹) * y₁⁻¹ * r₂⁻¹ * y₂⁻¹ := by rw [c1]; group
        _ = y₁ * y₂ * (r₂ * y₁⁻¹) * r₂⁻¹ * y₂⁻¹ := by rw [c3]; group
        _ = y₁ * y₂ * y₁⁻¹ * y₂⁻¹ := by rw [c2]; group
        _ = ⁅y₁, y₂⁆ := (commutatorElement_def _ _).symm
    rw [e, hA₁]
    exact commutator_mem_commutator hy₁ hy₂

section Certificates

theorem mem_normalizer_szA_of_conj_mem_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f) (hc : ¬ ∀ r ∈ R₂, t * r * t⁻¹ = r⁻¹) {y : G}
    (hyR : y ∈ normalizer (szR (szT₁ L T) R₂ t : Set G))
    (hyA : y ∈ normalizer (szA₁ (szT₁ L T) : Set G)) (hyt : y * t * y⁻¹ ∈ R₂ ⊔ zpowers t) :
    y ∈ normalizer (szA L T t : Set G) := by
  obtain ⟨-, -, -, hNR₁⟩ := h.char_of_card_sylow hS2 hR
  obtain ⟨-, -, -, -, -, hTH⟩ := h.s₁_facts_of_card_sylow hS2 hR
  obtain ⟨htT, -⟩ := h.start_of_card_sylow hS2
  have hyH : y ∈ normalizer ((szT₁ L T ⊔ R₂ : Subgroup G) : Set G) := (mem_inf.mp (hNR₁ hyR)).1
  have hzN : zpowers t ≤ normalizer (R₂ : Set G) := zpowers_le.mpr hR.t_mem_normalizer
  have hyt' : y * t * y⁻¹ ∈ ((R₂ ⊔ zpowers t : Subgroup G) : Set G) := hyt
  rw [coe_mul_of_right_le_normalizer_left _ _ hzN] at hyt'
  obtain ⟨r, hr, z, hz, hrz⟩ := Set.mem_mul.mp hyt'
  have hytA : y * t * y⁻¹ ∈ szA L T t := by
    rcases mem_zpowers_involution_eq_one_or_eq hR.t_sq hz with hz1 | hz1
    · exfalso
      rw [hz1, mul_one] at hrz
      have h1 : y⁻¹ * (y * t * y⁻¹) * y ∈ szT₁ L T ⊔ R₂ :=
        (mem_normalizer_iff''.mp hyH _).mp (hrz ▸ mem_sup_right hr)
      rw [show y⁻¹ * (y * t * y⁻¹) * y = t by group] at h1
      exact h.not_mem_szT₁_of_card_sylow hS2 (hTH ⟨htT, h1⟩)
    · rw [hz1] at hrz
      have h2 : (r * t) ^ 2 = 1 := by
        rw [hrz, show (y * t * y⁻¹) ^ 2 = y * t ^ 2 * y⁻¹ by rw [sq, sq]; group, hR.t_sq,
          mul_one, mul_inv_cancel]
      rw [← hrz]
      exact mul_mem (mem_sup_left (hR.mem_szA_of_sq_eq_one hc hr h2))
        (mem_sup_right (mem_zpowers t))
  have key : ∀ x ∈ szA L T t, y⁻¹⁻¹ * x * y⁻¹ ∈ szA L T t := by
    intro x hx
    rw [inv_inv]
    have hle : szA L T t ≤ (szA L T t).comap (MulAut.conj y).toMonoidHom := by
      refine sup_le (fun a ha => ?_) (zpowers_le.mpr ?_)
      · rw [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        exact mem_sup_left ((mem_normalizer_iff.mp hyA a).mp ha)
      · rw [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        exact hytA
    have := hle hx
    rwa [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
  have := mem_normalizer_of_forall_inv_mul_mul_mem key
  simpa using inv_mem this

theorem weakClosed_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f) :
    ∀ k ∈ normalizer (szA₁ (szT₁ L T) : Set G),
      (∀ r ∈ szR (szT₁ L T) R₂ t, k⁻¹ * r * k ∈ T ⊔ R₂) →
        ∀ r ∈ szR (szT₁ L T) R₂ t, k⁻¹ * r * k ∈ szR (szT₁ L T) R₂ t := by
  by_cases hcyc : ∃ b ∈ T, ∀ s ∈ T, ∃ k : ℤ, (b ^ k)⁻¹ * s ∈ szT₁ L T
  · intro k hk hkS r hr
    obtain ⟨hR₁, -⟩ := h.s₁_facts_of_card_sylow hS2 hR
    refine h.mem_szR_of_sq_mem_of_card_sylow hS2 hR hcyc (hkS r hr) ?_
    have hr2 : r ^ 2 ∈ szA₁ (szT₁ L T) := by
      rw [hR₁] at hr
      exact h.sq_mem_szA₁_of_mem_u3R₁_of_card_sylow hS2 hr
    rw [show (k⁻¹ * r * k) ^ 2 = k⁻¹ * r ^ 2 * k by rw [sq, sq]; group]
    exact mem_sup_left (szA₁_le _ ((mem_normalizer_iff''.mp hk _).mp hr2))
  · obtain ⟨v, hvT, hv2, hvS⟩ := u3SplitInput G L f t T h hS2 hcyc
    exact h.weakClosed_of_outer_of_card_sylow hS2 hR hvT hv2 hvS

theorem conj_not_mem_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f) (hc : ¬ ∀ r ∈ R₂, t * r * t⁻¹ = r⁻¹) {x : G}
    (hxR : x ∈ normalizer (szR (szT₁ L T) R₂ t : Set G))
    (hxA : x ∈ normalizer (szA₁ (szT₁ L T) : Set G)) (hxS : x ∉ T ⊔ R₂) {P : Subgroup G}
    (hP : IsPGroup 2 P) (hSP : T ⊔ R₂ ≤ P) (hxP : x ∈ P) :
    x * t * x⁻¹ ∉ R₂ ⊔ zpowers t := by
  intro hxt
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, -, -, hsyl⟩ := h.u3R2_canonical_of_card_sylow hS2 hR
  have hxNA := h.mem_normalizer_szA_of_conj_mem_of_card_sylow hS2 hR hc hxR hxA hxt
  have heq := hsyl.eq_of_le (le_sup_left : T ⊔ R₂ ≤ (T ⊔ R₂) ⊔ zpowers x)
    (sup_le hsyl.le (zpowers_le.mpr hxNA)) (hP.to_le (sup_le hSP (zpowers_le.mpr hxP)))
  apply hxS
  rw [← heq]
  exact mem_sup_right (mem_zpowers x)

theorem exists_move_of_not_isSylow_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f) (hc : ¬ ∀ r ∈ R₂, t * r * t⁻¹ = r⁻¹)
    (hns : ¬ ∃ P : Sylow 2 (normalizer (szA₁ (szT₁ L T) : Set G)),
      (P : Subgroup (normalizer (szA₁ (szT₁ L T) : Set G))) =
        (T ⊔ R₂).subgroupOf (normalizer (szA₁ (szT₁ L T) : Set G))) :
    ∃ y ∈ normalizer ((szT₁ L T ⊔ R₂ ⊔ zpowers t : Subgroup G) : Set G),
      y * t * y⁻¹ ∉ R₂ ⊔ zpowers t := by
  obtain ⟨-, hS₁N, hS₁A, hR₁S₁, -, -⟩ := h.s₁_facts_of_card_sylow hS2 hR
  obtain ⟨-, -, -, -, -, hsyl⟩ := h.u3R2_canonical_of_card_sylow hS2 hR
  set X := normalizer (szA₁ (szT₁ L T) : Set G) with hX
  have hS' : IsPGroup 2 ((T ⊔ R₂).subgroupOf X) :=
    hsyl.isPGroup.of_equiv (subgroupOfEquivOfLe hS₁A).symm
  obtain ⟨z, hz, hzS, P, hP, hSP, hzP⟩ := exists_normalizer_not_mem_of_not_isSylow hS' hns
  have hxS : (z : G) ∉ T ⊔ R₂ := fun h1 => hzS (mem_subgroupOf.mpr h1)
  have hxN : (z : G) ∈ normalizer ((T ⊔ R₂ : Subgroup G) : Set G) := by
    refine mem_normalizer_of_forall_inv_mul_mul_mem fun w hw => ?_
    have h1 := (mem_normalizer_iff''.mp hz ⟨w, hS₁A hw⟩).mp (mem_subgroupOf.mpr hw)
    rw [mem_subgroupOf] at h1
    simpa using h1
  have hxR : (z : G) ∈ normalizer (szR (szT₁ L T) R₂ t : Set G) := by
    refine mem_normalizer_of_forall_inv_mul_mul_mem fun r hr => ?_
    refine h.weakClosed_of_card_sylow hS2 hR z z.2 (fun r' hr' => ?_) r hr
    exact (mem_normalizer_iff''.mp hxN _).mp (hR₁S₁ hr')
  refine ⟨z, hxR, h.conj_not_mem_of_card_sylow hS2 hR hc hxR z.2 hxS
    (hP.map X.subtype) ?_ ⟨z, hzP, rfl⟩⟩
  intro w hw
  exact ⟨⟨w, hS₁A hw⟩, hSP (mem_subgroupOf.mpr hw), rfl⟩

theorem exists_move_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f) (hstar : StarPrimeStatement f)
    (hN : normalizer ((T ⊔ R₂ : Subgroup G) : Set G) ≤ normalizer (szA₁ (szT₁ L T) : Set G))
    (hc : ¬ ∀ r ∈ R₂, t * r * t⁻¹ = r⁻¹) :
    ∃ y ∈ normalizer ((szT₁ L T ⊔ R₂ ⊔ zpowers t : Subgroup G) : Set G),
      y * t * y⁻¹ ∉ R₂ ⊔ zpowers t := by
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hsylA : ∃ P : Sylow 2 (normalizer (szA₁ (szT₁ L T) : Set G)),
      (P : Subgroup (normalizer (szA₁ (szT₁ L T) : Set G))) =
        (T ⊔ R₂).subgroupOf (normalizer (szA₁ (szT₁ L T) : Set G))
  · exfalso
    obtain ⟨-, -, hS₁A, -, -, -⟩ := h.s₁_facts_of_card_sylow hS2 hR
    obtain ⟨-, -, -, -, -, hsyl⟩ := h.u3R2_canonical_of_card_sylow hS2 hR
    obtain ⟨x, hxN, hxS, P, hP, hSP, hxP⟩ := exists_normalizer_not_mem_of_not_isSylow
      hsyl.isPGroup (h.not_isSylow_S₁_of_starPrime_of_card_sylow hS2 hR hstar)
    obtain ⟨Q, hQ⟩ := hsylA
    have hsylA' : CFSG.ABGLocalTools.IsSylowOf 2 (T ⊔ R₂)
        (normalizer (szA₁ (szT₁ L T) : Set G)) :=
      ⟨Q, by rw [hQ, subgroupOf_map_subtype, inf_eq_left.mpr hS₁A]⟩
    have heq := hsylA'.eq_of_le (le_sup_left : T ⊔ R₂ ≤ (T ⊔ R₂) ⊔ zpowers x)
      (sup_le hS₁A (zpowers_le.mpr (hN hxN))) (hP.to_le (sup_le hSP (zpowers_le.mpr hxP)))
    apply hxS
    rw [← heq]
    exact mem_sup_right (mem_zpowers x)
  · exact h.exists_move_of_not_isSylow_of_card_sylow hS2 hR hc hsylA

end Certificates

end U3Start

end CFSG.SeitzReduction.RankOne
