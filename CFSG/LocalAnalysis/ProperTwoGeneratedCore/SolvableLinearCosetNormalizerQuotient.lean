module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian

public section

namespace CFSG.ProperTwoGeneratedCore.HighRankPair

open scoped commutatorElement

variable {G : Type*} [Group G]

theorem isElementaryAbelian_quotient {Q U : Subgroup G} [(U.subgroupOf Q).Normal]
    (hsq : ∀ x ∈ Q, x * x ∈ U) (hcomm : ∀ x ∈ Q, ∀ y ∈ Q, x * y * x⁻¹ * y⁻¹ ∈ U) :
    IsElementaryAbelian 2 (Q ⧸ U.subgroupOf Q) := by
  have hc : ∀ a b : Q ⧸ U.subgroupOf Q, a * b = b * a := by
    intro a b
    induction a using QuotientGroup.induction_on with | H x => ?_
    induction b using QuotientGroup.induction_on with | H y => ?_
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have h := hcomm _ (Q.inv_mem y.2) _ (Q.inv_mem x.2)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, inv_inv] at h ⊢
    convert h using 1
    group
  refine { toIsMulCommutative := ⟨⟨hc⟩⟩, exponent_dvd_p := ?_ }
  apply Monoid.exponent_dvd_of_forall_pow_eq_one
  intro a
  induction a using QuotientGroup.induction_on with | H x => ?_
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, pow_two]
  exact hsq x x.2

theorem closure_commutators_quotient_eq {Q U A : Subgroup G} [(U.subgroupOf Q).Normal]
    (hAQ : A ≤ Subgroup.normalizer (Q : Set G)) :
    Subgroup.closure {f : Q ⧸ U.subgroupOf Q | ∃ a ∈ A, ∃ x y : Q,
        (y : G) = a * x * a⁻¹ ∧ f = QuotientGroup.mk y * (QuotientGroup.mk x)⁻¹} =
      (⁅A, Q⁆.subgroupOf Q).map (QuotientGroup.mk' (U.subgroupOf Q)) := by
  have hmem : ∀ a ∈ A, ∀ x ∈ Q, ⁅a, x⁆ ∈ Q := fun a ha x hx => by
    rw [commutatorElement_def]
    exact Q.mul_mem ((Subgroup.mem_normalizer_iff.mp (hAQ ha) x).mp hx) (Q.inv_mem hx)
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro _ ⟨a, ha, x, y, hy, rfl⟩
    refine ⟨⟨⁅a, (x : G)⁆, hmem a ha x x.2⟩, ?_, ?_⟩
    · exact Subgroup.mem_subgroupOf.mpr (Subgroup.commutator_mem_commutator ha x.2)
    · rw [QuotientGroup.mk'_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
      congr 1
      apply Subtype.ext
      simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv, hy]
  · rw [Subgroup.map_le_iff_le_comap]
    have hle : ⁅A, Q⁆ ≤ (Subgroup.comap (QuotientGroup.mk' (U.subgroupOf Q))
        (Subgroup.closure {f : Q ⧸ U.subgroupOf Q | ∃ a ∈ A, ∃ x y : Q,
          (y : G) = a * x * a⁻¹ ∧ f = QuotientGroup.mk y * (QuotientGroup.mk x)⁻¹})).map
          Q.subtype := by
      rw [Subgroup.commutator_le]
      intro a ha x hx
      refine ⟨⟨⁅a, x⁆, hmem a ha x hx⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_comap]
      apply Subgroup.subset_closure
      refine ⟨a, ha, ⟨x, hx⟩, ⟨a * x * a⁻¹, (Subgroup.mem_normalizer_iff.mp (hAQ ha) x).mp hx⟩,
        rfl, ?_⟩
      rw [QuotientGroup.mk'_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
      congr 1
    intro y hy
    obtain ⟨y', hy', hyy'⟩ := hle (Subgroup.mem_subgroupOf.mp hy)
    have : y' = y := Subtype.ext hyy'
    rw [← this]
    exact hy'

theorem eq_one_or_eq_of_mem_zpowers {u y : G} (hu : u * u = 1) (hy : y ∈ Subgroup.zpowers u) :
    y = 1 ∨ y = u := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hu2 : u ^ (2 : ℤ) = 1 := by rw [zpow_two, hu]
  have hk : u ^ k = u ^ (k % 2) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv k 2, zpow_add, zpow_mul, hu2, one_zpow, mul_one]
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · left; rw [hk, h0, zpow_zero]
  · right; rw [hk, h1, zpow_one]

theorem isCompl_quotient_of_sup_eq {Q U V : Subgroup G} {u : G} [(U.subgroupOf Q).Normal]
    (hUV : U ≤ V) (hVQ : V ≤ Q) (hu : u * u = 1) (huQ : u ∈ Q) (huV : u ∉ V)
    (hQ : Subgroup.zpowers u ⊔ V = Q) :
    IsCompl (((Subgroup.zpowers u).subgroupOf Q).map (QuotientGroup.mk' (U.subgroupOf Q)))
      ((V.subgroupOf Q).map (QuotientGroup.mk' (U.subgroupOf Q))) := by
  have hzpow : ∀ y ∈ Subgroup.zpowers u, y = 1 ∨ y = u := fun y hy =>
    eq_one_or_eq_of_mem_zpowers hu hy
  constructor
  · rw [Subgroup.disjoint_def]
    rintro f ⟨y, hy, rfl⟩ ⟨v, hv, hvy⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hy hv
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      Subgroup.mem_subgroupOf] at hvy
    have hyV : (y : G) ∈ V := by
      have h1 : (y : G) = v * ((v⁻¹ * y : Q) : G) := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
      rw [h1]
      exact V.mul_mem hv (hUV hvy)
    rcases hzpow _ hy with h1 | h1
    · rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff _).mpr]
      rw [Subgroup.mem_subgroupOf, h1]
      exact Subgroup.one_mem _
    · exact absurd (h1 ▸ hyV) huV
  · rw [codisjoint_iff, ← Subgroup.map_sup,
      ← Subgroup.subgroupOf_sup (Subgroup.zpowers_le.mpr huQ) hVQ, hQ, Subgroup.subgroupOf_self]
    exact Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)

theorem map_comap_map_mk'_eq {Q U V : Subgroup G} [(U.subgroupOf Q).Normal] (hUV : U ≤ V)
    (hVQ : V ≤ Q) :
    (((V.subgroupOf Q).map (QuotientGroup.mk' (U.subgroupOf Q))).comap
      (QuotientGroup.mk' (U.subgroupOf Q))).map Q.subtype = V := by
  have hle : U.subgroupOf Q ≤ V.subgroupOf Q := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (hUV (Subgroup.mem_subgroupOf.mp hx))
  rw [QuotientGroup.comap_map_mk', sup_eq_right.mpr hle,
    Subgroup.map_subgroupOf_eq_of_le hVQ]

theorem map_mk'_sup_eq {Q U K : Subgroup G} [(U.subgroupOf Q).Normal] (hUQ : U ≤ Q)
    (hKQ : K ≤ Q) :
    ((U ⊔ K).subgroupOf Q).map (QuotientGroup.mk' (U.subgroupOf Q)) =
      (K.subgroupOf Q).map (QuotientGroup.mk' (U.subgroupOf Q)) := by
  rw [Subgroup.subgroupOf_sup hUQ hKQ, Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq]

end CFSG.ProperTwoGeneratedCore.HighRankPair
