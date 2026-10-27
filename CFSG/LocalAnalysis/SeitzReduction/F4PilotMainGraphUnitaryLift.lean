module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphTorusLift

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.EvenSmallLie
  CFSG.Assembly.LowTwoRank
open CFSG.Quasithin (perfectCore)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

local instance f4PilotMainGraphUnitaryLiftNeZeroRank : NeZero Tag.F4.rank := ⟨by decide⟩

section TLift

variable {M : Type} [Group M] [Finite M] {G : Type} [Group G]

theorem exists_mulAut_comp_eq_conj_of_closed [Group.IsPerfect M]
    (hsplit : ∀ (E' : Type) [Group E'] [Finite E'] (π' : E' →* M), Function.Surjective π' →
      π'.ker ≤ center E' → ∃ s : M →* E', ∀ g, π' (s g) = g)
    (Φ : M →* G) (hker : Φ.ker ≤ center M) {t : G} (ht : t ∈ normalizer (Φ.range : Set G)) :
    ∃ β : MulAut M, ∀ g, Φ (β g) = t * Φ g * t⁻¹ := by
  set c : MulAut Φ.range := Φ.range.normalizerMonoidHom ⟨t, ht⟩ with hc
  have hcapp : ∀ y : Φ.range, ((c y : Φ.range) : G) = t * y * t⁻¹ := fun y =>
    coe_normalizerMonoidHom_mk_apply Φ.range ht y
  set π : M →* Φ.range := c.toMonoidHom.comp Φ.rangeRestrict
  have hπ : Function.Surjective π := c.surjective.comp Φ.rangeRestrict_surjective
  have hρker : Φ.rangeRestrict.ker ≤ center M := by
    rw [MonoidHom.ker_rangeRestrict]
    exact hker
  obtain ⟨θ, hθs, hθ⟩ := exists_lift_of_central π hπ hsplit Φ.rangeRestrict
    Φ.rangeRestrict_surjective hρker
  have hθb : Function.Bijective θ := ⟨Finite.injective_iff_surjective.mpr hθs, hθs⟩
  refine ⟨MulEquiv.ofBijective θ hθb, fun g => ?_⟩
  have h1 := congrArg Subtype.val (hθ g)
  change Φ (θ g) = ((c (Φ.rangeRestrict g) : Φ.range) : G) at h1
  rw [hcapp] at h1
  exact h1

omit [Finite M] in
theorem mulAut_eq_of_comp_eq_of_perfect [Group.IsPerfect M] (Φ : M →* G) (hker : Φ.ker ≤ center M)
    {γ₁ γ₂ : MulAut M} (h : ∀ g, Φ (γ₁ g) = Φ (γ₂ g)) : γ₁ = γ₂ := by
  refine graphTorus_mulAut_eq_of_inv_mul_mem_center fun g => hker ?_
  rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]

omit [Finite M] in
theorem mulAut_mul_self_of_comp_eq_conj_of_perfect [Group.IsPerfect M] (Φ : M →* G)
    (hker : Φ.ker ≤ center M) {t : G} (htt : t * t = 1) {β : MulAut M}
    (hβ : ∀ g, Φ (β g) = t * Φ g * t⁻¹) : β * β = 1 := by
  refine mulAut_eq_of_comp_eq_of_perfect Φ hker fun g => ?_
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  rw [MulAut.mul_apply, hβ, hβ, MulAut.one_apply, ht']
  calc t * (t * Φ g * t) * t = (t * t) * Φ g * (t * t) := by group
    _ = Φ g := by rw [htt, one_mul, mul_one]

end TLift

section Transfer

variable {M : Type} [Group M] {Kb : Type} [Group Kb]

@[expose] noncomputable def centerQuotientEquivOfSurjective [Group.IsPerfect M] (χ : M →* Kb)
    (hχ : Function.Surjective χ) (hker : χ.ker ≤ center M) :
    M ⧸ center M ≃* Kb ⧸ center Kb :=
  (QuotientGroup.quotientMulEquivOfEq (show center M =
      ((QuotientGroup.mk' (center Kb)).comp χ).ker by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    constructor
    · intro hx
      rw [mem_center_iff]
      intro k
      obtain ⟨y, rfl⟩ := hχ k
      rw [← map_mul, ← map_mul, mem_center_iff.mp hx y]
    · exact CFSG.ComponentClassification.OddSelector.mem_center_of_map_mem_center χ hker)).trans
    (QuotientGroup.quotientKerEquivOfSurjective _
      ((QuotientGroup.mk'_surjective (center Kb)).comp hχ))

theorem centerQuotientEquivOfSurjective_mk [Group.IsPerfect M] (χ : M →* Kb)
    (hχ : Function.Surjective χ) (hker : χ.ker ≤ center M) (g : M) :
    centerQuotientEquivOfSurjective χ hχ hker (QuotientGroup.mk' (center M) g) =
      QuotientGroup.mk' (center Kb) (χ g) :=
  rfl

theorem congr_centerQuotientAut [Group.IsPerfect M] (χ : M →* Kb) (hχ : Function.Surjective χ)
    (hker : χ.ker ≤ center M) {β : MulAut M} {τ : MulAut Kb} (hβτ : ∀ g, χ (β g) = τ (χ g)) :
    MulAut.congr (centerQuotientEquivOfSurjective χ hχ hker) (centerQuotientAut β) =
      centerQuotientAut τ := by
  ext y
  obtain ⟨x, rfl⟩ := (centerQuotientEquivOfSurjective χ hχ hker).surjective y
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (center M) x
  rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
    centerQuotientAut_mk, centerQuotientEquivOfSurjective_mk, centerQuotientEquivOfSurjective_mk,
    hβτ, centerQuotientAut_mk]

theorem nonempty_fixedSubgroup_centerQuotientAut_equiv [Group.IsPerfect M] (χ : M →* Kb)
    (hχ : Function.Surjective χ) (hker : χ.ker ≤ center M) {β : MulAut M} {τ : MulAut Kb}
    (hβτ : ∀ g, χ (β g) = τ (χ g)) :
    Nonempty (fixedSubgroup (centerQuotientAut β) ≃* fixedSubgroup (centerQuotientAut τ)) :=
  ⟨(CFSG.ComponentClassification.CatLeafProof.fixedSubgroupCongrEquiv
    (centerQuotientEquivOfSurjective χ hχ hker) _).trans
      (MulEquiv.subgroupCongr (congrArg fixedSubgroup (congr_centerQuotientAut χ hχ hker hβτ)))⟩

theorem mem_range_conj_of_centerQuotientAut [Group.IsPerfect M] (χ : M →* Kb)
    (hχ : Function.Surjective χ) {β : MulAut M} {τ : MulAut Kb} (hβτ : ∀ g, χ (β g) = τ (χ g))
    (h : centerQuotientAut β ∈ (MulAut.conj : M ⧸ center M →* MulAut (M ⧸ center M)).range) :
    τ ∈ (MulAut.conj : Kb →* MulAut Kb).range := by
  obtain ⟨x, hx⟩ := h
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (center M) x
  have hβ : β = MulAut.conj g := by
    refine (graphTorus_mulAut_eq_of_inv_mul_mem_center fun y => ?_).symm
    have h1 := congrArg (fun α : MulAut (M ⧸ center M) => α (QuotientGroup.mk' (center M) y)) hx
    simp only [MulAut.conj_apply, centerQuotientAut_mk] at h1
    rw [← map_mul, ← map_inv, ← map_mul, eq_comm, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq] at h1
    have h2 := inv_mem h1
    simpa [MulAut.conj_apply, mul_assoc] using h2
  refine ⟨χ g, MulEquiv.ext fun k => ?_⟩
  obtain ⟨h', rfl⟩ := hχ k
  rw [← hβτ, hβ, MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv]

omit [Group Kb] in
theorem centerQuotientAut_mul (β γ : MulAut M) :
    centerQuotientAut (β * γ) = centerQuotientAut β * centerQuotientAut γ := by
  ext x
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (center M) x
  rw [MulAut.mul_apply, centerQuotientAut_mk, centerQuotientAut_mk, centerQuotientAut_mk,
    MulAut.mul_apply]

omit [Group Kb] in
theorem centerQuotientAut_one : centerQuotientAut (1 : MulAut M) = 1 := by
  ext x
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (center M) x
  rw [centerQuotientAut_mk, MulAut.one_apply, MulAut.one_apply]

end Transfer

section Setting


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K]

theorem exists_graphLift_of_closed_X {t : G} {f : ℕ} (hw : F4Work L K t f) (hf : 2 ≤ f)
    (e : L ≃* adjointGroup .F4 K) {κ : Sp6Kind} (hκF : κ ≠ .field) (hκS : κ ≠ .swap)
    (hX : HR8Kind e t f .X κ) {M : Type} [Group M] [Finite M] [Group.IsPerfect M]
    (hsplit : ∀ (E' : Type) [Group E'] [Finite E'] (π' : E' →* M), Function.Surjective π' →
      π'.ker ≤ center E' → ∃ s : M →* E', ∀ g, π' (s g) = g)
    (Φ : M →* G) (hE : Φ.range = neighbourCore e .X) (hker : Φ.ker ≤ center M) :
    ∃ β : MulAut M, (∀ g, Φ (β g) = t * Φ g * t⁻¹) ∧ β * β = 1 ∧
      centerQuotientAut β * centerQuotientAut β = 1 ∧
      centerQuotientAut β ∉ (MulAut.conj : M ⧸ center M →* MulAut (M ⧸ center M)).range ∧
      LieModel (fixedSubgroup (centerQuotientAut β)) .PSp 3 2 f := by
  have htt : t * t = 1 := by rw [← sq, ← hw.orderOf_eq, pow_orderOf_eq_one]
  have htN : t ∈ normalizer (Φ.range : Set G) := by
    rw [hE]
    exact le_normalizer_neighbourCore e hw.mem_centralizer .X
  obtain ⟨β, hβ⟩ := exists_mulAut_comp_eq_conj_of_closed hsplit Φ hker htN
  have hββ := mulAut_mul_self_of_comp_eq_conj_of_perfect Φ hker htt hβ
  obtain ⟨Kb, _, τ, qh, hqs, hqker, hτo, hτfix, hqt⟩ := exists_neighbourCoreData_X hw hf e hκS hX
    fun _ _ _ hKb hty => isSolvable_outer_of_sp6KindType_graph hKb hκF hκS hty
  have hmemE : ∀ g, Φ g ∈ neighbourCore e .X := fun g => hE ▸ ⟨g, rfl⟩
  set Φ' : M →* neighbourCore e .X := Φ.codRestrict _ hmemE
  have hΦ's : Function.Surjective Φ' := by
    rintro ⟨y, hy⟩
    rw [← hE] at hy
    obtain ⟨g, rfl⟩ := hy
    exact ⟨g, rfl⟩
  have hΦ'ker : Φ'.ker ≤ center M := fun g hg =>
    hker (by
      rw [MonoidHom.mem_ker] at hg ⊢
      exact congrArg Subtype.val hg)
  set χ : M →* Kb := qh.comp Φ'
  have hχs : Function.Surjective χ := hqs.comp hΦ's
  have hχker : χ.ker ≤ center M := fun g hg =>
    CFSG.ComponentClassification.OddSelector.mem_center_of_map_mem_center Φ' hΦ'ker (hqker hg)
  have hχβ : ∀ g, χ (β g) = τ (χ g) := by
    intro g
    have hy : t * ((Φ' g : neighbourCore e .X) : G) * t⁻¹ ∈ neighbourCore e .X := by
      change t * Φ g * t⁻¹ ∈ neighbourCore e .X
      rw [← hβ]
      exact hmemE _
    have e1 : Φ' (β g) = ⟨t * ((Φ' g : neighbourCore e .X) : G) * t⁻¹, hy⟩ :=
      Subtype.ext (hβ g)
    change qh (Φ' (β g)) = τ (qh (Φ' g))
    rw [e1, hqt]
  refine ⟨β, hβ, hββ, by rw [← centerQuotientAut_mul, hββ, centerQuotientAut_one],
    fun hin => hτo (mem_range_conj_of_centerQuotientAut χ hχs hχβ hin), ?_⟩
  obtain ⟨ε⟩ := nonempty_fixedSubgroup_centerQuotientAut_equiv χ hχs hχker hχβ
  exact CFSG.LieType.CurtisTits.lieModel_of_mulEquiv ε.symm hτfix

end Setting

end CFSG.SeitzReduction.F4Pilot
