module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimpleSplit

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.CrossChar
open scoped commutatorElement Polynomial

set_option linter.unusedSectionVars false


section FixedField

variable {L : Type} [Field L] [IsAlgClosed L]

theorem ncard_pow_eq_self (r e : ℕ) [Fact r.Prime] [CharP L r] (he : 0 < e) :
    {c : L | c ^ (r ^ e) = c}.Finite ∧ {c : L | c ^ (r ^ e) = c}.ncard = r ^ e := by
  have hQ : 1 < r ^ e := Nat.one_lt_pow he.ne' (Fact.out : r.Prime).one_lt
  have hsep : (Polynomial.X ^ (r ^ e) - Polynomial.X : L[X]).Separable :=
    galois_poly_separable r (r ^ e) (dvd_pow_self r he.ne')
  have hcard := Polynomial.card_rootSet_eq_natDegree (K := L) hsep (IsAlgClosed.splits_domain _)
  have hdeg : (Polynomial.X ^ (r ^ e) - Polynomial.X : L[X]).natDegree = r ^ e := FiniteField.X_pow_card_sub_X_natDegree_eq L hQ
  have hne : (Polynomial.X ^ (r ^ e) - Polynomial.X : L[X]) ≠ 0 := fun h0 => by
    have := hdeg
    rw [h0, Polynomial.natDegree_zero] at this
    omega
  have hset : (Polynomial.X ^ (r ^ e) - Polynomial.X : L[X]).rootSet L = {c : L | c ^ (r ^ e) = c} := by
    ext c
    simp only [Polynomial.mem_rootSet, ne_eq, Set.mem_setOf_eq]
    constructor
    · rintro ⟨-, h⟩
      simpa [sub_eq_zero] using h
    · intro h
      exact ⟨hne, by simpa [sub_eq_zero] using h⟩
  rw [← hset]
  refine ⟨Set.toFinite _, ?_⟩
  rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card, hcard, hdeg]


theorem exists_unit_sq_ne_one {r e : ℕ} [Fact r.Prime] [CharP L r] (σ : L ≃+* L)
    (hσ : ∀ c, σ c = c ^ (r ^ e)) (he : 0 < e) (hQ : 4 ≤ r ^ e) :
    ∃ t : (fixSubfield σ)ˣ, t ^ 2 ≠ 1 := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨hfin, hcard⟩ := ncard_pow_eq_self (L := L) r e he
  have hsub : {c : L | c ^ (r ^ e) = c} ⊆ (({0, 1, -1} : Finset L) : Set L) := by
    intro c hc
    by_cases h0 : c = 0
    · simp [h0]
    · have hmem : c ∈ fixSubfield σ := by
        rw [mem_fixSubfield, hσ]
        exact hc
      have h1 := hcon (Units.mk0 ⟨c, hmem⟩ (fun h => h0 (congrArg Subtype.val h)))
      have h2 : c ^ 2 = 1 := by
        have := congrArg (fun x : (fixSubfield σ)ˣ => ((x : fixSubfield σ) : L)) h1
        simpa using this
      have h3 : (c - 1) * (c + 1) = 0 := by linear_combination h2
      rcases mul_eq_zero.1 h3 with h | h
      · simp [sub_eq_zero.1 h]
      · simp [eq_neg_of_add_eq_zero_left h]
  have := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
  rw [hcard, Set.ncard_coe_finset] at this
  have h3 : ({0, 1, -1} : Finset L).card ≤ 3 := by
    refine (Finset.card_insert_le _ _).trans ?_
    have := Finset.card_insert_le (1 : L) {-1}
    simp only [Finset.card_singleton] at this
    omega
  omega

end FixedField

section Quasi

variable {τ : Tag} {L : Type} [Field L] {M : Type*} [CommGroup M]
  {χ : Multiplicative (Fin τ.rank → ℤ) →* M} (i : KernelComponent χ)

theorem CQ_eq_map (σ : L ≃+* L) :
    CQ σ i = (componentRootSpan (fixSubfield σ) χ i).map
      (baseChangeGL (fixSubfield σ).subtype) := by
  apply le_antisymm
  · unfold CQ
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨γ, hγ, c, hc, rfl⟩
    have hcK : c ∈ fixSubfield σ := hc
    refine ⟨pinnedX τ (fixSubfield σ) γ ⟨c, hcK⟩, ?_, ?_⟩
    · rw [unionRoots_singleton] at hγ
      exact pinnedX_mem_rootSpan hγ _
    · exact baseChangeGL_pinnedX (fixSubfield σ).subtype γ ⟨c, hcK⟩
  · rw [Subgroup.map_le_iff_le_comap]
    refine iSup₂_le fun γ hγ => ?_
    rw [rootSubgroup, Subgroup.closure_le]
    rintro _ ⟨c, rfl⟩
    show baseChangeGL (fixSubfield σ).subtype (pinnedX τ (fixSubfield σ) γ c) ∈ CQ σ i
    rw [baseChangeGL_pinnedX]
    exact pinnedX_mem_CQ (by rw [unionRoots_singleton]; exact hγ) c.2

end Quasi

section Image

theorem commute_of_forall_commutator_mem_center {C : Type*} [Group C] (hC : Group.IsPerfect C)
    {c : C} (hc : ∀ x : C, ⁅c, x⁆ ∈ Subgroup.center C) : c ∈ Subgroup.center C := by
  let φ : C →* Subgroup.center C :=
    { toFun := fun x => ⟨⁅c, x⁆, hc x⟩
      map_one' := by ext; simp
      map_mul' := fun x y => by
        ext
        have hz : ⁅c, y⁆ ∈ Subgroup.center C := hc y
        have h1 : ⁅c, x * y⁆ = ⁅c, x⁆ * (x * ⁅c, y⁆ * x⁻¹) := by
          simp only [commutatorElement_def]; group
        have h2 : x * ⁅c, y⁆ * x⁻¹ = ⁅c, y⁆ := by
          have := (Subgroup.mem_center_iff.1 hz x)
          rw [this]; group
        simp only [Subgroup.coe_mul]
        rw [h1, h2] }
  have hker : commutator C ≤ φ.ker := by
    rw [commutator_def C, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker]
    have h1 : φ ⁅a, b⁆ = ⁅φ a, φ b⁆ := map_commutatorElement φ a b
    rw [h1]
    exact commutatorElement_eq_one_iff_mul_comm.2
      (Subtype.ext (Subgroup.mem_center_iff.1 (φ b).2 (φ a : C)))
  have htop : commutator C = ⊤ := Group.isPerfect_def.1 hC
  rw [htop] at hker
  rw [Subgroup.mem_center_iff]
  intro x
  have h3 : φ x = 1 := hker (Subgroup.mem_top x)
  have h4 : ⁅c, x⁆ = 1 := congrArg Subtype.val h3
  rw [commutatorElement_eq_one_iff_mul_comm] at h4
  exact h4.symm

theorem isQuasisimple_range_of_ker_le_center {C G : Type*} [Group C] [Group G]
    (hC : CFSG.IsQuasisimple C) (f : C →* G) (hker : f.ker ≤ Subgroup.center C) :
    CFSG.IsQuasisimple f.range := by
  obtain ⟨hperf, hsimple, a, b, hab⟩ := hC
  set H : Subgroup G := f.range with hH
  set f' : C →* H := f.rangeRestrict with hf'
  have hsurj : Function.Surjective f' := f.rangeRestrict_surjective
  have hf'ker : f'.ker = f.ker := f.ker_rangeRestrict
  have hcenter : ∀ c : C, f' c ∈ Subgroup.center H ↔ c ∈ Subgroup.center C := by
    intro c
    constructor
    · intro hc
      refine commute_of_forall_commutator_mem_center hperf fun x => ?_
      have h1 : f' ⁅c, x⁆ = 1 := by
        rw [map_commutatorElement]
        exact commutatorElement_eq_one_iff_mul_comm.2 (Subgroup.mem_center_iff.1 hc (f' x)).symm
      exact hker (by rw [← hf'ker]; exact h1)
    · intro hc
      rw [Subgroup.mem_center_iff]
      intro h
      obtain ⟨x, rfl⟩ := hsurj h
      rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.1 hc x).symm]
  set Φ : C →* H ⧸ Subgroup.center H := (QuotientGroup.mk' (Subgroup.center H)).comp f' with hΦ
  have hΦsurj : Function.Surjective Φ := (QuotientGroup.mk'_surjective _).comp hsurj
  have hΦker : Φ.ker = Subgroup.center C := by
    ext c
    rw [MonoidHom.mem_ker, hΦ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    exact hcenter c
  let e : C ⧸ Subgroup.center C ≃* H ⧸ Subgroup.center H :=
    (QuotientGroup.quotientMulEquivOfEq hΦker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective Φ hΦsurj)
  have hperfH : Group.IsPerfect H := Group.IsPerfect.ofSurjective hsurj
  have hsimp : IsSimpleGroup (C ⧸ Subgroup.center C) := hsimple
  refine ⟨hperfH, MulEquiv.isSimpleGroup e.symm, e a, e b, fun h => hab (e.injective ?_)⟩
  rw [map_mul, map_mul]
  exact h

end Image

end CFSG.HardMathSupport.Timmesfeld.LangTorus
