module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaInputsKinds
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaEndDefs
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneLinearField

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaInputs

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.ComponentClassification
open scoped MatrixGroups

section LinAut

variable {n : ℕ} {F : Type} [Field F]

theorem stdSL_eq (A : GL (Fin n) F) (σ : F ≃+* F) (ε : ℕ) :
    stdSL n F A σ ε = CatalogueBHigherLinearAction.slConjugation n F A *
      CatalogueBHigherLinearField.slFieldAut (Fin n) F σ * CatalogueBGraphForm.slGraphAut n F ^ ε :=
  rfl

theorem stdSL_one_eq (A : GL (Fin n) F) (ε : ℕ) :
    stdSL n F A 1 ε = CatalogueBHigherLinearAction.slConjugation n F A *
      CatalogueBGraphForm.slGraphAut n F ^ ε := by
  rw [stdSL_eq, map_one, mul_one]

theorem slGraph_mul_slConjugation (A : GL (Fin n) F) :
    CatalogueBGraphForm.slGraphAut n F * CatalogueBHigherLinearAction.slConjugation n F A =
      CatalogueBHigherLinearAction.slConjugation n F (GeneralLinearGroup.inverseTranspose A) *
        CatalogueBGraphForm.slGraphAut n F := by
  rw [← slGraph_mul_slConjugation_mul_slGraph, mul_assoc, slGraph_mul_slGraph, mul_one]

variable (n F) in
@[expose] def linAut : Subgroup (MulAut SL(n, F)) where
  carrier := {β | ∃ (A : GL (Fin n) F) (ε : ℕ), ε ≤ 1 ∧ β = stdSL n F A 1 ε}
  mul_mem' := by
    rintro _ _ ⟨A, ε, hε, rfl⟩ ⟨B, η, hη, rfl⟩
    simp only [Set.mem_ofPred_eq]
    set c := CatalogueBHigherLinearAction.slConjugation n F
    set δ := CatalogueBGraphForm.slGraphAut n F
    have h := slGraph_mul_slConjugation (n := n) (F := F) B
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hε with rfl | rfl
    · refine ⟨A * B, η, hη, ?_⟩
      rw [stdSL_one_eq, stdSL_one_eq, stdSL_one_eq, pow_zero, mul_one, map_mul, mul_assoc]
    · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hη with rfl | rfl
      · refine ⟨A * GeneralLinearGroup.inverseTranspose B, 1, le_rfl, ?_⟩
        rw [stdSL_one_eq, stdSL_one_eq, stdSL_one_eq, pow_one, pow_zero, mul_one,
          map_mul, mul_assoc, h, mul_assoc]
      · refine ⟨A * GeneralLinearGroup.inverseTranspose B, 0, zero_le_one, ?_⟩
        rw [stdSL_one_eq, stdSL_one_eq, stdSL_one_eq, pow_one, pow_zero, mul_one]
        calc c A * δ * (c B * δ) = c A * (δ * c B) * δ := by simp only [mul_assoc]
          _ = c A * (c (GeneralLinearGroup.inverseTranspose B) * δ) * δ := by rw [h]
          _ = c A * c (GeneralLinearGroup.inverseTranspose B) * (δ * δ) := by
              simp only [mul_assoc]
          _ = c (A * GeneralLinearGroup.inverseTranspose B) := by
              rw [slGraph_mul_slGraph, mul_one, map_mul]
  one_mem' := ⟨1, 0, zero_le_one, by rw [stdSL_one_eq, map_one, pow_zero, mul_one]⟩
  inv_mem' := by
    rintro _ ⟨A, ε, hε, rfl⟩
    simp only [Set.mem_ofPred_eq]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hε with rfl | rfl
    · exact ⟨A⁻¹, 0, zero_le_one, by rw [stdSL_one_eq, stdSL_one_eq, pow_zero, mul_one,
        mul_one, map_inv]⟩
    · refine ⟨GeneralLinearGroup.inverseTranspose A⁻¹, 1, le_rfl, ?_⟩
      rw [stdSL_one_eq, stdSL_one_eq, pow_one, _root_.mul_inv_rev,
        inv_eq_of_mul_eq_one_right slGraph_mul_slGraph, ← map_inv, slGraph_mul_slConjugation]

theorem stdSL_mem_linAut (A : GL (Fin n) F) {ε : ℕ} (hε : ε ≤ 1) :
    stdSL n F A 1 ε ∈ linAut n F :=
  ⟨A, ε, hε, rfl⟩

theorem stdSL_mul_stdSL_mem_linAut {σ : F ≃+* F} (hσσ : σ * σ = 1) (A B : GL (Fin n) F)
    {ε η : ℕ} (hε : ε ≤ 1) (hη : η ≤ 1) : stdSL n F A σ ε * stdSL n F B σ η ∈ linAut n F := by
  set c := CatalogueBHigherLinearAction.slConjugation n F
  set f := CatalogueBHigherLinearField.slFieldAut (Fin n) F σ
  set δ := CatalogueBGraphForm.slGraphAut n F
  have hff : f * f = 1 := by rw [← map_mul, hσσ, map_one]
  have hfinv : f⁻¹ = f := inv_eq_of_mul_eq_one_right hff
  have hfδ : f * δ = δ * f := by
    have h := slGraph_mul_slField_mul_slGraph (n := n) (K := F) σ
    calc f * δ = δ * f * δ * δ := by rw [h]
      _ = δ * f * (δ * δ) := by simp only [mul_assoc]
      _ = δ * f := by rw [slGraph_mul_slGraph, mul_one]
  have hfδε : f * δ ^ ε = δ ^ ε * f := ((Commute.pow_right hfδ ε))
  have hfc : f * c B * f = c (CatalogueBHigherLinearField.glFieldEquiv (Fin n) σ B) := by
    calc f * c B * f = f * c B * f⁻¹ := by rw [hfinv]
      _ = _ := slField_mul_slConjugation_mul_inv σ B
  have key : stdSL n F A σ ε * stdSL n F B σ η =
      stdSL n F A 1 ε * stdSL n F (CatalogueBHigherLinearField.glFieldEquiv (Fin n) σ B) 1 η := by
    rw [stdSL_eq, stdSL_eq, stdSL_one_eq, stdSL_one_eq, ← hfc]
    calc c A * f * δ ^ ε * (c B * f * δ ^ η) = c A * (f * δ ^ ε) * (c B * f * δ ^ η) := by
          simp only [mul_assoc]
      _ = c A * (δ ^ ε * f) * (c B * f * δ ^ η) := by rw [hfδε]
      _ = c A * δ ^ ε * (f * c B * f * δ ^ η) := by simp only [mul_assoc]
  rw [key]
  exact mul_mem (stdSL_mem_linAut A hε) (stdSL_mem_linAut _ hη)

end LinAut

section Field

variable {n : ℕ} {F : Type} [Field F] [Finite F]

theorem field_eq_of_stdSL_eq (hn : 3 ≤ n) {A B : GL (Fin n) F} {σ τ : F ≃+* F} {ε η : ℕ}
    (hε : ε ≤ 1) (hη : η ≤ 1) (h : stdSL n F A σ ε = stdSL n F B τ η) : σ = τ :=
  (ProjectivePlane.standard_form_unique hn hε hη
    (by rw [← descendAut_stdSL, ← descendAut_stdSL, h])).1

omit [Finite F] in
theorem eq_sq_of_ne_one (hF : Nat.card F = 4) {σ : F ≃+* F} (hσ : σ ≠ 1) :
    ∀ c, σ c = c ^ 2 := by
  obtain ⟨φ, hφ, hord, hzp, -⟩ := finite_field_automorphism_fixed_field_cardinality
    (F := F) Nat.prime_two (n := 2) (by norm_num) (by rw [hF]; norm_num)
  have hσmem : σ ∈ zpowers φ := hzp ▸ mem_top σ
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hσmem
  rw [← zpow_mod_orderOf, hord] at hσ ⊢
  simp only [Nat.cast_ofNat] at hσ ⊢
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · rw [h, zpow_zero] at hσ
    exact absurd rfl hσ
  · intro c
    rw [h, zpow_one, hφ]

end Field

section Acts

variable {n : ℕ} {F : Type} [Field F] {G : Type*} [Group G] {K : Subgroup G}

@[expose] def Acts (ψ : SL(n, F) →* K) (y : G) (β : MulAut SL(n, F)) : Prop :=
  ∀ x, y * (ψ x : G) * y⁻¹ = ψ (β x)

theorem acts_one (ψ : SL(n, F) →* K) : Acts ψ 1 1 := fun x => by
  rw [one_mul, inv_one, mul_one, MulAut.one_apply]

theorem Acts.mul {ψ : SL(n, F) →* K} {y₁ y₂ : G} {β₁ β₂ : MulAut SL(n, F)}
    (h₁ : Acts ψ y₁ β₁) (h₂ : Acts ψ y₂ β₂) : Acts ψ (y₁ * y₂) (β₁ * β₂) := fun x => by
  rw [MulAut.mul_apply, ← h₁, ← h₂]
  group

theorem Acts.inv {ψ : SL(n, F) →* K} {y : G} {β : MulAut SL(n, F)} (h : Acts ψ y β) :
    Acts ψ y⁻¹ β⁻¹ := fun x => by
  have := h (β⁻¹ x)
  rw [MulAut.apply_inv_self] at this
  rw [← this]
  group

variable (ψ : SL(n, F) →* K) in
@[expose] def linSub : Subgroup G where
  carrier := {y | ∃ β ∈ linAut n F, Acts ψ y β}
  mul_mem' := by
    rintro _ _ ⟨β₁, hβ₁, h₁⟩ ⟨β₂, hβ₂, h₂⟩
    exact ⟨β₁ * β₂, mul_mem hβ₁ hβ₂, h₁.mul h₂⟩
  one_mem' := ⟨1, one_mem _, acts_one ψ⟩
  inv_mem' := by
    rintro _ ⟨β, hβ, h⟩
    exact ⟨β⁻¹, inv_mem hβ, h.inv⟩

theorem Acts.eq (hn : 3 ≤ n) {ψ : SL(n, F) →* K} (hker : ψ.ker ≤ center SL(n, F)) {y : G}
    {β β' : MulAut SL(n, F)} (h : Acts ψ y β) (h' : Acts ψ y β') : β = β' := by
  have := CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect (K := F) hn
  have hfg := eq_of_inv_mul_mem_center β.toMonoidHom β'.toMonoidHom fun x => by
    apply hker
    rw [MonoidHom.mem_ker, map_mul, map_inv]
    change (ψ (β x))⁻¹ * ψ (β' x) = 1
    have e : ψ (β x) = ψ (β' x) := Subtype.ext ((h x).symm.trans (h' x))
    rw [e, inv_mul_cancel]
  exact MulEquiv.ext fun x => DFunLike.congr_fun hfg x

variable [Finite F]

theorem not_mem_linSub (hn : 3 ≤ n) {ψ : SL(n, F) →* K} (hker : ψ.ker ≤ center SL(n, F))
    {y : G} {A : GL (Fin n) F} {σ : F ≃+* F} {ε : ℕ} (hε : ε ≤ 1)
    (hA : Acts ψ y (stdSL n F A σ ε)) (hσ : σ ≠ 1) : y ∉ linSub ψ := by
  rintro ⟨_, ⟨A', ε', hε', rfl⟩, h⟩
  exact hσ (field_eq_of_stdSL_eq hn hε hε' (hA.eq hn hker h))

theorem mul_mem_linSub (hn : 3 ≤ n) (hF : Nat.card F = 4) {ψ : SL(n, F) →* K}
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ center SL(n, F)) {x y : G}
    (hx : x ∈ normalizer (K : Set G)) (hy : y ∈ normalizer (K : Set G))
    (hxL : x ∉ linSub ψ) (hyL : y ∉ linSub ψ) : x * y ∈ linSub ψ := by
  obtain ⟨A, σ, ε, hε, hA⟩ := exists_stdSL_lift hn ψ hψ hker hx
  obtain ⟨B, τ, η, hη, hB⟩ := exists_stdSL_lift hn ψ hψ hker hy
  have hσ : σ ≠ 1 := by
    rintro rfl
    exact hxL ⟨_, stdSL_mem_linAut A hε, hA⟩
  have hτ : τ ≠ 1 := by
    rintro rfl
    exact hyL ⟨_, stdSL_mem_linAut B hη, hB⟩
  have hστ : τ = σ := RingEquiv.ext fun c => by
    rw [eq_sq_of_ne_one hF hσ, eq_sq_of_ne_one hF hτ]
  subst hστ
  have : Finite F := inferInstance
  have hσσ : τ * τ = 1 := by
    have := Fintype.ofFinite F
    refine RingEquiv.ext fun c => ?_
    rw [RingAut.mul_apply, eq_sq_of_ne_one hF hτ, eq_sq_of_ne_one hF hτ, ← pow_mul]
    have h4 := FiniteField.pow_card c
    rw [← Nat.card_eq_fintype_card, hF] at h4
    exact h4
  exact ⟨_, stdSL_mul_stdSL_mem_linAut hσσ A B hε hη, Acts.mul hA hB⟩

end Acts

theorem l64TransferInput : YamadaEnd.L64TransferInput := by
  intro G _ _ F _ _ hF G₀ ψ hψ hker _ T t hT htT ht h17
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have hTN : T ≤ normalizer (G₀ : Set G) := hT.le
  have hsmall : ∀ Q ≤ G₀ ⊓ centralizer ({t} : Set G), IsPGroup 2 Q →
      Nat.card Q < Nat.card F ^ (3 * 3) := fun Q hQ h2 => by
    have := h17 Q hQ h2
    rw [hF]
    omega
  obtain ⟨A, σ, ε, hε, hA⟩ := exists_stdSL_lift (by norm_num) ψ hψ hker (hTN htT)
  have hσ : σ ≠ 1 := field_ne_one_of_small hF (Or.inr rfl) rfl ψ hker htt hε hA hsmall
  have htL : t ∉ linSub ψ := not_mem_linSub (by norm_num) hker hε hA hσ
  refine ⟨T ⊓ linSub ψ, inf_le_left, ?_, ?_⟩
  · rw [relIndex, index_eq_two_iff]
    refine ⟨⟨t, htT⟩, fun b => ?_⟩
    have hbtT : (b : G) * t ∈ T := mul_mem b.2 htT
    simp only [mem_subgroupOf, Subgroup.coe_mul, mem_inf, b.2, hbtT, true_and]
    by_cases hb : (b : G) ∈ linSub ψ
    · have hbt : (b : G) * t ∉ linSub ψ := fun hbt => htL (by
        have := mul_mem (inv_mem hb) hbt
        rwa [inv_mul_cancel_left] at this)
      simp [hb, hbt]
    · have hbt := mul_mem_linSub (by norm_num) hF hψ hker (hTN b.2) (hTN htT) hb htL
      simp [hb, hbt]
  · rintro y ⟨-, β, ⟨A', ε', hε', rfl⟩, hy⟩ hy2
    have hyy : y * y = 1 := by rw [← sq, ← hy2, pow_orderOf_eq_one]
    obtain ⟨Q, hQ, hQ2, hQcard⟩ := exists_twoSubgroup_of_linear hF (Or.inr rfl) rfl ψ hker hyy
      hε' hy
    refine ⟨Q, hQ, hQ2, ?_⟩
    rw [hF] at hQcard
    calc 2 ^ 18 = 4 ^ (3 * 3) := by norm_num
      _ ≤ Nat.card Q := hQcard

end CFSG.EvenSmallLie.UnitarySix.YamadaInputs
