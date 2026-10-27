module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open QuadraticMap CFSG.ClassicalGroups.Orthogonal Module

theorem isSquare_mul_of_not_isSquare {F : Type*} [Field F] [Finite F] {a b : F} (ha : a ≠ 0)
    (hb : b ≠ 0) (ha' : ¬IsSquare a) (hb' : ¬IsSquare b) : IsSquare (a * b) := by
  classical
  have := Fintype.ofFinite F
  have hχa : quadraticChar F a = -1 := (quadraticChar_dichotomy ha).resolve_left
    fun h => ha' ((quadraticChar_one_iff_isSquare ha).1 h)
  have hχb : quadraticChar F b = -1 := (quadraticChar_dichotomy hb).resolve_left
    fun h => hb' ((quadraticChar_one_iff_isSquare hb).1 h)
  rw [← quadraticChar_one_iff_isSquare (mul_ne_zero ha hb), map_mul, hχa, hχb]
  norm_num

theorem exists_fin_four_eq_mul {A : Type*} [CommGroup A] {x₁ x₂ : A} (h₁ : x₁ ^ 2 = 1)
    (h₂ : x₂ ^ 2 = 1) {x : A} (hx : x = x₁ ∨ x = x₂) (i : Fin 4) :
    ∃ j, (![1, x₁, x₂, x₁ * x₂] : Fin 4 → A) j = x * ![1, x₁, x₂, x₁ * x₂] i := by
  rw [pow_two] at h₁ h₂
  rcases hx with rfl | rfl <;> fin_cases i
  · exact ⟨1, by simp⟩
  · exact ⟨0, by simp [h₁]⟩
  · exact ⟨3, by simp⟩
  · exact ⟨2, by simp [← mul_assoc, h₁]⟩
  · exact ⟨2, by simp⟩
  · exact ⟨3, by simp [mul_comm]⟩
  · exact ⟨0, by simp [h₂]⟩
  · exact ⟨1, by simp [mul_left_comm x, h₂]⟩

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem reflect_smul_of_ne_zero {c : K} (hc : c ≠ 0) (v : V) :
    reflect Q (c • v) = reflect Q v := by
  by_cases hv : Q v = 0
  · rw [reflect_of_map_eq_zero hv, reflect_of_map_eq_zero (by
      rw [QuadraticMap.map_smul, hv, smul_zero])]
  · have hcv : Q (c • v) ≠ 0 := by
      rw [QuadraticMap.map_smul, smul_eq_mul]
      exact mul_ne_zero (mul_ne_zero hc hc) hv
    refine LinearEquiv.ext fun x => ?_
    rw [reflect_apply hcv, reflect_apply hv, polar_smul_left, QuadraticMap.map_smul, smul_smul,
      smul_eq_mul, smul_eq_mul]
    congr 2
    field_simp

theorem exists_mem_orthogonalGroup_apply_eq (h2 : (2 : K) ≠ 0) {v w : V} (hvw : Q v = Q w)
    (hw : Q w ≠ 0) : ∃ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q, g v = w := by
  have : NeZero (2 : K) := ⟨h2⟩
  obtain ⟨f, hf⟩ := QuadraticMap.exists_isometryEquiv_apply_eq_of_map_eq Q hvw hw
  exact ⟨f.toLinearEquiv, TauCeti.QuadraticMap.mem_orthogonalGroup_iff.2 fun m => f.map_app m, hf⟩

variable (Q) in
noncomputable def reflectClass (v : V) : Abelianization (TauCeti.QuadraticMap.orthogonalGroup Q) :=
  Abelianization.of ⟨reflect Q v, reflect_mem_orthogonalGroup Q v⟩

theorem reflectClass_sq (v : V) : reflectClass Q v ^ 2 = 1 := by
  have h : (⟨reflect Q v, reflect_mem_orthogonalGroup Q v⟩ :
      TauCeti.QuadraticMap.orthogonalGroup Q) ^ 2 = 1 :=
    Subtype.ext (by rw [Subgroup.coe_pow, pow_two]; exact reflect_mul_self Q v)
  rw [reflectClass, ← map_pow, h, map_one]

theorem reflectClass_eq_of_isSquare (h2 : (2 : K) ≠ 0) {v w : V} (hv : Q v ≠ 0) (hw : Q w ≠ 0)
    (hsq : IsSquare (Q v * Q w)) : reflectClass Q v = reflectClass Q w := by
  obtain ⟨c, hc⟩ := hsq
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact mul_ne_zero hv hw (by rw [hc, mul_zero])
  have hw' : Q v = Q ((c / Q w) • w) := by
    rw [QuadraticMap.map_smul, smul_eq_mul]
    field_simp
    linear_combination hc
  obtain ⟨g, hg, hgv⟩ := exists_mem_orthogonalGroup_apply_eq h2 hw' (by rwa [← hw'])
  have hconj : (⟨g, hg⟩ : TauCeti.QuadraticMap.orthogonalGroup Q) *
      ⟨reflect Q v, reflect_mem_orthogonalGroup Q v⟩ * ⟨g, hg⟩⁻¹ =
        ⟨reflect Q w, reflect_mem_orthogonalGroup Q w⟩ := by
    refine Subtype.ext ?_
    change g * reflect Q v * g⁻¹ = reflect Q w
    rw [reflect_conj hg, hgv, reflect_smul_of_ne_zero (div_ne_zero hc0 hw)]
  rw [reflectClass, reflectClass, ← hconj, map_mul, map_mul, map_inv,
    mul_comm (Abelianization.of _), mul_inv_cancel_right]

theorem exists_reflectClass_two_values [Finite K] (h2 : (2 : K) ≠ 0) :
    ∃ x₁ x₂ : Abelianization (TauCeti.QuadraticMap.orthogonalGroup Q), x₁ ^ 2 = 1 ∧
      x₂ ^ 2 = 1 ∧ ∀ v, Q v ≠ 0 → reflectClass Q v = x₁ ∨ reflectClass Q v = x₂ := by
  by_cases h : ∃ v, Q v ≠ 0 ∧ ∃ w, Q w ≠ 0 ∧ ¬IsSquare (Q v * Q w)
  · obtain ⟨v₀, hv₀, w₀, hw₀, hns⟩ := h
    refine ⟨reflectClass Q v₀, reflectClass Q w₀, reflectClass_sq _, reflectClass_sq _,
      fun v hv => ?_⟩
    by_cases h1 : IsSquare (Q v₀ * Q v)
    · exact Or.inl (reflectClass_eq_of_isSquare h2 hv₀ hv h1).symm
    · right
      obtain ⟨c, hc⟩ :=
        isSquare_mul_of_not_isSquare (mul_ne_zero hv₀ hw₀) (mul_ne_zero hv₀ hv) hns h1
      refine (reflectClass_eq_of_isSquare h2 hw₀ hv ⟨c / Q v₀, ?_⟩).symm
      field_simp
      linear_combination hc
  · push Not at h
    by_cases h' : ∃ v, Q v ≠ 0
    · obtain ⟨v₀, hv₀⟩ := h'
      exact ⟨reflectClass Q v₀, reflectClass Q v₀, reflectClass_sq _, reflectClass_sq _,
        fun v hv => Or.inl (reflectClass_eq_of_isSquare h2 hv₀ hv (h v₀ hv₀ v hv)).symm⟩
    · push Not at h'
      exact ⟨1, 1, one_pow _, one_pow _, fun v hv => absurd (h' v) hv⟩

theorem odd_orthogonal_abelianization_order_bound [Finite K] [FiniteDimensional K V]
    (hK : ringChar K ≠ 2) (hQ : (polarBilin Q).Nondegenerate) :
    CFSG.IsElementaryAbelian 2 (Abelianization (TauCeti.QuadraticMap.orthogonalGroup Q)) ∧
      Nat.card (Abelianization (TauCeti.QuadraticMap.orthogonalGroup Q)) ≤ 4 ∧
      ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ ≤
        TauCeti.QuadraticMap.specialOrthogonalGroup Q ∧
      (⁅TauCeti.QuadraticMap.orthogonalGroup Q,
          TauCeti.QuadraticMap.orthogonalGroup Q⁆.subgroupOf
        (TauCeti.QuadraticMap.specialOrthogonalGroup Q)).index ≤ 2 := by
  set O := TauCeti.QuadraticMap.orthogonalGroup Q
  set SO := TauCeti.QuadraticMap.specialOrthogonalGroup Q
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  obtain ⟨x₁, x₂, hx₁, hx₂, hx⟩ := exists_reflectClass_two_values (Q := Q) h2
  set f : Fin 4 → Abelianization O := ![1, x₁, x₂, x₁ * x₂]
  have hprod : ∀ l : List V, (∀ v ∈ l, Q v ≠ 0) → ∀ hl : (l.map (reflect Q)).prod ∈ O,
      ∃ i, f i = Abelianization.of ⟨(l.map (reflect Q)).prod, hl⟩ := by
    intro l
    induction l with
    | nil =>
      intro _ _
      exact ⟨0, (map_one Abelianization.of).symm⟩
    | cons v l ih =>
      intro hvl hl
      have hlO : (l.map (reflect Q)).prod ∈ O :=
        list_prod_mem fun g hg => by
          obtain ⟨w, -, rfl⟩ := List.mem_map.1 hg
          exact reflect_mem_orthogonalGroup Q w
      obtain ⟨i, hi⟩ := ih (fun w hw => hvl w (List.mem_cons_of_mem v hw)) hlO
      have e : (⟨((v :: l).map (reflect Q)).prod, hl⟩ : O) =
          ⟨reflect Q v, reflect_mem_orthogonalGroup Q v⟩ * ⟨(l.map (reflect Q)).prod, hlO⟩ :=
        Subtype.ext (by
          change ((v :: l).map (reflect Q)).prod = reflect Q v * (l.map (reflect Q)).prod
          rw [List.map_cons, List.prod_cons])
      rw [e, map_mul, ← hi]
      exact exists_fin_four_eq_mul hx₁ hx₂ (hx v (hvl v List.mem_cons_self)) i
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨⟨g, hg⟩, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨l, -, hl, rfl⟩ := orthogonal_odd_reflection_generation hK hQ hg
    exact hprod l hl hg
  have hcard : Nat.card (Abelianization O) ≤ 4 :=
    (Nat.card_le_card_of_surjective f hsurj).trans_eq (Nat.card_fin 4)
  have hexp : ∀ y : Abelianization O, y ^ 2 = 1 := by
    intro y
    obtain ⟨i, rfl⟩ := hsurj y
    fin_cases i
    · exact one_pow 2
    · exact hx₁
    · exact hx₂
    · change (x₁ * x₂) ^ 2 = 1
      rw [mul_pow, hx₁, hx₂, one_mul]
  have hΩ : ⁅O, O⁆ ≤ SO := by
    rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    rw [TauCeti.QuadraticMap.mem_specialOrthogonalGroup_iff]
    refine ⟨?_, ?_⟩
    · rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hg₁ hg₂) (inv_mem hg₁)) (inv_mem hg₂)
    · rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm, mul_comm]
  have hEA : CFSG.IsElementaryAbelian 2 (Abelianization O) :=
    { is_comm := ⟨mul_comm⟩, exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one hexp }
  refine ⟨hEA, hcard, hΩ, ?_⟩
  rcases subsingleton_or_nontrivial V with hV | hV
  · have : Subsingleton (V ≃ₗ[K] V) :=
      ⟨fun g₁ g₂ => LinearEquiv.ext fun x => Subsingleton.elim _ _⟩
    refine le_of_eq_of_le (Subgroup.index_eq_one.2 ?_) one_le_two
    exact eq_top_iff.2 fun x _ => by
      rw [Subsingleton.elim x 1]
      exact one_mem _
  · have : NeZero (2 : K) := ⟨h2⟩
    let _ : Invertible (2 : K) := invertibleOfNonzero h2
    have hQ' : Q.Nondegenerate := QuadraticMap.nondegenerate_polar_iff.mp hQ
    have hSO : (SO.subgroupOf O).index = 2 := by
      rw [← QuadraticMap.specialOrthogonalWithin_eq_subgroupOf]
      exact TauCeti.QuadraticMap.index_specialOrthogonalWithin hQ'
    have hcomm : ⁅O, O⁆.subgroupOf O = commutator O := by
      rw [← Subgroup.map_subtype_commutator, Subgroup.subgroupOf,
        Subgroup.comap_map_eq_self_of_injective O.subtype_injective]
    have hmul := Subgroup.relIndex_mul_index (Subgroup.subgroupOf_mono O hΩ)
    rw [Subgroup.relIndex_subgroupOf (TauCeti.QuadraticMap.specialOrthogonalGroup_le_orthogonalGroup
      Q), hSO, hcomm, Subgroup.index_eq_card] at hmul
    change ⁅O, O⁆.relIndex SO ≤ 2
    change ⁅O, O⁆.relIndex SO * 2 = Nat.card (Abelianization O) at hmul
    omega

end CFSG.LocalAnalysis.ComponentInitial
