module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.SpinorNorm.Basic
import TauCeti.Algebra.Group.Units.Basic
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LieType.Universal.SpinOmega.Reflections

public section

namespace CFSG.ClassicalInvolution

open TauCeti QuadraticMap CliffordAlgebra CFSG.ClassicalGroups.Orthogonal
  CFSG.LieType.Universal.Spin
open scoped commutatorElement

section Helpers

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem map_hypPair_add_smul {Q : QuadraticForm K V} (P : HypPair Q) (c : K) :
    Q (P.e + c • P.f) = c := by
  rw [QuadraticMap.map_add Q, map_smul_eq_sq, polar_smul_right_eq, P.Q_e, P.Q_f, P.polar_ef]
  ring

instance finite_orthogonalGroup_of_finite [Finite K] [FiniteDimensional K V]
    {Q : QuadraticForm K V} :
    Finite (TauCeti.QuadraticMap.orthogonalGroup Q) := by
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) :=
    Finite.of_injective (fun g : V ≃ₗ[K] V => g.toEquiv)
      (fun g h hgh => LinearEquiv.ext fun x => by simpa using congrArg (fun e : V ≃ V => e x) hgh)
  infer_instance

theorem exists_sq_or_sq_mul_of_ne_zero [Finite K] {ν : K} (hν : ¬ IsSquare ν) {x : K}
    (hx : x ≠ 0) : ∃ t : K, t ≠ 0 ∧ (x = t ^ 2 ∨ x = t ^ 2 * ν) := by
  classical
  have := Fintype.ofFinite K
  by_cases hsq : IsSquare x
  · obtain ⟨r, hr⟩ := hsq
    have hr0 : r ≠ 0 := by
      rintro rfl
      exact hx (by simpa using hr)
    exact ⟨r, hr0, Or.inl (by rw [hr]; ring)⟩
  · have hν0 : ν ≠ 0 := fun h => hν (by rw [h]; exact ⟨0, by simp⟩)
    have h1 : quadraticChar K (x * ν) = 1 := by
      rw [map_mul, quadraticChar_neg_one_iff_not_isSquare.2 hsq,
        quadraticChar_neg_one_iff_not_isSquare.2 hν]
      norm_num
    obtain ⟨r, hr⟩ := (quadraticChar_one_iff_isSquare (mul_ne_zero hx hν0)).1 h1
    have hr0 : r ≠ 0 := by
      rintro rfl
      exact mul_ne_zero hx hν0 (by simpa using hr)
    refine ⟨r / ν, div_ne_zero hr0 hν0, Or.inr ?_⟩
    field_simp
    linear_combination hr

end Helpers

section GroupLemma

variable {G : Type*} [Group G]

theorem eq_one_or_eq_or_eq_mul_of_mem_closure_pair {a b : G} (haa : a * a = 1) (hbb : b * b = 1)
    (hab : a * b = b * a) {x : G} (hx : x ∈ Subgroup.closure ({a, b} : Set G)) :
    x = 1 ∨ x = a ∨ x = b ∨ x = a * b := by
  have e1 : a * (a * b) = b := by rw [← mul_assoc, haa, one_mul]
  have e2 : b * (a * b) = a := by rw [hab, ← mul_assoc, hbb, one_mul]
  have e3 : (a * b) * a = b := by rw [mul_assoc, ← hab, ← mul_assoc, haa, one_mul]
  have e4 : (a * b) * b = a := by rw [mul_assoc, hbb, mul_one]
  have e5 : (a * b) * (a * b) = 1 := by rw [← mul_assoc, e3, hbb]
  have ia : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  have ib : b⁻¹ = b := inv_eq_of_mul_eq_one_right hbb
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
  | one => exact Or.inl rfl
  | mul x y _ _ hx hy =>
    rcases hx with hx | hx | hx | hx <;> rcases hy with hy | hy | hy | hy <;> subst hx hy
    · simp
    · simp
    · simp
    · simp
    · simp
    · simp [haa]
    · simp
    · simp [e1]
    · simp
    · simp [hab.symm]
    · simp [hbb]
    · simp [e2]
    · simp
    · simp [e3]
    · simp [e4]
    · simp [e5]
  | inv x _ hx =>
    rcases hx with hx | hx | hx | hx <;> subst hx
    · simp
    · simp [ia]
    · simp [ib]
    · simp [mul_inv_rev, ia, ib, hab.symm]

end GroupLemma

section Index

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

omit [FiniteDimensional K V] in
theorem coe_reflectionOrthogonal_eq_reflect (v : V) [Invertible (Q v)] :
    ((TauCeti.QuadraticMap.reflectionOrthogonal Q v :
      TauCeti.QuadraticMap.orthogonalGroup Q) : V ≃ₗ[K] V) = reflect Q v := by
  rw [TauCeti.QuadraticMap.coe_reflectionOrthogonal, reflect_eq_reflection]

variable [Finite K] [Invertible (2 : K)]

@[expose] noncomputable def detSpinorNorm (hQ : Q.Nondegenerate) :
    ↥(TauCeti.QuadraticMap.orthogonalGroup Q) →* Kˣ × Multiplicative (SquareClassGroup K) :=
  (QuadraticMap.orthogonalDet Q).prod (orthogonalSpinorNorm Q hQ)

theorem detSpinorNorm_apply (hQ : Q.Nondegenerate) (g : TauCeti.QuadraticMap.orthogonalGroup Q) :
    detSpinorNorm hQ g = (QuadraticMap.orthogonalDet Q g, orthogonalSpinorNorm Q hQ g) :=
  rfl

theorem detSpinorNorm_reflectionOrthogonal (hQ : Q.Nondegenerate) (v : V) [Invertible (Q v)] :
    detSpinorNorm hQ (TauCeti.QuadraticMap.reflectionOrthogonal Q v) =
      (-1, squareClassHom (unitOfInvertible (Q v))) := by
  simp [detSpinorNorm, orthogonalSpinorNorm_reflectionOrthogonal]


theorem orthogonalGroup_index_four (hQ : (polarBilin Q).Nondegenerate) {P₁ P₂ P₃ : HypPair Q}
    (h₁₂ : P₁.Orth P₂) (h₁₃ : P₁.Orth P₃) (h₂₃ : P₂.Orth P₃) :
    Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) = 4 * Nat.card (elementaryGroup Q) ∧
      ∀ g : TauCeti.QuadraticMap.orthogonalGroup Q,
        (g : V ≃ₗ[K] V) ∈ elementaryGroup Q ↔
          detSpinorNorm (QuadraticMap.nondegenerate_polar_iff.mp hQ) g = 1 := by
  classical
  have h2 : (2 : K) ≠ 0 := (isUnit_of_invertible (2 : K)).ne_zero
  have : NeZero (2 : K) := ⟨h2⟩
  have hQ' : Q.Nondegenerate := QuadraticMap.nondegenerate_polar_iff.mp hQ
  set O := TauCeti.QuadraticMap.orthogonalGroup Q with hO
  set E := elementaryGroup Q with hE
  have hEO : E ≤ O := elementaryGroup_le_orthogonalGroup Q
  have hcomm : ⁅O, O⁆ = E :=
    commutator_orthogonalGroup_eq_elementaryGroup_of_two_ne_zero h2 hQ h₁₂ h₁₃ h₂₃
  set E' : Subgroup O := E.subgroupOf O with hE'
  have hE'n : E'.Normal := elementaryGroup_subgroupOf_normal Q
  have hE'comm : E' = commutator O := by
    rw [hE', ← hcomm, ← Subgroup.map_subtype_commutator, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective O.subtype_injective]
  set Φ := detSpinorNorm hQ' with hΦ
  have hΦ1 : E' ≤ Φ.ker := by
    rw [hE'comm, commutator_def, Subgroup.commutator_le]
    intro g₁ _ g₂ _
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 (mul_comm (Φ g₁) (Φ g₂))
  have hring : ringChar K ≠ 2 := by
    intro h
    apply h2
    have := (ringChar.spec K 2).2 (by rw [h])
    exact_mod_cast this
  obtain ⟨ν, hν⟩ := FiniteField.exists_nonsquare hring
  have hν0 : ν ≠ 0 := fun h => hν (by rw [h]; exact ⟨0, by simp⟩)
  set v₁ : V := P₁.e + (1 : K) • P₁.f with hv₁def
  set vν : V := P₁.e + ν • P₁.f with hvνdef
  have hv₁ : Q v₁ = 1 := map_hypPair_add_smul P₁ 1
  have hvν : Q vν = ν := map_hypPair_add_smul P₁ ν
  have inv1 : Invertible (Q v₁) := invertibleOfNonzero (by rw [hv₁]; exact one_ne_zero)
  have invν : Invertible (Q vν) := invertibleOfNonzero (by rw [hvν]; exact hν0)
  set s₁ : O := TauCeti.QuadraticMap.reflectionOrthogonal Q v₁ with hs₁def
  set sν : O := TauCeti.QuadraticMap.reflectionOrthogonal Q vν with hsνdef
  have hs₁ : s₁ * s₁ = 1 := TauCeti.QuadraticMap.reflectionOrthogonal_mul_self Q v₁
  have hsν : sν * sν = 1 := TauCeti.QuadraticMap.reflectionOrthogonal_mul_self Q vν
  set π : O →* O ⧸ E' := QuotientGroup.mk' E' with hπ
  set a : O ⧸ E' := π s₁ with ha
  set b : O ⧸ E' := π sν with hb
  have haa : a * a = 1 := by rw [ha, ← map_mul, hs₁, map_one]
  have hbb : b * b = 1 := by rw [hb, ← map_mul, hsν, map_one]
  have hab : a * b = b * a := by
    have hc : ⁅(s₁ : V ≃ₗ[K] V), (sν : V ≃ₗ[K] V)⁆ ∈ E := by
      have := commutatorElement_reflect_mem hQ h₁₂ v₁ vν
      rwa [← coe_reflectionOrthogonal_eq_reflect v₁, ← coe_reflectionOrthogonal_eq_reflect vν]
        at this
    have hc' : ⁅s₁, sν⁆ ∈ E' := by
      rw [hE', Subgroup.mem_subgroupOf]
      simpa [commutatorElement_def] using hc
    have h1 : π ⁅s₁, sν⁆ = 1 := (QuotientGroup.eq_one_iff _).2 hc'
    rw [map_commutatorElement] at h1
    exact (commutatorElement_eq_one_iff_mul_comm.1 h1)
  have hrefl : ∀ (v : V) [Invertible (Q v)],
      π (TauCeti.QuadraticMap.reflectionOrthogonal Q v) = a ∨
        π (TauCeti.QuadraticMap.reflectionOrthogonal Q v) = b := by
    intro v _
    have hv0 : Q v ≠ 0 := (isUnit_of_invertible (Q v)).ne_zero
    have hinv : (TauCeti.QuadraticMap.reflectionOrthogonal Q v)⁻¹ =
        TauCeti.QuadraticMap.reflectionOrthogonal Q v :=
      TauCeti.QuadraticMap.reflectionOrthogonal_inv Q v
    obtain ⟨t, ht, h | h⟩ := exists_sq_or_sq_mul_of_ne_zero hν hv0
    · left
      have hmem := reflect_mul_reflect_mem_of_eq_sq_mul hQ h₁₂ (a := v) (b := v₁)
        (by rw [hv₁]; exact one_ne_zero) ht (by rw [h, hv₁, mul_one])
      rw [ha, hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, hinv,
        hE', Subgroup.mem_subgroupOf, Subgroup.coe_mul, coe_reflectionOrthogonal_eq_reflect v,
        hs₁def, coe_reflectionOrthogonal_eq_reflect v₁]
      exact hmem
    · right
      have hmem := reflect_mul_reflect_mem_of_eq_sq_mul hQ h₁₂ (a := v) (b := vν)
        (by rw [hvν]; exact hν0) ht (by rw [h, hvν])
      rw [hb, hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, hinv,
        hE', Subgroup.mem_subgroupOf, Subgroup.coe_mul, coe_reflectionOrthogonal_eq_reflect v,
        hsνdef, coe_reflectionOrthogonal_eq_reflect vν]
      exact hmem
  have hgen : ∀ x : O ⧸ E', x = 1 ∨ x = a ∨ x = b ∨ x = a * b := by
    set H : Subgroup O := (Subgroup.closure ({a, b} : Set (O ⧸ E'))).comap π with hH
    have hHtop : H = ⊤ := by
      refine TauCeti.QuadraticMap.subgroup_eq_top_of_reflection_mem Q hQ' H ?_
      intro v _
      rw [hH, Subgroup.mem_comap]
      rcases hrefl v with h | h <;> rw [h] <;> exact Subgroup.subset_closure (by simp)
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    have hg : g ∈ H := by rw [hHtop]; exact Subgroup.mem_top g
    exact eq_one_or_eq_or_eq_mul_of_mem_closure_pair haa hbb hab (Subgroup.mem_comap.1 hg)
  let Ψ : O ⧸ E' →* Kˣ × Multiplicative (SquareClassGroup K) := QuotientGroup.lift E' Φ hΦ1
  have hΨ : ∀ g : O, Ψ (π g) = Φ g := fun g => rfl
  have hu₁ : unitOfInvertible (Q v₁) = 1 := Units.ext (by simp [hv₁])
  have hΦs₁ : Φ s₁ = (-1, 1) := by
    rw [hs₁def, hΦ, detSpinorNorm_reflectionOrthogonal, hu₁, map_one]
  have hσν : squareClassHom (unitOfInvertible (Q vν)) ≠ 1 := by
    intro h
    have h1 : unitOfInvertible (Q vν) ∈ (squareClassHom (K := K)).ker := h
    rw [ker_squareClassHom, Subgroup.mem_square, ← isSquare_units_val_iff] at h1
    exact hν (by simpa [hvν] using h1)
  have hΦsν : Φ sν = (-1, squareClassHom (unitOfInvertible (Q vν))) := by
    rw [hsνdef, hΦ, detSpinorNorm_reflectionOrthogonal]
  have hneg : (-1 : Kˣ) ≠ 1 := by
    intro h
    apply h2
    have := congrArg (fun u : Kˣ => (u : K)) h
    simp only [Units.val_neg, Units.val_one] at this
    linear_combination -this
  have hΨa : Ψ a = (-1, 1) := by rw [ha, hΨ, hΦs₁]
  have hΨb : Ψ b = (-1, squareClassHom (unitOfInvertible (Q vν))) := by rw [hb, hΨ, hΦsν]
  have hΨab : Ψ (a * b) = (1, squareClassHom (unitOfInvertible (Q vν))) := by
    rw [map_mul, hΨa, hΨb]
    ext
    · simp
    · simp
  have hΨinj : Function.Injective Ψ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    rcases hgen x with rfl | rfl | rfl | rfl
    · rfl
    · rw [hΨa] at hx
      exact absurd (congrArg Prod.fst hx) hneg
    · rw [hΨb] at hx
      exact absurd (congrArg Prod.fst hx) hneg
    · rw [hΨab] at hx
      exact absurd (congrArg Prod.snd hx) hσν
  have d1a : (1 : O ⧸ E') ≠ a := fun h => by
    have := congrArg Ψ h
    rw [map_one, hΨa] at this
    exact hneg (congrArg Prod.fst this).symm
  have d1b : (1 : O ⧸ E') ≠ b := fun h => by
    have := congrArg Ψ h
    rw [map_one, hΨb] at this
    exact hneg (congrArg Prod.fst this).symm
  have d1ab : (1 : O ⧸ E') ≠ a * b := fun h => by
    have := congrArg Ψ h
    rw [map_one, hΨab] at this
    exact hσν (congrArg Prod.snd this).symm
  have dab : a ≠ b := fun h => by
    have := congrArg Ψ h
    rw [hΨa, hΨb] at this
    exact hσν (congrArg Prod.snd this).symm
  have daab : a ≠ a * b := fun h => by
    have := congrArg Ψ h
    rw [hΨa, hΨab] at this
    exact hneg (congrArg Prod.fst this)
  have dbab : b ≠ a * b := fun h => by
    have := congrArg Ψ h
    rw [hΨb, hΨab] at this
    exact hneg (congrArg Prod.fst this)
  have hcard4 : Nat.card (O ⧸ E') = 4 := by
    have huniv : (Set.univ : Set (O ⧸ E')) = {1, a, b, a * b} := by
      ext x
      simp only [Set.mem_univ, Set.mem_insert_iff, Set.mem_singleton_iff, true_iff]
      exact hgen x
    rw [← Set.ncard_univ, huniv, Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem,
      Set.ncard_pair dbab]
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨dab, daab⟩
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨d1a, d1b, d1ab⟩
  have hker : ∀ g : O, Φ g = 1 → g ∈ E' := by
    intro g hg
    have : π g = 1 := hΨinj (by rw [hΨ, hg, map_one])
    exact (QuotientGroup.eq_one_iff _).1 this
  refine ⟨?_, fun g => ⟨fun hg => MonoidHom.mem_ker.1 (hΦ1 (Subgroup.mem_subgroupOf.2 hg)),
    fun hg => Subgroup.mem_subgroupOf.1 (hker g hg)⟩⟩
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup E'
  rw [hcard4, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEO).toEquiv] at hcard
  exact hcard

end Index

end CFSG.ClassicalInvolution
