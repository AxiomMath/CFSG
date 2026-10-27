module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness

public noncomputable section

namespace CFSG.EvenSmallLie.Child3.SelOmega

open QuadraticMap Module CFSG.ClassicalGroups.Orthogonal

section TwoElements

variable {K : Type*} [Field K]

theorem eq_zero_or_eq_one_of_card_eq_two (hK : Nat.card K = 2) (a : K) : a = 0 ∨ a = 1 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have : Fintype K := Fintype.ofFinite K
  have h := FiniteField.pow_card a
  rw [Fintype.card_eq_nat_card, hK] at h
  have h2 : a * (a - 1) = 0 := by rw [mul_sub, mul_one, ← _root_.sq, h, sub_self]
  rcases mul_eq_zero.mp h2 with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (sub_eq_zero.mp h1)

theorem charP_two_of_card_eq_two (hK : Nat.card K = 2) : CharP K 2 := by
  refine CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero ?_
  rcases eq_zero_or_eq_one_of_card_eq_two hK (2 : K) with h | h
  · exact h
  · exact absurd (by linear_combination h) (one_ne_zero (α := K))

theorem units_eq_one_of_card_eq_two (hK : Nat.card K = 2) (c : Kˣ) : c = 1 := by
  rcases eq_zero_or_eq_one_of_card_eq_two hK (c : K) with h | h
  · exact absurd h c.ne_zero
  · exact Units.ext h

end TwoElements

section Singular

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem exists_ne_zero_map_eq_zero (hK : Nat.card K = 2) (Q : QuadraticForm K V)
    (U : Submodule K V) [FiniteDimensional K U] (hU : 3 ≤ finrank K U) :
    ∃ u ∈ U, u ≠ 0 ∧ Q u = 0 := by
  set b := Module.finBasis K U
  set v : Fin (finrank K U) → V := fun i => (b i : V) with hv
  have hli : LinearIndependent K v := b.linearIndependent.map' U.subtype (Submodule.ker_subtype U)
  have hmem : ∀ i, v i ∈ U := fun i => (b i).2
  have hsum : ∀ s : Finset (Fin (finrank K U)), s.Nonempty → ∑ i ∈ s, v i ≠ 0 := by
    intro s hs h0
    obtain ⟨i, hi⟩ := hs
    have h := linearIndependent_iff'.mp hli s (fun _ => 1) (by simpa using h0) i hi
    exact one_ne_zero h
  set i0 : Fin (finrank K U) := ⟨0, by omega⟩
  set i1 : Fin (finrank K U) := ⟨1, by omega⟩
  set i2 : Fin (finrank K U) := ⟨2, by omega⟩
  have h01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  have h02 : i0 ≠ i2 := by simp [i0, i2, Fin.ext_iff]
  have h12 : i1 ≠ i2 := by simp [i1, i2, Fin.ext_iff]
  have hne : ∀ s : Finset (Fin (finrank K U)), s.Nonempty → ∑ i ∈ s, v i ∈ U :=
    fun s _ => U.sum_mem fun i _ => hmem i
  by_contra hcon
  push Not at hcon
  have h1 : ∀ u ∈ U, u ≠ 0 → Q u = 1 := fun u hu h0 =>
    (eq_zero_or_eq_one_of_card_eq_two hK (Q u)).resolve_left (hcon u hu h0)
  have e0 := h1 _ (hmem i0) (by simpa using hsum {i0} (by simp))
  have e1 := h1 _ (hmem i1) (by simpa using hsum {i1} (by simp))
  have e2 := h1 _ (hmem i2) (by simpa using hsum {i2} (by simp))
  have e01 := h1 (v i0 + v i1) (U.add_mem (hmem _) (hmem _))
    (by simpa [Finset.sum_pair h01] using hsum {i0, i1} (by simp))
  have e12 := h1 (v i1 + v i2) (U.add_mem (hmem _) (hmem _))
    (by simpa [Finset.sum_pair h12] using hsum {i1, i2} (by simp))
  have e20 := h1 (v i2 + v i0) (U.add_mem (hmem _) (hmem _))
    (by simpa [Finset.sum_pair h02.symm] using hsum {i2, i0} (by simp))
  have e012 : Q (v i0 + v i1 + v i2) = 1 := by
    refine h1 _ (U.add_mem (U.add_mem (hmem _) (hmem _)) (hmem _)) ?_
    have h := hsum {i0, i1, i2} (by simp)
    rwa [Finset.sum_insert (by simp [h01, h02]), Finset.sum_pair h12, ← add_assoc] at h
  have key := QuadraticMap.map_add_add_add_map Q (v i0) (v i1) (v i2)
  rw [e0, e1, e2, e01, e12, e20, e012] at key
  exact one_ne_zero (by linear_combination key)

end Singular

section Kernels

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem finrank_le_finrank_ker_add_finrank_ker {f g : V →ₗ[K] V} (h : g ∘ₗ f = 0) :
    finrank K V ≤ finrank K (LinearMap.ker f) + finrank K (LinearMap.ker g) := by
  have h1 := LinearMap.finrank_range_add_finrank_ker f
  have h2 : LinearMap.range f ≤ LinearMap.ker g := by
    rintro _ ⟨v, rfl⟩
    rw [LinearMap.mem_ker, ← LinearMap.comp_apply, h, LinearMap.zero_apply]
  have h3 := Submodule.finrank_mono h2
  omega

theorem finrank_inf_ker_ge (A : Submodule K V) (φ : V →ₗ[K] K) :
    finrank K A ≤ finrank K ↥(A ⊓ LinearMap.ker φ) + 1 := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq A (LinearMap.ker φ)
  have h2 := LinearMap.finrank_range_add_finrank_ker φ
  have h3 : finrank K (LinearMap.range φ) ≤ 1 := by
    have := Submodule.finrank_le (LinearMap.range φ)
    rwa [Module.finrank_self] at this
  have h4 := Submodule.finrank_le (A ⊔ LinearMap.ker φ)
  omega

omit [FiniteDimensional K V] in
theorem exists_mem_forall_ne_smul (A : Submodule K V) (hA : 2 ≤ finrank K A) (e : V) :
    ∃ y ∈ A, ∀ c : K, y ≠ c • e := by
  by_contra h
  push Not at h
  have hle : A ≤ K ∙ e := fun y hy => by
    obtain ⟨c, hc⟩ := h y hy
    exact Submodule.mem_span_singleton.mpr ⟨c, hc.symm⟩
  have h1 := Submodule.finrank_mono hle
  have h2 := finrank_span_le_card (R := K) ({e} : Set V)
  simp only [Set.toFinset_singleton, Finset.card_singleton] at h2
  omega

end Kernels

section Eichler

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem eichler_ne_one (hQ : (polarBilin Q).Nondegenerate) {u w : V} (hu : Q u = 0)
    (hw : polar Q u w = 0) (hu0 : u ≠ 0) (hwu : ∀ c : K, w ≠ c • u) : eichler Q u w ≠ 1 := by
  intro h1
  obtain ⟨y, hy⟩ := exists_polar_ne_zero hQ hu0
  have hyu : polar Q y u ≠ 0 := by rwa [polar_comm]
  have h : eichler Q u w y = y := by rw [h1]; rfl
  rw [eichler_apply hu hw, add_sub_assoc, add_eq_left, sub_eq_zero] at h
  apply hwu ((polar Q y u)⁻¹ * (polar Q y w + Q w * polar Q y u))
  rw [← smul_smul, ← h, smul_smul, inv_mul_cancel₀ hyu, one_smul]

theorem eichler_mul_self [CharP K 2] {u w : V} (hw : polar Q u w = 0) :
    eichler Q u w * eichler Q u w = 1 := by
  rw [eichler_mul hw hw, ← two_smul K w, CharTwo.two_eq_zero, zero_smul, eichler_zero_right]

theorem eichler_neg_swap {u w : V} (hu : Q u = 0) (hw : Q w = 0) (huw : polar Q u w = 0) :
    eichler Q w (-u) = eichler Q u w := by
  have hwu : polar Q w (-u) = 0 := by rw [polar_neg_right, polar_comm, huw, neg_zero]
  refine LinearEquiv.ext fun x => ?_
  rw [eichler_apply hw hwu, eichler_apply hu huw, polar_neg_right, QuadraticMap.map_neg, hu, hw]
  module

end Eichler

section Isometry

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

theorem exists_eichler_commute (hK : Nat.card K = 2) (hQ : (polarBilin Q).Nondegenerate)
    (hV : 6 ≤ finrank K V) {X : V ≃ₗ[K] V} (hX : X ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hX3 : ∀ v, X (X (X v)) = v) :
    ∃ u w : V, Q u = 0 ∧ polar Q u w = 0 ∧ eichler Q u w ≠ 1 ∧
      X * eichler Q u w = eichler Q u w * X := by
  have : CharP K 2 := charP_two_of_card_eq_two hK
  set N₁ : V →ₗ[K] V := X.toLinearMap - LinearMap.id with hN₁
  set N₂ : V →ₗ[K] V := X.toLinearMap ∘ₗ X.toLinearMap + X.toLinearMap + LinearMap.id with hN₂
  have hcomp : N₁ ∘ₗ N₂ = 0 := by
    refine LinearMap.ext fun v => ?_
    simp only [hN₁, hN₂, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.add_apply,
      LinearEquiv.coe_coe, LinearMap.id_apply, map_add, hX3, LinearMap.zero_apply]
    abel
  have hdim := finrank_le_finrank_ker_add_finrank_ker hcomp
  rcases (show 3 ≤ finrank K (LinearMap.ker N₁) ∨ 3 ≤ finrank K (LinearMap.ker N₂) by omega)
    with h1 | h2
  ·
    obtain ⟨e, he, he0, hQe⟩ := exists_ne_zero_map_eq_zero hK Q (LinearMap.ker N₁) h1
    have hfix : ∀ v ∈ LinearMap.ker N₁, X v = v := fun v hv => by
      rw [LinearMap.mem_ker, hN₁, LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply,
        sub_eq_zero] at hv
      exact hv
    have hA := finrank_inf_ker_ge (LinearMap.ker N₁) (polarBilin Q e)
    obtain ⟨y, hy, hye⟩ := exists_mem_forall_ne_smul _ (by omega : 2 ≤ finrank K
      ↥(LinearMap.ker N₁ ⊓ LinearMap.ker (polarBilin Q e))) e
    have hpol : polar Q e y = 0 := (Submodule.mem_inf.mp hy).2
    refine ⟨e, y, hQe, hpol, eichler_ne_one hQ hQe hpol he0 hye, ?_⟩
    have hconj := eichler_conj hX e y
    rw [hfix e he, hfix y (Submodule.mem_inf.mp hy).1] at hconj
    exact mul_inv_eq_iff_eq_mul.mp hconj
  ·
    obtain ⟨w, hw, hw0, hQw⟩ := exists_ne_zero_map_eq_zero hK Q (LinearMap.ker N₂) h2
    have hN : X (X w) + X w + w = 0 := by
      rw [LinearMap.mem_ker, hN₂] at hw
      simpa using hw
    have hQXw : Q (X w) = 0 := by rw [map_of_mem hX, hQw]
    have hXX : X (X w) = -w + (-1 : K) • X w := by
      have h0 : X (X w) + (X w + w) = 0 := by rw [← add_assoc]; exact hN
      rw [eq_neg_of_add_eq_zero_left h0, neg_one_smul, neg_add, add_comm]
    have hpol : polar Q w (X w) = 0 := by
      have h1 : Q (X (X w)) = 0 := by rw [map_of_mem hX, map_of_mem hX, hQw]
      rw [hXX, QuadraticMap.map_add Q, QuadraticMap.map_neg, hQw, map_smul_eq_sq, hQXw,
        polar_neg_left, polar_smul_right_eq] at h1
      have h2 : polar Q w (X w) = 0 := by linear_combination h1
      exact h2
    refine ⟨w, X w, hQw, hpol, eichler_ne_one hQ hQw hpol hw0 fun c hc => ?_, ?_⟩
    · have h3 : (c ^ 2 + c + 1) • w = 0 := by
        rw [← hN, hc, map_smul, hc, smul_smul]
        module
      rcases smul_eq_zero.mp h3 with h4 | h4
      · rcases eq_zero_or_eq_one_of_card_eq_two hK c with rfl | rfl
        · exact one_ne_zero (by linear_combination h4)
        · exact one_ne_zero (by linear_combination h4 - CharTwo.two_eq_zero (R := K))
      · exact hw0 h4
    · have hconj := eichler_conj hX w (X w)
      rw [hXX, eichler_add_smul_self hQXw, eichler_neg_swap hQw hQXw hpol] at hconj
      exact mul_inv_eq_iff_eq_mul.mp hconj

end Isometry

section Matrix

open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear

variable {K : Type} [Field K] {d : ℕ}

theorem map_matrixDerived (Q : QuadraticForm K (Fin d → K)) :
    (matrixDerived Q).map (matrixLinearIso (d := d) (K := K)).toMonoidHom =
      ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
  rw [matrixDerived, Subgroup.map_commutator, matrixIsometries,
    Subgroup.map_comap_eq_self_of_surjective (matrixLinearIso (d := d) (K := K)).surjective]

theorem matrixProjectiveProjection_injective (hK : Nat.card K = 2)
    (Q : QuadraticForm K (Fin d → K)) :
    Function.Injective (matrixProjectiveProjection Q) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hmem : g ∈ matrixDerivedScalars Q := by
    rw [← QuotientGroup.ker_mk' (matrixDerivedScalars Q)]
    exact hg
  obtain ⟨c, hc⟩ := (mem_matrixDerivedScalars_iff Q g).mp hmem
  rw [units_eq_one_of_card_eq_two hK c, map_one] at hc
  exact Subtype.ext hc.symm

theorem exists_orderOf_eq_two_commute_matrixProjectiveDerived (hK : Nat.card K = 2)
    (Q : QuadraticForm K (Fin d → K)) (hQ : (polarBilin Q).Nondegenerate) (hd : 6 ≤ d)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q)
    (y : matrixProjectiveDerived Q) (hy : orderOf y = 3) :
    ∃ u : matrixProjectiveDerived Q, orderOf u = 2 ∧ Commute u y := by
  have : CharP K 2 := charP_two_of_card_eq_two hK
  have hinj := matrixProjectiveProjection_injective hK Q
  obtain ⟨g, rfl⟩ := matrixProjectiveProjection_surjective Q y
  have hg3 : g ^ 3 = 1 := by
    rw [orderOf_injective _ hinj g] at hy
    rw [← hy, pow_orderOf_eq_one]
  set X := matrixLinearIso (d := d) (K := K) (g : GL (Fin d) K) with hXdef
  have hX : X ∈ TauCeti.QuadraticMap.orthogonalGroup Q := matrixDerived_le_isometries Q g.2
  have hX3 : ∀ v, X (X (X v)) = v := fun v => by
    have h : X ^ 3 = 1 := by
      rw [hXdef, ← map_pow, ← Subgroup.coe_pow, hg3, Subgroup.coe_one, map_one]
    have h' := congrArg (fun F : (Fin d → K) ≃ₗ[K] (Fin d → K) => F v) h
    simpa [pow_succ] using h'
  obtain ⟨u, w, hu, hw, hne, hcomm⟩ :=
    exists_eichler_commute hK hQ (by rw [Module.finrank_fin_fun]; exact hd) hX hX3
  have hEmem : eichler Q u w ∈
      (matrixDerived Q).map (matrixLinearIso (d := d) (K := K)).toMonoidHom := by
    rw [map_matrixDerived, hE]
    exact eichler_mem_elementaryGroup Q u w
  obtain ⟨s, hs, hsE⟩ := hEmem
  refine ⟨matrixProjectiveProjection Q ⟨s, hs⟩, ?_, ?_⟩
  · rw [orderOf_injective _ hinj, ← orderOf_injective (matrixDerived Q).subtype
      Subtype.val_injective ⟨s, hs⟩]
    change orderOf s = 2
    rw [← MulEquiv.orderOf_eq (matrixLinearIso (d := d) (K := K)) s,
      show matrixLinearIso s = eichler Q u w from hsE]
    exact orderOf_eq_prime (by rw [pow_two]; exact eichler_mul_self hw) hne
  · change _ * _ = _ * _
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    apply (matrixLinearIso (d := d) (K := K)).injective
    change matrixLinearIso (s * g.1) = matrixLinearIso (g.1 * s)
    rw [map_mul, map_mul, show matrixLinearIso s = eichler Q u w from hsE]
    exact hcomm.symm

end Matrix

section Model

open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatalogueBOrthogonalPointData

theorem exists_orderOf_eq_two_commute_of_POmega {T : Type} [Group T] {t : StatedLieTag}
    (ht : t = .POmegaPlus ∨ t = .POmegaMinus) {n : ℕ} (hT : StatedClassicalModel T t n 2 1)
    (x : T) (hx : orderOf x = 3) : ∃ u : T, orderOf u = 2 ∧ Commute u x := by
  rcases ht with rfl | rfl
  · obtain ⟨⟨-, -, hn⟩, K, _, _, hK, ⟨eT⟩⟩ := hT
    rw [pow_one] at hK
    have hreg := regular_coordinateQuadPlus n K (by omega)
    set e := coordinatePlusWitnessEquiv K eT
    obtain ⟨u, hu, hc⟩ := exists_orderOf_eq_two_commute_matrixProjectiveDerived hK _ hreg.1
      (by omega) (commutator_coordinateQuadPlus n K (by omega)) (e x)
      (by rw [MulEquiv.orderOf_eq]; exact hx)
    refine ⟨e.symm u, by rw [MulEquiv.orderOf_eq]; exact hu, ?_⟩
    have := hc.map e.symm.toMonoidHom
    simpa using this
  · obtain ⟨⟨-, -, hn⟩, K, _, _, hK, b, c, hirr, ⟨eT⟩⟩ := hT
    rw [pow_one] at hK
    have hreg := regular_coordinateQuadMinus n K b c hn hirr
    set e := coordinateMinusWitnessEquiv K (by omega) b c eT
    obtain ⟨u, hu, hc⟩ := exists_orderOf_eq_two_commute_matrixProjectiveDerived hK _ hreg.1
      (by omega) (commutator_coordinateQuadMinus n K b c hn hirr) (e x)
      (by rw [MulEquiv.orderOf_eq]; exact hx)
    refine ⟨e.symm u, by rw [MulEquiv.orderOf_eq]; exact hu, ?_⟩
    have := hc.map e.symm.toMonoidHom
    simpa using this

end Model

end CFSG.EvenSmallLie.Child3.SelOmega
