module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHighField
public import CFSG.LieType.SeitzGeneration.OuterOrthCat
public import CFSG.LieType.SeitzGeneration.OuterOrthThreeData
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.P3.OrthFix

open Matrix CFSG.Open CFSG.LieType.Seitz CFSG.LieType.SeitzGeneration CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.CTP CFSG.RankThree.PartOne.KCOrthogonalSubfield
  CFSG.RankThree.Classical.SteinbergBY CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBHigherLinearField
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHigh
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)
open CFSG.Assembly.LowTwoRank (StatedProj StatedOmega StatedQuadOdd StatedQuadMinus
  StatedLieAdmissible StatedLieTag StatedClassicalModel)
open CFSG.HardMathSupport.Lang.Proving (orthogonal_prime_semilinear_actual_fixed_form_descent')
open CFSG.RankThree.PartOne.KCOrthogonalAut (matrixProjectiveImage_eq_top_odd
  matrixProjectiveImage_eq_top_minus)
open CFSG.ClassicalGroups.Orthogonal (ringChar_eq_of_card_eq)

theorem center_eq_bot_of_orth_model {G : Type} [Group G] {c : StatedLieTag} {n ℓ f : ℕ}
    (hc : c = .POmegaOdd ∨ c = .POmegaPlus ∨ c = .POmegaMinus)
    (hM : StatedClassicalModel G c n ℓ f) : Subgroup.center G = ⊥ := by
  obtain ⟨-, hnt, hsimp, hperf⟩ := orth_facts_of_model hc hM
  rcases hsimp.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
  · exact h
  · exfalso
    have hcomm : ∀ a b : G, a * b = b * a := fun a b => by
      have ha : a ∈ Subgroup.center G := h ▸ Subgroup.mem_top a
      exact (Subgroup.mem_center_iff.1 ha b).symm
    exact Group.IsPerfect.not_isMulCommutative G ⟨⟨hcomm⟩⟩

private theorem conj_fixed {P : Type*} [Group P] {D F : MulAut P} {x : P} (hx : F x = x) :
    (D * F * D⁻¹) (D x) = D x := by
  simp only [MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply, hx]

theorem exists_fixed_model_coordOdd {n ℓ f p : ℕ} {K : Type} [Field K] [Finite K]
    (hadm : StatedLieAdmissible .POmegaOdd n ℓ f) (hK : Nat.card K = ℓ ^ f)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ)
    {α : MulAut (matrixProjectiveDerived (coordinateQuadOdd n K))} (hα : IsOuterOfOrder p α) :
    ∃ (M : Type) (_ : Group M) (e : ℕ), StatedClassicalModel M .POmegaOdd n ℓ e ∧
      ∃ ψ : M →* matrixProjectiveDerived (coordinateQuadOdd n K), Function.Injective ψ ∧
        ∀ m, α (ψ m) = ψ m := by
  classical
  obtain ⟨hℓ, hf, hn3, hℓ2⟩ := id hadm
  have hM : StatedClassicalModel (StatedProj (StatedOmega (StatedQuadOdd n K))) .POmegaOdd n ℓ f :=
    ⟨hadm, K, inferInstance, inferInstance, hK, ⟨MulEquiv.refl _⟩⟩
  have hg : OrthogonalGates (coordinateQuadOdd n K) f :=
    orthogonal_large_prime_semilinear_field_and_diagonal_gates _ .POmegaOdd (Or.inl rfl) n ℓ f hM
      K hK (MulEquiv.refl _)
  have h2K : ringChar K ≠ 2 := by
    rw [ringChar_eq_of_card_eq hℓ hf hK]
    exact hℓ2
  have htop := matrixProjectiveImage_eq_top_odd K n hn3 h2K
  obtain ⟨hE, hD⟩ := outer_mem_E_not_D_of_top hg htop hp hp2 hα
  have hdesc := orthogonal_prime_semilinear_actual_fixed_form_descent' _ .POmegaOdd (Or.inl rfl)
    n ℓ f p hM hp hp2 K hK (MulEquiv.refl _) α hE hD hα.1
  obtain ⟨D, -, σ, hσ, hαD⟩ := exists_conj_fieldAutT_of_descent _ hE hdesc
    (fun σ _ => coordinateQuadOdd_fieldAut n σ)
    (fun U Q₀ _ hdisp => by
      obtain ⟨ν, S₀, -, -, S, ν', hSQ, -, hSA, -⟩ := hdisp
      exact ⟨S, ν', hSQ, hSA⟩)
  obtain ⟨hpf, hcardk⟩ := card_semilinearFixedSubfield hℓ hf hK hσ
  obtain ⟨e, rfl⟩ := hpf
  have he : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with h0 | h0
    · rw [h0, mul_zero] at hf
      omega
    · exact h0
  rw [Nat.mul_div_cancel_left e hp.pos] at hcardk
  have hK' : Nat.card K = ℓ ^ (e * p) := by rw [hK, mul_comm]
  have hσk : ∀ x, x ∈ semilinearFixedSubfield σ ↔ σ x = x := fun x => RingHom.mem_eqLocusField
  have hadm0 : StatedLieAdmissible .POmegaOdd n ℓ e := ⟨hℓ, he, hn3, hℓ2⟩
  obtain ⟨-, hconc⟩ :=
    orthogonal_prime_subfield_fixed_group_and_full_centralizer_odd .POmegaOdd
      (Or.inl rfl) n ℓ e p hadm0 hp hp2 hpℓ K (semilinearFixedSubfield σ) hcardk hK' σ hσ hσk
  obtain ⟨⟨hinj, -, -⟩, -, hfixiff, hJN, -⟩ := hconc
  set k := semilinearFixedSubfield σ with hk
  have hkfin : Finite k := inferInstance
  have hM0 : StatedClassicalModel (matrixProjectiveDerived (coordinateQuadOdd n k))
      .POmegaOdd n ℓ e :=
    ⟨hadm0, k, inferInstance, inferInstance, hcardk,
      ⟨(coordinateOddWitnessEquiv (n := n) k (MulEquiv.refl _)).symm⟩⟩
  refine ⟨_, inferInstance, e, hM0,
    (D : MulAut _).toMonoidHom.comp (incl k (coordinateQuadOdd_isExtension k n)),
    D.injective.comp hinj, fun m => ?_⟩
  have hfix : fieldAutT (coordinateQuadOdd n K) σ (coordinateQuadOdd_fieldAut n σ)
      (incl k (coordinateQuadOdd_isExtension k n) m) =
      incl k (coordinateQuadOdd_isExtension k n) m :=
    (hfixiff _).2 (hJN ⟨m, rfl⟩)
  rw [hαD]
  exact conj_fixed hfix

theorem exists_fixed_model_of_odd {G : Type} [Group G] [Finite G] {n ℓ f p : ℕ}
    (hM : StatedClassicalModel G .POmegaOdd n ℓ f) (hp : p.Prime) (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ)
    {α : MulAut G} (hα : IsOuterOfOrder p α) :
    ∃ (M : Type) (_ : Group M) (e : ℕ), StatedClassicalModel M .POmegaOdd n ℓ e ∧
      ∃ ψ : M →* G, Function.Injective ψ ∧ ∀ m, α (ψ m) = ψ m := by
  obtain ⟨hadm, K, _, _, hK, ⟨e₀⟩⟩ := hM
  let θ : G ≃* matrixProjectiveDerived (coordinateQuadOdd n K) := coordinateOddWitnessEquiv K e₀
  obtain ⟨M, _, e, hM0, ψ, hψ, hfix⟩ :=
    exists_fixed_model_coordOdd hadm hK hp hp2 hpℓ (isOuterOfOrder_congr θ hα)
  refine ⟨M, inferInstance, e, hM0, θ.symm.toMonoidHom.comp ψ, θ.symm.injective.comp hψ,
    fun m => ?_⟩
  have h := hfix m
  rw [MulAut.congr_apply] at h
  change α (θ.symm (ψ m)) = θ.symm (ψ m)
  apply θ.injective
  rw [MulEquiv.apply_symm_apply]
  exact h

theorem exists_fixed_model_minus_rational {n ℓ e p : ℕ} {K : Type} [Field K] [Finite K]
    (hn : 4 ≤ n) (hn1 : 1 ≤ n) (hℓ : ℓ.Prime) (he : 1 ≤ e) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpℓ : p ≠ ℓ) {k : Subfield K} (hk : Nat.card k = ℓ ^ e) (hK : Nat.card K = ℓ ^ (e * p))
    {σ₀ : K ≃+* K} (hσ₀ : orderOf σ₀ = p) (hfix : ∀ x, x ∈ k ↔ σ₀ x = x) (b c : k)
    (hirr : ∀ s : k, s ^ 2 + b * s + c ≠ 0)
    {α : MulAut (matrixProjectiveDerived (coordinateQuadMinus n K hn1 (b : K) (c : K)))}
    (hα : IsOuterOfOrder p α) :
    ∃ (M : Type) (_ : Group M), StatedClassicalModel M .POmegaMinus n ℓ e ∧
      ∃ ψ : M →* matrixProjectiveDerived (coordinateQuadMinus n K hn1 (b : K) (c : K)),
        Function.Injective ψ ∧ ∀ m, α (ψ m) = ψ m := by
  classical
  have hf : 1 ≤ e * p := Nat.mul_pos he hp.pos
  have hfixall := fun σ (h : orderOf σ = p) => fixed_of_orderOf_orth hℓ he hp hK hσ₀ hfix h
  have hirrK : ∀ s : K, s ^ 2 + (b : K) * s + (c : K) ≠ 0 :=
    rootFree_of_odd_degree k hp hp2 (finrank_subfield_eq k hℓ he hk hK) b c hirr
  have hM : StatedClassicalModel
      (StatedProj (StatedOmega (StatedQuadMinus n K (b : K) (c : K)))) .POmegaMinus n ℓ (e * p) :=
    ⟨⟨hℓ, hf, hn⟩, K, inferInstance, inferInstance, hK, b, c, hirrK, ⟨MulEquiv.refl _⟩⟩
  have hg : OrthogonalGates (coordinateQuadMinus n K hn1 (b : K) (c : K)) (e * p) :=
    orthogonal_large_prime_semilinear_field_and_diagonal_gates _ .POmegaMinus
      (Or.inr (Or.inr rfl)) n ℓ (e * p) hM hn1 K hK b c hirrK (MulEquiv.refl _)
  have htop := matrixProjectiveImage_eq_top_minus K n hn (b : K) (c : K) hirrK
  obtain ⟨hE, hD⟩ := outer_mem_E_not_D_of_top hg htop hp hp2 hα
  have hdesc := orthogonal_prime_semilinear_actual_fixed_form_descent' _ .POmegaMinus
    (Or.inr (Or.inr rfl)) n ℓ (e * p) p hM hp hp2 hn1 K hK b c hirrK (MulEquiv.refl _) α hE hD
    hα.1
  obtain ⟨D, -, σ, hσ, hαD⟩ := exists_conj_fieldAutT_of_descent _ hE hdesc
    (fun σ h v => coordinateQuadMinus_fieldAut k n hn1 (hfixall σ h) b c v) (by
      intro U Q₀ hord hdisp
      obtain ⟨b', c', hirr', ν, S₀, -, -, S, ν', hSQ, -, hSA, -⟩ := hdisp
      have hfixV := hfixall U.val.right hord
      have hσk' : ∀ x, x ∈ semilinearFixedSubfield U.val.right ↔ U.val.right x = x :=
        fun x => RingHom.mem_eqLocusField
      have hb'k : (b' : K) ∈ k := (hfixV _).2 ((hσk' _).1 b'.2)
      have hc'k : (c' : K) ∈ k := (hfixV _).2 ((hσk' _).1 c'.2)
      have hirrkK : ∀ s ∈ k, s ^ 2 + (b : K) * s + (c : K) ≠ 0 := fun s hs hz =>
        hirr ⟨s, hs⟩ (Subtype.ext (by simpa using hz))
      have hirr'kK : ∀ s ∈ k, s ^ 2 + (b' : K) * s + (c' : K) ≠ 0 := by
        intro s hs hz
        have hsV : s ∈ KCOrthogonalDescent.fixedField U.val := (hσk' s).2 ((hfixV s).1 hs)
        exact hirr' ⟨s, hsV⟩ (Subtype.ext (by simpa using hz))
      obtain ⟨μ, hμk, hμQ⟩ :=
        SEITZ2.exists_tail_isometry k hn1 b.2 c.2 hb'k hc'k hirrkK hirr'kK
      have hμσ : glFieldAut (Fin (2 * n)) K U.val.right μ = μ :=
        Units.ext (Matrix.ext fun i j => (hfixV _).1 (hμk i j))
      refine ⟨μ * S, ν', fun v => ?_, ?_⟩
      · rw [Units.val_mul, ← Matrix.mulVec_mulVec]
        exact (hμQ _).trans (hSQ v)
      · rw [mul_assoc, hSA, map_mul, hμσ])
  obtain ⟨-, hconc⟩ :=
    orthogonal_prime_subfield_fixed_group_and_full_centralizer_odd .POmegaMinus
      (Or.inr (Or.inr rfl)) n ℓ e p ⟨hℓ, he, hn⟩ hp hp2 hpℓ hn1 K k hk hK σ hσ (hfixall σ hσ)
      b c hirr
  obtain ⟨⟨hinj, -, -⟩, -, hfixiff, hJN, -⟩ := hconc
  have hkfin : Finite k := inferInstance
  have hM0 : StatedClassicalModel (matrixProjectiveDerived (coordinateQuadMinus n k hn1 b c))
      .POmegaMinus n ℓ e :=
    ⟨⟨hℓ, he, hn⟩, k, inferInstance, inferInstance, hk, b, c, hirr,
      ⟨(coordinateMinusWitnessEquiv k hn1 b c (MulEquiv.refl _)).symm⟩⟩
  refine ⟨_, inferInstance, hM0,
    (D : MulAut _).toMonoidHom.comp (incl k (coordinateQuadMinus_isExtension k n hn1 b c)),
    D.injective.comp hinj, fun m => ?_⟩
  have hfx : fieldAutT (coordinateQuadMinus n K hn1 (b : K) (c : K)) σ
      (coordinateQuadMinus_fieldAut k n hn1 (hfixall σ hσ) b c)
      (incl k (coordinateQuadMinus_isExtension k n hn1 b c) m) =
      incl k (coordinateQuadMinus_isExtension k n hn1 b c) m :=
    (hfixiff _).2 (hJN ⟨m, rfl⟩)
  rw [hαD]
  exact conj_fixed hfx

theorem exists_fixed_model_of_minus {G : Type} [Group G] [Finite G] {n ℓ f p : ℕ}
    (hM : StatedClassicalModel G .POmegaMinus n ℓ f) (hp : p.Prime) (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ)
    {α : MulAut G} (hα : IsOuterOfOrder p α) :
    ∃ (M : Type) (_ : Group M) (e : ℕ), StatedClassicalModel M .POmegaMinus n ℓ e ∧
      ∃ ψ : M →* G, Function.Injective ψ ∧ ∀ m, α (ψ m) = ψ m := by
  obtain ⟨hℓ, hf, hn⟩ := id hM.1
  have hn1 : 1 ≤ n := by omega
  obtain ⟨e, K, _, _, k, σ, b, c, he, -, hk, hK, hσ, hfix, hirr, ⟨θ⟩⟩ :
      ∃ (e : ℕ) (K : Type) (_ : Field K) (_ : Finite K) (k : Subfield K) (σ : K ≃+* K)
        (b c : k), 1 ≤ e ∧ f = p * e ∧ Nat.card k = ℓ ^ e ∧ Nat.card K = ℓ ^ (e * p) ∧
        orderOf σ = p ∧ (∀ x, x ∈ k ↔ σ x = x) ∧ (∀ s : k, s ^ 2 + b * s + c ≠ 0) ∧
        Nonempty (G ≃* matrixProjectiveDerived
          (coordinateQuadMinus n K hn1 (b : K) (c : K))) := by
    by_cases hp3 : p = 3
    · exact exists_rational_model_minus_three hn1 hM hp hp3 hα
    · have hp5 : 3 < p := by
        obtain ⟨j, hj⟩ := hp.odd_of_ne_two hp2
        have := hp.two_le
        omega
      exact exists_rational_model_minus hn1 hM hp hp5 hpℓ hα
  obtain ⟨M, _, hM0, ψ, hψ, hfx⟩ := exists_fixed_model_minus_rational hn hn1 hℓ he hp hp2 hpℓ hk hK
    hσ hfix b c hirr (isOuterOfOrder_congr θ hα)
  refine ⟨M, inferInstance, e, hM0, θ.symm.toMonoidHom.comp ψ, θ.symm.injective.comp hψ,
    fun m => ?_⟩
  have h := hfx m
  rw [MulAut.congr_apply] at h
  change α (θ.symm (ψ m)) = θ.symm (ψ m)
  apply θ.injective
  rw [MulEquiv.apply_symm_apply]
  exact h

end CFSG.LocalAnalysis.GLTheoremA.S267.P3.OrthFix

end
