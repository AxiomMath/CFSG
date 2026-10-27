module

public import CFSG.LieType.SeitzGeneration.OuterOrthThreeGates
public import CFSG.LieType.SeitzGeneration.OuterOrthThreeSubfield
public import CFSG.LieType.SeitzGeneration.OuterOrthThreePair
public import CFSG.LieType.SeitzGeneration.OuterOrthMinus
public import CFSG.HardMathSupport.Lang.Proving.OrthogonalFieldDescentOdd

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix Subgroup CFSG.RankThree.PartOne CFSG.RankThree.PartOne.CTP
  CFSG.RankThree.PartOne.KCOrthogonalSubfield CFSG.RankThree.Classical.SteinbergBY
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBHigherLinearField
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)
open CFSG.Assembly.LowTwoRank (StatedProj StatedOmega StatedQuadOdd StatedQuadPlus StatedQuadMinus
  StatedLieAdmissible StatedLieTag StatedClassicalModel)
open CFSG.HardMathSupport.Lang.Proving (orthogonal_prime_semilinear_actual_fixed_form_descent')
open CFSG.RankThree.PartOne.KCOrthogonalAut
  (matrixProjectiveImage_eq_top_odd matrixProjectiveImage_eq_top_plus
    matrixProjectiveImage_eq_top_minus)
open CFSG.ClassicalGroups.Orthogonal (ringChar_eq_of_card_eq)

section Odd

variable {n ℓ f p : ℕ} {K : Type} [Field K] [Finite K]

theorem fieldAutData_odd_three (hpair : SubfieldPairOmegaOddThree)
    (hadm : StatedLieAdmissible .POmegaOdd n ℓ f) (hK : Nat.card K = ℓ ^ f) (hp : p.Prime)
    (hp3 : p = 3) (hpℓ : p ≠ ℓ) :
    FieldAutData (matrixProjectiveDerived (coordinateQuadOdd n K)) p := by
  classical
  subst hp3
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
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
  refine fieldAutData_matrixProjectiveDerived_odd _ hℓ hf hK hp
    (fun E hE hEc => exists_conj_mem_of_plane_of_top hg htop hp hp2 E hE hEc)
    (fun σ _ => coordinateQuadOdd_fieldAut n σ) ?_ ?_
  · intro α hα
    obtain ⟨hE, hD⟩ := outer_mem_E_not_D_of_top hg htop hp hp2 hα
    have hdesc := orthogonal_prime_semilinear_actual_fixed_form_descent' _ .POmegaOdd (Or.inl rfl)
      n ℓ f 3 hM hp hp2 K hK (MulEquiv.refl _) α hE hD hα.1
    exact exists_conj_fieldAutT_of_descent _ hE hdesc (fun σ _ => coordinateQuadOdd_fieldAut n σ)
      (fun U Q₀ _ hdisp => by
        obtain ⟨ν, S₀, -, -, S, ν', hSQ, -, hSA, -⟩ := hdisp
        exact ⟨S, ν', hSQ, hSA⟩)
  · intro σ hσ
    obtain ⟨hpf, hcardk⟩ := card_semilinearFixedSubfield hℓ hf hK hσ
    obtain ⟨e, rfl⟩ := hpf
    have he : 1 ≤ e := by
      rcases Nat.eq_zero_or_pos e with h0 | h0
      · rw [h0, mul_zero] at hf
        omega
      · exact h0
    rw [Nat.mul_div_cancel_left e hp.pos] at hcardk
    have hK' : Nat.card K = ℓ ^ (e * 3) := by rw [hK, mul_comm]
    have hσk : ∀ x, x ∈ semilinearFixedSubfield σ ↔ σ x = x := fun x => RingHom.mem_eqLocusField
    obtain ⟨-, hconc⟩ :=
      orthogonal_prime_subfield_fixed_group_and_full_centralizer_odd .POmegaOdd
        (Or.inl rfl) n ℓ e 3 ⟨hℓ, he, hn3, hℓ2⟩ hp hp2 hpℓ K (semilinearFixedSubfield σ) hcardk hK'
        σ hσ hσk
    exact fixedGood_of_subfieldConclusion hconc
      (hpair n ℓ e hn3 hℓ hℓ2 (Ne.symm hpℓ) he K (semilinearFixedSubfield σ) hcardk hK')

end Odd

section Plus

variable {n ℓ f p : ℕ} {K : Type} [Field K] [Finite K]

theorem fieldAutData_plus_three (hpair : SubfieldPairOmegaPlusThree)
    (hadm : StatedLieAdmissible .POmegaPlus n ℓ f) (hn5 : 5 ≤ n) (hK : Nat.card K = ℓ ^ f)
    (hp : p.Prime) (hp3 : p = 3) (hpℓ : p ≠ ℓ) :
    FieldAutData (matrixProjectiveDerived (coordinateQuadPlus n K)) p := by
  classical
  subst hp3
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  obtain ⟨hℓ, hf, hn4⟩ := id hadm
  have hM : StatedClassicalModel (StatedProj (StatedOmega (StatedQuadPlus n K))) .POmegaPlus n ℓ
      f := ⟨hadm, K, inferInstance, inferInstance, hK, ⟨MulEquiv.refl _⟩⟩
  have hg : OrthogonalGates (coordinateQuadPlus n K) f :=
    orthogonal_large_prime_semilinear_field_and_diagonal_gates _ .POmegaPlus (Or.inr (Or.inl rfl))
      n ℓ f hM K hK (MulEquiv.refl _)
  have htop := matrixProjectiveImage_eq_top_plus K n hn5
  refine fieldAutData_matrixProjectiveDerived_odd _ hℓ hf hK hp
    (fun E hE hEc => exists_conj_mem_of_plane_of_top hg htop hp hp2 E hE hEc)
    (fun σ _ => coordinateQuadPlus_fieldAut n σ) ?_ ?_
  · intro α hα
    obtain ⟨hE, hD⟩ := outer_mem_E_not_D_of_top hg htop hp hp2 hα
    have hdesc := orthogonal_prime_semilinear_actual_fixed_form_descent' _ .POmegaPlus
      (Or.inr (Or.inl rfl)) n ℓ f 3 hM hp hp2 K hK (MulEquiv.refl _) α hE hD hα.1
    exact exists_conj_fieldAutT_of_descent _ hE hdesc (fun σ _ => coordinateQuadPlus_fieldAut n σ)
      (fun U Q₀ _ hdisp => by
        obtain ⟨ν, S₀, -, -, S, ν', hSQ, -, hSA, -⟩ := hdisp
        exact ⟨S, ν', hSQ, hSA⟩)
  · intro σ hσ
    obtain ⟨hpf, hcardk⟩ := card_semilinearFixedSubfield hℓ hf hK hσ
    obtain ⟨e, rfl⟩ := hpf
    have he : 1 ≤ e := by
      rcases Nat.eq_zero_or_pos e with h0 | h0
      · rw [h0, mul_zero] at hf
        omega
      · exact h0
    rw [Nat.mul_div_cancel_left e hp.pos] at hcardk
    have hK' : Nat.card K = ℓ ^ (e * 3) := by rw [hK, mul_comm]
    have hσk : ∀ x, x ∈ semilinearFixedSubfield σ ↔ σ x = x := fun x => RingHom.mem_eqLocusField
    obtain ⟨-, hconc⟩ :=
      orthogonal_prime_subfield_fixed_group_and_full_centralizer_odd .POmegaPlus
        (Or.inr (Or.inl rfl)) n ℓ e 3 ⟨hℓ, he, hn4⟩ hp hp2 hpℓ K (semilinearFixedSubfield σ)
        hcardk hK' σ hσ hσk
    exact fixedGood_of_subfieldConclusion hconc
      (hpair n ℓ e hn4 hℓ (Ne.symm hpℓ) he K (semilinearFixedSubfield σ) hcardk hK')

end Plus

section Rational

variable {n ℓ e p : ℕ} {K : Type} [Field K] [Finite K]

theorem fieldAutData_minus_rational_three (hpair : SubfieldPairOmegaMinusThree) (hn : 4 ≤ n)
    (hn1 : 1 ≤ n) (hℓ : ℓ.Prime) (he : 1 ≤ e) (hp : p.Prime) (hp3 : p = 3) (hpℓ : p ≠ ℓ)
    {k : Subfield K} (hk : Nat.card k = ℓ ^ e) (hK : Nat.card K = ℓ ^ (e * p)) {σ₀ : K ≃+* K}
    (hσ₀ : orderOf σ₀ = p) (hfix : ∀ x, x ∈ k ↔ σ₀ x = x) (b c : k)
    (hirr : ∀ s : k, s ^ 2 + b * s + c ≠ 0) :
    FieldAutData (matrixProjectiveDerived (coordinateQuadMinus n K hn1 (b : K) (c : K))) p := by
  classical
  subst hp3
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hf : 1 ≤ e * 3 := Nat.mul_pos he hp.pos
  have hfixall := fun σ (h : orderOf σ = 3) => fixed_of_orderOf_orth hℓ he hp hK hσ₀ hfix h
  have hirrK : ∀ s : K, s ^ 2 + (b : K) * s + (c : K) ≠ 0 :=
    rootFree_of_odd_degree k hp hp2 (finrank_subfield_eq k hℓ he hk hK) b c hirr
  have hM : StatedClassicalModel
      (StatedProj (StatedOmega (StatedQuadMinus n K (b : K) (c : K)))) .POmegaMinus n ℓ (e * 3) :=
    ⟨⟨hℓ, hf, hn⟩, K, inferInstance, inferInstance, hK, b, c, hirrK, ⟨MulEquiv.refl _⟩⟩
  have hg : OrthogonalGates (coordinateQuadMinus n K hn1 (b : K) (c : K)) (e * 3) :=
    orthogonal_large_prime_semilinear_field_and_diagonal_gates _ .POmegaMinus
      (Or.inr (Or.inr rfl)) n ℓ (e * 3) hM hn1 K hK b c hirrK (MulEquiv.refl _)
  have htop := matrixProjectiveImage_eq_top_minus K n hn (b : K) (c : K) hirrK
  refine fieldAutData_matrixProjectiveDerived_odd _ hℓ hf hK hp
    (fun E hE hEc => exists_conj_mem_of_plane_of_top hg htop hp hp2 E hE hEc)
    (fun σ h v => coordinateQuadMinus_fieldAut k n hn1 (hfixall σ h) b c v) ?_ ?_
  · intro α hα
    obtain ⟨hE, hD⟩ := outer_mem_E_not_D_of_top hg htop hp hp2 hα
    have hdesc := orthogonal_prime_semilinear_actual_fixed_form_descent' _ .POmegaMinus
      (Or.inr (Or.inr rfl)) n ℓ (e * 3) 3 hM hp hp2 hn1 K hK b c hirrK (MulEquiv.refl _) α hE hD
      hα.1
    refine exists_conj_fieldAutT_of_descent _ hE hdesc
      (fun σ h v => coordinateQuadMinus_fieldAut k n hn1 (hfixall σ h) b c v) ?_
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
    · rw [mul_assoc, hSA, map_mul, hμσ]
  · intro σ hσ
    obtain ⟨-, hconc⟩ :=
      orthogonal_prime_subfield_fixed_group_and_full_centralizer_odd .POmegaMinus
        (Or.inr (Or.inr rfl)) n ℓ e 3 ⟨hℓ, he, hn⟩ hp hp2 hpℓ hn1 K k hk hK σ hσ (hfixall σ hσ)
        b c hirr
    exact fixedGood_of_subfieldConclusion hconc
      (hpair n ℓ e hn hℓ (Ne.symm hpℓ) he K k hk hK b c hirr)

end Rational

section Model

variable {G : Type} [Group G] [Finite G] {n ℓ f p : ℕ}

omit [Finite G] in
theorem exists_rational_model_minus_three (hn1 : 1 ≤ n)
    (hM : StatedClassicalModel G .POmegaMinus n ℓ f) (hp : p.Prime) (hp3 : p = 3)
    {α : MulAut G} (hα : IsOuterOfOrder p α) :
    ∃ (e : ℕ) (K : Type) (_ : Field K) (_ : Finite K) (k : Subfield K) (σ : K ≃+* K) (b c : k),
      1 ≤ e ∧ f = p * e ∧ Nat.card k = ℓ ^ e ∧ Nat.card K = ℓ ^ (e * p) ∧ orderOf σ = p ∧
        (∀ x, x ∈ k ↔ σ x = x) ∧ (∀ s : k, s ^ 2 + b * s + c ≠ 0) ∧
        Nonempty (G ≃* matrixProjectiveDerived (coordinateQuadMinus n K hn1 (b : K) (c : K))) := by
  classical
  have hp2 : p ≠ 2 := by omega
  have hf1 : 1 ≤ f := hM.1.2.1
  obtain ⟨-, K, _, _, hK, b₁, c₁, hirr₁, ⟨e₁⟩⟩ := id hM
  have hn : 4 ≤ n := hM.1.2.2
  have hg : OrthogonalGates (coordinateQuadMinus n K hn1 b₁ c₁) f :=
    orthogonal_large_prime_semilinear_field_and_diagonal_gates G .POmegaMinus
      (Or.inr (Or.inr rfl)) n ℓ f hM hn1 K hK b₁ c₁ hirr₁ e₁
  have htop := matrixProjectiveImage_eq_top_minus K n hn b₁ c₁ hirr₁
  have ha := isOuterOfOrder_congr (coordinateMinusWitnessEquiv K hn1 b₁ c₁ e₁) hα
  obtain ⟨haE, haD⟩ := outer_mem_E_not_D_of_top hg htop hp hp2 ha
  have hdesc := orthogonal_prime_semilinear_actual_fixed_form_descent' G .POmegaMinus
    (Or.inr (Or.inr rfl)) n ℓ f p hM hp hp2 hn1 K hK b₁ c₁ hirr₁ e₁ _ haE haD ha.1
  obtain ⟨g, hg'⟩ := haE
  obtain ⟨hpf, hrest⟩ := hdesc
  obtain ⟨hord', hcard, V, cc, Q₀, hVκ, hVr, hFFD, hDisp⟩ := hrest g.val.right ⟨g, hg', rfl⟩
  obtain ⟨b', c', hirr', ν, S₀, hS₀, hCM, hT⟩ := hDisp
  obtain ⟨S, ν', hSQ, hSS₀, hSA, Θ, hΘ1, g', hg'l, hg'r, hΘ⟩ := hT
  obtain ⟨e, rfl⟩ := hpf
  have he : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with h0 | h0
    · rw [h0, mul_zero] at hf1
      omega
    · exact h0
  rw [Nat.mul_div_cancel_left e hp.pos] at hcard
  have hσV : orderOf V.val.right = p := by rw [hVr]; exact hord'
  have hσk : ∀ x, x ∈ semilinearFixedSubfield V.val.right ↔ V.val.right x = x :=
    fun x => RingHom.mem_eqLocusField
  have hcard' : Nat.card (semilinearFixedSubfield V.val.right) = ℓ ^ e := by
    rw [hVr]
    exact hcard
  exact ⟨e, K, inferInstance, inferInstance, semilinearFixedSubfield V.val.right, V.val.right,
    b', c', he, rfl, hcard', by rw [mul_comm]; exact hK, hσV, hσk, hirr',
    ⟨(coordinateMinusWitnessEquiv K hn1 b₁ c₁ e₁).trans Θ⟩⟩

theorem fieldAutData_minus_three (hpair : SubfieldPairOmegaMinusThree)
    (hM : StatedClassicalModel G .POmegaMinus n ℓ f) (hp : p.Prime) (hp3 : p = 3)
    (hpℓ : p ≠ ℓ) : FieldAutData G p := by
  obtain ⟨hℓ, hf, hn⟩ := id hM.1
  have hn1 : 1 ≤ n := by omega
  have hp2 : p ≠ 2 := by omega
  by_cases hex : ∃ α : MulAut G, IsOuterOfOrder p α
  · obtain ⟨α, hα⟩ := hex
    obtain ⟨e, K, _, _, k, σ, b, c, he, -, hk, hK, hσ, hfix, hirr, ⟨ψ⟩⟩ :=
      exists_rational_model_minus_three hn1 hM hp hp3 hα
    exact (fieldAutData_minus_rational_three hpair hn hn1 hℓ he hp hp3 hpℓ hk hK hσ hfix b c
      hirr).of_mulEquiv ψ hp
  · obtain ⟨-, K, _, _, hK, b₁, c₁, hirr₁, ⟨e₁⟩⟩ := id hM
    have hg : OrthogonalGates (coordinateQuadMinus n K hn1 b₁ c₁) f :=
      orthogonal_large_prime_semilinear_field_and_diagonal_gates G .POmegaMinus
        (Or.inr (Or.inr rfl)) n ℓ f hM hn1 K hK b₁ c₁ hirr₁ e₁
    have htop := matrixProjectiveImage_eq_top_minus K n hn b₁ c₁ hirr₁
    let Θ := coordinateMinusWitnessEquiv K hn1 b₁ c₁ e₁
    have hexP : ¬ ∃ α : MulAut (matrixProjectiveDerived (coordinateQuadMinus n K hn1 b₁ c₁)),
        IsOuterOfOrder p α := fun ⟨α, hα⟩ =>
      hex ⟨MulAut.congr Θ.symm α, isOuterOfOrder_congr Θ.symm hα⟩
    have hdata : FieldAutData (matrixProjectiveDerived (coordinateQuadMinus n K hn1 b₁ c₁)) p :=
      ⟨fun E hE hEc => exists_conj_mem_of_plane_of_top hg htop hp hp2 E hE hEc,
        fun σ hσ => absurd ⟨σ, hσ⟩ hexP, fun σ τ hσ _ _ => absurd ⟨σ, hσ⟩ hexP⟩
    exact hdata.of_mulEquiv Θ hp

theorem fieldAutData_of_model_three (hpair : SubfieldPairOmegaThree) {c : StatedLieTag}
    (hc : c = .POmegaOdd ∨ c = .POmegaPlus ∨ c = .POmegaMinus)
    (hM : StatedClassicalModel G c n ℓ f) (hD4 : c = .POmegaPlus → n ≠ 4) (hp : p.Prime)
    (hp3 : p = 3) (hpℓ : p ≠ ℓ) : FieldAutData G p := by
  rcases hc with rfl | rfl | rfl
  · obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ := id hM
    exact (fieldAutData_odd_three hpair.1 hadm hK hp hp3 hpℓ).of_mulEquiv
      (coordinateOddWitnessEquiv K e) hp
  · obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ := id hM
    have hn4 : 4 ≤ n := hadm.2.2
    have hn5 : 5 ≤ n := by
      have := hD4 rfl
      omega
    exact (fieldAutData_plus_three hpair.2.1 hadm hn5 hK hp hp3 hpℓ).of_mulEquiv
      (coordinatePlusWitnessEquiv K e) hp
  · exact fieldAutData_minus_three hpair.2.2 hM hp hp3 hpℓ

end Model

end CFSG.LieType.SeitzGeneration
