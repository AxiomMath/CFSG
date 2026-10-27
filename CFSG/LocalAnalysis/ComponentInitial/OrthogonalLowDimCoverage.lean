module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalLowDimCoverageCases
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalComponents

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial

open Matrix CFSG.ComponentClassification CFSG.ComponentClassification.CatalogueBOrthogonal
  CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit

section Packaging

variable {G : Type*} [Group G]

theorem derived_coverage_of_quasisimple (hq : CFSG.IsQuasisimple (commutator G))
    (hsq : ∀ g : G, g ^ 2 ∈ commutator G) :
    Group.IsPerfect (commutator G) ∧ IsPGroup 2 (G ⧸ commutator G) ∧
      (∃ (n : ℕ) (L : Fin n → Subgroup G), 1 ≤ n ∧ n ≤ 2 ∧ (⨆ i, L i) = commutator G ∧
        (∀ i, CFSG.IsQuasisimple (L i) ∧ L i ≤ commutator G ∧
          ((L i).subgroupOf (commutator G)).Normal) ∧
        ∀ i j, i ≠ j → ∀ x ∈ L i, ∀ y ∈ L j, x * y = y * x) ∧
      ∀ (g : G) (p : ℕ), p.Prime → 3 < p → orderOf g = p → g ∈ commutator G := by
  have hP := isPGroup_two_of_forall_sq_mem hsq
  refine ⟨hq.1, hP, ⟨1, fun _ => commutator G, le_rfl, by norm_num, iSup_const,
    fun _ => ⟨hq, le_rfl, ?_⟩, fun i j hij => absurd (Subsingleton.elim i j) hij⟩, ?_⟩
  · rw [Subgroup.subgroupOf_self]
    infer_instance
  · intro g p hp hp3 hg
    exact mem_of_isPGroup_two_of_orderOf_prime hP hp (by omega) hg

theorem derived_coverage_of_two_factors {L₁ L₂ : Subgroup G}
    (hsup : commutator G = L₁ ⊔ L₂) (hq₁ : CFSG.IsQuasisimple L₁)
    (hq₂ : CFSG.IsQuasisimple L₂) (hn₁ : (L₁.subgroupOf (commutator G)).Normal)
    (hn₂ : (L₂.subgroupOf (commutator G)).Normal)
    (hcomm : ∀ x ∈ L₁, ∀ y ∈ L₂, x * y = y * x) (hperf : Group.IsPerfect (commutator G))
    (hsq : ∀ g : G, g ^ 2 ∈ commutator G) :
    Group.IsPerfect (commutator G) ∧ IsPGroup 2 (G ⧸ commutator G) ∧
      (∃ (n : ℕ) (L : Fin n → Subgroup G), 1 ≤ n ∧ n ≤ 2 ∧ (⨆ i, L i) = commutator G ∧
        (∀ i, CFSG.IsQuasisimple (L i) ∧ L i ≤ commutator G ∧
          ((L i).subgroupOf (commutator G)).Normal) ∧
        ∀ i j, i ≠ j → ∀ x ∈ L i, ∀ y ∈ L j, x * y = y * x) ∧
      ∀ (g : G) (p : ℕ), p.Prime → 3 < p → orderOf g = p → g ∈ commutator G := by
  have hP := isPGroup_two_of_forall_sq_mem hsq
  refine ⟨hperf, hP, ⟨2, ![L₁, L₂], by norm_num, le_rfl, ?_, ?_, ?_⟩, ?_⟩
  · rw [hsup]
    apply le_antisymm
    · refine iSup_le fun i => ?_
      fin_cases i
      · exact le_sup_left
      · exact le_sup_right
    · exact sup_le (le_iSup ![L₁, L₂] 0) (le_iSup ![L₁, L₂] 1)
  · intro i
    fin_cases i
    · exact ⟨hq₁, hsup ▸ le_sup_left, hn₁⟩
    · exact ⟨hq₂, hsup ▸ le_sup_right, hn₂⟩
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact hcomm
    · exact fun x hx y hy => (hcomm y hy x hx).symm
    · exact absurd rfl hij
  · intro g p hp hp3 hg
    exact mem_of_isPGroup_two_of_orderOf_prime hP hp (by omega) hg

end Packaging

variable {K W : Type*} [Field K] [Finite K] [AddCommGroup W] [Module K W]
  [FiniteDimensional K W]

theorem orthogonal_low_dimensional_fixed_derived_component_coverage
    (Q : QuadraticForm K W) (hQ : Q.polarBilin.Nondegenerate)
    (hcase : (Odd (Nat.card K) ∧ (Module.finrank K W = 3 ∨ Module.finrank K W = 4 ∨
        Module.finrank K W = 5)) ∨
      (Odd (Nat.card K) ∧ Module.finrank K W = 6 ∧
        ¬ ∃ T : Submodule K W, Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) ∨
      (Module.finrank K W = 4 ∧
        ∃ S : Submodule K W, Module.finrank K S = 2 ∧ ∀ x ∈ S, Q x = 0)) :
    ((Module.finrank K W = 3 ∧ Nat.card K = 3) ∨
        ((Module.finrank K W = 4 ∧
          ∃ S : Submodule K W, Module.finrank K S = 2 ∧ ∀ x ∈ S, Q x = 0) ∧
          (Nat.card K = 2 ∨ Nat.card K = 3)) →
      (∀ p : ℕ, p.Prime → p ∣ Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) →
        p = 2 ∨ p = 3) ∧
      ∀ (g : TauCeti.QuadraticMap.orthogonalGroup Q) (p : ℕ), p.Prime → 3 < p →
        orderOf g ≠ p) ∧
    (¬ ((Module.finrank K W = 3 ∧ Nat.card K = 3) ∨
        ((Module.finrank K W = 4 ∧
          ∃ S : Submodule K W, Module.finrank K S = 2 ∧ ∀ x ∈ S, Q x = 0) ∧
          (Nat.card K = 2 ∨ Nat.card K = 3))) →
      Group.IsPerfect (commutator (TauCeti.QuadraticMap.orthogonalGroup Q)) ∧
      IsPGroup 2 (TauCeti.QuadraticMap.orthogonalGroup Q ⧸
        commutator (TauCeti.QuadraticMap.orthogonalGroup Q)) ∧
      (∃ (n : ℕ) (L : Fin n → Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)),
        1 ≤ n ∧ n ≤ 2 ∧ (⨆ i, L i) = commutator (TauCeti.QuadraticMap.orthogonalGroup Q) ∧
        (∀ i, CFSG.IsQuasisimple (L i) ∧
          L i ≤ commutator (TauCeti.QuadraticMap.orthogonalGroup Q) ∧
          ((L i).subgroupOf (commutator (TauCeti.QuadraticMap.orthogonalGroup Q))).Normal) ∧
        ∀ i j, i ≠ j → ∀ x ∈ L i, ∀ y ∈ L j, x * y = y * x) ∧
      ∀ (g : TauCeti.QuadraticMap.orthogonalGroup Q) (p : ℕ), p.Prime → 3 < p →
        orderOf g = p → g ∈ commutator (TauCeti.QuadraticMap.orthogonalGroup Q)) ∧
    (Odd (Nat.card K) → Module.finrank K W = 3 → Nat.card K ≠ 3 →
      ∃ (d : Kˣ) (ψ : W ≃ₗ[K] traceZeroSubmodule K)
        (e : TauCeti.QuadraticMap.orthogonalGroup Q ≃*
          TauCeti.QuadraticMap.orthogonalGroup (traceZeroForm K)),
        (∀ v, Q v = (d : K) * traceZeroForm K (ψ v)) ∧
        (∀ (g : TauCeti.QuadraticMap.orthogonalGroup Q) (X : traceZeroSubmodule K),
          (e g).val X = ψ (g.val (ψ.symm X))) ∧
        commutator (TauCeti.QuadraticMap.orthogonalGroup Q) =
          (traceZeroSpecialImage K).map e.symm.toMonoidHom ∧
        CFSG.IsQuasisimple (commutator (TauCeti.QuadraticMap.orthogonalGroup Q))) ∧
    (Module.finrank K W = 4 →
      (∃ S : Submodule K W, Module.finrank K S = 2 ∧ ∀ x ∈ S, Q x = 0) →
      Nat.card K ≠ 2 → Nat.card K ≠ 3 →
      ∃ (ψ : W ≃ₗ[K] Matrix (Fin 2) (Fin 2) K)
        (e : TauCeti.QuadraticMap.orthogonalGroup Q ≃* DeterminantIsometries K),
        (∀ v, Q v = (ψ v).det) ∧
        (∀ (g : TauCeti.QuadraticMap.orthogonalGroup Q) (X : Matrix (Fin 2) (Fin 2) K),
          (e g).val X = ψ (g.val (ψ.symm X))) ∧
        commutator (TauCeti.QuadraticMap.orthogonalGroup Q) =
          (determinantLeftFactor K).map e.symm.toMonoidHom ⊔
            (determinantRightFactor K).map e.symm.toMonoidHom ∧
        CFSG.IsQuasisimple ((determinantLeftFactor K).map e.symm.toMonoidHom) ∧
        CFSG.IsQuasisimple ((determinantRightFactor K).map e.symm.toMonoidHom) ∧
        (((determinantLeftFactor K).map e.symm.toMonoidHom).subgroupOf
          (commutator (TauCeti.QuadraticMap.orthogonalGroup Q))).Normal ∧
        (((determinantRightFactor K).map e.symm.toMonoidHom).subgroupOf
          (commutator (TauCeti.QuadraticMap.orthogonalGroup Q))).Normal ∧
        ∀ x ∈ (determinantLeftFactor K).map e.symm.toMonoidHom,
          ∀ y ∈ (determinantRightFactor K).map e.symm.toMonoidHom, x * y = y * x) ∧
    (∀ hodd : Odd (Nat.card K), Module.finrank K W = 4 →
      (¬ ∃ S : Submodule K W, Module.finrank K S = 2 ∧ ∀ x ∈ S, Q x = 0) →
      ∃ (δ : Kˣ), ¬ IsSquare (δ : K) ∧ ∃ (d : Kˣ)
        (ψ : W ≃ₗ[K] CatalogueBOrthogonalFourNonsplit.hermitianSubmodule (δ : K))
        (e : TauCeti.QuadraticMap.orthogonalGroup Q ≃*
          CatalogueBOrthogonalFourNonsplit.HermitianIsometries (δ : K)),
        (∀ v, Q v = (d : K) * CatalogueBOrthogonalFourNonsplit.hermitianForm (δ : K) (ψ v)) ∧
        (∀ (g : TauCeti.QuadraticMap.orthogonalGroup Q)
          (X : CatalogueBOrthogonalFourNonsplit.hermitianSubmodule (δ : K)),
          (e g).val X = ψ (g.val (ψ.symm X))) ∧
        commutator (TauCeti.QuadraticMap.orthogonalGroup Q) =
          (CatalogueBOrthogonalFourNonsplit.specialImage (δ : K)
            (CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd)).map e.symm.toMonoidHom ∧
        CFSG.IsQuasisimple (commutator (TauCeti.QuadraticMap.orthogonalGroup Q))) ∧
    (∀ hodd : Odd (Nat.card K), Module.finrank K W = 5 →
      ∃ (d : Kˣ) (ψ : W ≃ₗ[K] CatalogueBOrthogonalFive.selfAdjointSubmodule K)
        (e : TauCeti.QuadraticMap.orthogonalGroup Q ≃*
          TauCeti.QuadraticMap.orthogonalGroup (CatalogueBOrthogonalFive.selfAdjointForm K)),
        (∀ v, Q v = (d : K) * CatalogueBOrthogonalFive.selfAdjointForm K (ψ v)) ∧
        (∀ (g : TauCeti.QuadraticMap.orthogonalGroup Q)
          (X : CatalogueBOrthogonalFive.selfAdjointSubmodule K),
          (e g).val X = ψ (g.val (ψ.symm X))) ∧
        commutator (TauCeti.QuadraticMap.orthogonalGroup Q) =
          (CatalogueBOrthogonalFive.selfAdjointSymplecticImage
            (CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd)).map e.symm.toMonoidHom ∧
        CFSG.IsQuasisimple (commutator (TauCeti.QuadraticMap.orthogonalGroup Q))) ∧
    (∀ hodd : Odd (Nat.card K), Module.finrank K W = 6 →
      (¬ ∃ T : Submodule K W, Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) →
      ∃ (δ : Kˣ) (_ : Fact (¬ IsSquare (δ : K))) (d : Kˣ)
        (ψ : W ≃ₗ[K] CatalogueBOrthogonalSix.sixSubmodule (δ : K))
        (e : TauCeti.QuadraticMap.orthogonalGroup Q ≃*
          CatalogueBOrthogonalSix.SixIsometries (δ : K)),
        (∀ v, Q v = (d : K) * CatalogueBOrthogonalSix.sixForm (δ : K) (ψ v)) ∧
        (∀ (g : TauCeti.QuadraticMap.orthogonalGroup Q)
          (X : CatalogueBOrthogonalSix.sixSubmodule (δ : K)),
          (e g).val X = ψ (g.val (ψ.symm X))) ∧
        commutator (TauCeti.QuadraticMap.orthogonalGroup Q) =
          (CatalogueBOrthogonalSix.sixSpecialImage (δ : K)
            (CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd)).map e.symm.toMonoidHom ∧
        CFSG.IsQuasisimple (commutator (TauCeti.QuadraticMap.orthogonalGroup Q))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro hexc
    have hprime : ∀ p : ℕ, p.Prime → p ∣ Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) →
        p = 2 ∨ p = 3 := by
      intro p hp hdvd
      rcases hexc with ⟨hdim, hK⟩ | ⟨⟨hdim, S, hSdim, hSQ⟩, hK⟩
      · have hodd : Odd (Nat.card K) := by rw [hK]; decide
        obtain ⟨-, -, e, -, -, -⟩ :=
          CatalogueBOrthogonalThreeSimilarity.exists_trace_zero_similarity_and_orthogonal_equiv
            hodd Q hQ hdim
        rw [Nat.card_congr e.toEquiv] at hdvd
        exact traceZero_prime_dvd_card hK hp hdvd
      · obtain ⟨-, e, -, -, -⟩ := split_four_determinant_form_isometry Q hQ hdim S hSdim hSQ
        rw [Nat.card_congr e.toEquiv] at hdvd
        exact determinant_prime_dvd_card (by omega) hp hdvd
    exact ⟨hprime, fun g p hp hp3 => orderOf_ne_of_prime_dvd_card hprime g hp hp3⟩
  ·
    intro hnexc
    have h3 : Module.finrank K W = 3 → Nat.card K ≠ 3 := fun hd hK => hnexc (Or.inl ⟨hd, hK⟩)
    have hsplit : Module.finrank K W = 4 →
        (∃ S : Submodule K W, Module.finrank K S = 2 ∧ ∀ x ∈ S, Q x = 0) →
        Nat.card K ≠ 2 ∧ Nat.card K ≠ 3 := fun hd hS =>
      ⟨fun hK => hnexc (Or.inr ⟨⟨hd, hS⟩, Or.inl hK⟩),
        fun hK => hnexc (Or.inr ⟨⟨hd, hS⟩, Or.inr hK⟩)⟩
    have hsplitCase : Module.finrank K W = 4 →
        (∃ S : Submodule K W, Module.finrank K S = 2 ∧ ∀ x ∈ S, Q x = 0) →
        Group.IsPerfect (commutator (TauCeti.QuadraticMap.orthogonalGroup Q)) ∧
        IsPGroup 2 (TauCeti.QuadraticMap.orthogonalGroup Q ⧸
          commutator (TauCeti.QuadraticMap.orthogonalGroup Q)) ∧
        (∃ (n : ℕ) (L : Fin n → Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)),
          1 ≤ n ∧ n ≤ 2 ∧ (⨆ i, L i) = commutator (TauCeti.QuadraticMap.orthogonalGroup Q) ∧
          (∀ i, CFSG.IsQuasisimple (L i) ∧
            L i ≤ commutator (TauCeti.QuadraticMap.orthogonalGroup Q) ∧
            ((L i).subgroupOf (commutator (TauCeti.QuadraticMap.orthogonalGroup Q))).Normal) ∧
          ∀ i j, i ≠ j → ∀ x ∈ L i, ∀ y ∈ L j, x * y = y * x) ∧
        ∀ (g : TauCeti.QuadraticMap.orthogonalGroup Q) (p : ℕ), p.Prime → 3 < p →
          orderOf g = p → g ∈ commutator (TauCeti.QuadraticMap.orthogonalGroup Q) := by
      intro hd hS
      obtain ⟨hK2, hK3⟩ := hsplit hd hS
      obtain ⟨-, e, -, -, hsup, hq₁, hq₂, hn₁, hn₂, hcomm, hperf, hsq⟩ :=
        orthogonal_split_four_derived hK2 hK3 Q hQ hd hS
      exact derived_coverage_of_two_factors hsup hq₁ hq₂ hn₁ hn₂ hcomm hperf hsq
    rcases hcase with ⟨hodd, hd | hd | hd⟩ | ⟨hodd, hd, hno⟩ | ⟨hd, hS⟩
    · obtain ⟨-, -, -, -, -, -, hq, hsq⟩ := orthogonal_three_derived hodd (h3 hd) Q hQ hd
      exact derived_coverage_of_quasisimple hq hsq
    · by_cases hS : ∃ S : Submodule K W, Module.finrank K S = 2 ∧ ∀ x ∈ S, Q x = 0
      · exact hsplitCase hd hS
      · obtain ⟨-, -, -, -, -, -, -, -, hq, hsq⟩ := orthogonal_nonsplit_four_derived hodd Q hQ hd hS
        exact derived_coverage_of_quasisimple hq hsq
    · obtain ⟨-, -, -, -, -, -, hq, hsq⟩ := orthogonal_five_derived hodd Q hQ hd
      exact derived_coverage_of_quasisimple hq hsq
    · obtain ⟨-, -, -, -, -, -, -, -, hq, hsq⟩ := orthogonal_nonsplit_six_derived hodd Q hQ hd hno
      exact derived_coverage_of_quasisimple hq hsq
    · exact hsplitCase hd hS
  ·
    intro hodd hd hK3
    obtain ⟨d, ψ, e, hψ, he, hc, hq, -⟩ := orthogonal_three_derived hodd hK3 Q hQ hd
    exact ⟨d, ψ, e, hψ, he, hc, hq⟩
  ·
    intro hd hS hK2 hK3
    obtain ⟨ψ, e, hψ, he, hsup, hq₁, hq₂, hn₁, hn₂, hcomm, -, -⟩ :=
      orthogonal_split_four_derived hK2 hK3 Q hQ hd hS
    exact ⟨ψ, e, hψ, he, hsup, hq₁, hq₂, hn₁, hn₂, hcomm⟩
  ·
    intro hodd hd hno
    obtain ⟨δ, hδ, d, ψ, e, hψ, he, hc, hq, -⟩ := orthogonal_nonsplit_four_derived hodd Q hQ hd hno
    exact ⟨δ, hδ, d, ψ, e, hψ, he, hc, hq⟩
  ·
    intro hodd hd
    obtain ⟨d, ψ, e, hψ, he, hc, hq, -⟩ := orthogonal_five_derived hodd Q hQ hd
    exact ⟨d, ψ, e, hψ, he, hc, hq⟩
  ·
    intro hodd hd hno
    obtain ⟨δ, hδ, d, ψ, e, hψ, he, hc, hq, -⟩ := orthogonal_nonsplit_six_derived hodd Q hQ hd hno
    exact ⟨δ, hδ, d, ψ, e, hψ, he, hc, hq⟩

end CFSG.LocalAnalysis.ComponentInitial
