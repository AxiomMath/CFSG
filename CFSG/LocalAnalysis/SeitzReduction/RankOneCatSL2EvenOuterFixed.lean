module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatEvenOuterPSUPSp

public noncomputable section

namespace CFSG.SeitzReduction.RankOne

open CFSG Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification
open CFSG.ComponentClassification.CatLeafProof (fixedSubgroupCongrEquiv)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

@[expose] def SpFixedRankOrNoPComponent (X : Type) [Group X] (g : ℕ) (R : ℕ → Prop) : Prop :=
  (∃ (k : Type) (_ : Field k) (_ : Finite k) (r : ℕ), Nat.card k = 2 ^ g ∧ 1 ≤ r ∧ R r ∧
      Nonempty (X ≃* StatedSp r k)) ∨ (∀ P : Subgroup X, ¬ IsPComponent 2 P)

theorem spFixedRankOrNoPComponent_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    {g : ℕ} {R : ℕ → Prop} (h : SpFixedRankOrNoPComponent Y g R) :
    SpFixedRankOrNoPComponent X g R := by
  rcases h with ⟨k, _, _, r, hk, hr, hR, ⟨Φ⟩⟩ | h
  · exact Or.inl ⟨k, inferInstance, inferInstance, r, hk, hr, hR, ⟨e.trans Φ⟩⟩
  · exact Or.inr fun P hP =>
      h _ (LocalAnalysis.ComponentInitial.isPComponent_map_of_isPComponent 2 e hP)

@[expose] def PSLOuterFixedRank (X : Type) [Group X] (n e : ℕ) : Prop :=
  (∀ P : Subgroup X, IsPComponent 2 P →
      StatedLieAdmissible .PSL n 2 (e / 2) ∧ LieModel P .PSL n 2 (e / 2) ∧ 2 * (e / 2) = e) ∨
    (∀ P : Subgroup X, IsPComponent 2 P →
      StatedLieAdmissible .PSU n 2 (e / 2) ∧ LieModel P .PSU n 2 (e / 2)) ∨
    SpFixedRankOrNoPComponent X e (fun r => 3 ≤ n ∧ (n = 2 * r ∨ n = 2 * r + 1))

theorem pslOuterFixedRank_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {n e' : ℕ}
    (h : PSLOuterFixedRank Y n e') : PSLOuterFixedRank X n e' := by
  have hmap : ∀ P : Subgroup X, IsPComponent 2 P → IsPComponent 2 (P.map e.toMonoidHom) :=
    fun P hP => LocalAnalysis.ComponentInitial.isPComponent_map_of_isPComponent 2 e hP
  have heq : ∀ P : Subgroup X, P ≃* P.map e.toMonoidHom :=
    fun P => P.equivMapOfInjective e.toMonoidHom e.injective
  rcases h with h | h | h
  · refine Or.inl fun P hP => ?_
    obtain ⟨hadm, hm, he⟩ := h _ (hmap P hP)
    exact ⟨hadm, LieType.CurtisTits.lieModel_of_mulEquiv (heq P).symm hm, he⟩
  · refine Or.inr (Or.inl fun P hP => ?_)
    obtain ⟨hadm, hm⟩ := h _ (hmap P hP)
    exact ⟨hadm, LieType.CurtisTits.lieModel_of_mulEquiv (heq P).symm hm⟩
  · exact Or.inr (Or.inr (spFixedRankOrNoPComponent_of_mulEquiv e h))

theorem psl_outer_fixed_rank {J : Type} [Group J] {n e : ℕ}
    (hadm : StatedLieAdmissible .PSL n 2 e) (hm : LieModel J .PSL n 2 e) (α : MulAut J)
    (hα : orderOf α = 2) (hαo : α ∉ (MulAut.conj : J →* MulAut J).range) :
    PSLOuterFixedRank (fixedSubgroup α) n e := by
  obtain ⟨K, _, _, hK, ⟨eJ⟩⟩ := CatLeafProof.nonempty_mulEquiv_psl_of_lieModel hadm hm
  have hf : 1 ≤ e := hadm.2.1
  have hβ : orderOf (MulAut.congr eJ α) = 2 :=
    (orderOf_injective (MulAut.congr eJ).toMonoidHom (MulAut.congr eJ).injective α).trans hα
  have hβ2 : MulAut.congr eJ α ^ 2 = 1 := hβ ▸ pow_orderOf_eq_one _
  have hβo : MulAut.congr eJ α ∉ inner (ProjectiveSpecialLinearGroup (Fin n) K) := by
    rw [LocalAnalysis.ComponentInitial.FixedFourGroup.congr_mem_inner_iff]
    exact hαo
  have key : ∀ γ : MulAut (ProjectiveSpecialLinearGroup (Fin n) K), MulAut.congr eJ α = γ →
      PSLOuterFixedRank (fixedSubgroup γ) n e → PSLOuterFixedRank (fixedSubgroup α) n e :=
    fun γ hγ h => pslOuterFixedRank_of_mulEquiv ((fixedSubgroupCongrEquiv eJ α).trans
      (MulEquiv.subgroupCongr (congrArg fixedSubgroup hγ))) h
  have hn : 2 ≤ n := hadm.2.2.1
  have hsemi : ∀ (A : GL (Fin n) K) (σ : K ≃+* K),
      MulAut.congr eJ α = CatalogueBLinearSemilinear.semilinearAction n K A σ →
      PSLOuterFixedRank (fixedSubgroup α) n e := by
    intro A σ hAσ
    by_cases hσ : σ = 1
    · subst hσ
      rw [CatalogueBLinearSemilinear.semilinearAction_one_field] at hAσ
      exact absurd (CatLeafProof.innerDiagonalAction_mem_inner_of_sq hf hK A (hAσ ▸ hβ2))
        (hAσ ▸ hβo)
    · exact key _ hAσ (Or.inl (LinearPilot.psl_field_pComponents hn hf hK A σ hσ (hAσ ▸ hβ2)))
  rcases (by omega : n = 2 ∨ 3 ≤ n) with rfl | hn3
  · obtain ⟨A, σ, hAσ⟩ := CatLeafProof.psl_two_normal_form (MulAut.congr eJ α)
    exact hsemi A σ hAσ
  · obtain ⟨-, hgen⟩ := LocalAnalysis.ComponentInitial.LinearFlag.automorphism_generation
      (K := K) hn3
    obtain ⟨A, σ, ε, hε, hAσε⟩ :=
      hgen (MulAut.congr (CatalogueBLinearHigherB.nativeEquiv n K).symm (MulAut.congr eJ α))
    have hβ' : MulAut.congr eJ α = MulAut.congr (CatalogueBLinearHigherB.nativeEquiv n K)
        (LocalAnalysis.ComponentInitial.LinearFlag.conjAut n K A *
          LocalAnalysis.ComponentInitial.LinearFlag.fieldAut n K σ *
            LocalAnalysis.ComponentInitial.LinearFlag.dualAut n K ^ ε) := by
      rw [← hAσε]
      ext x
      simp
    interval_cases ε
    · rw [pow_zero, mul_one, CatalogueBLinearHigherB.congr_semilinear] at hβ'
      exact hsemi A σ hβ'
    · rw [pow_one] at hβ'
      by_cases hσ : σ = 1
      · subst hσ
        rw [map_one, mul_one, CatalogueBLinearHigherB.congr_pureGraph] at hβ'
        refine key _ hβ' ?_
        rcases F4Pilot.psl_graph_cases hf hK hn3 A (hβ' ▸ hβ) with ⟨r, hr1, hnr, ⟨Φ⟩⟩ | hch
        · exact Or.inr (Or.inr (Or.inl
            ⟨K, inferInstance, inferInstance, r, hK, hr1, ⟨hn3, hnr⟩, ⟨Φ⟩⟩))
        · exact Or.inr (Or.inr (Or.inr
            (ComponentClassification.CatLeafProof.not_isPComponent_of_isCharacteristicP hch)))
      · rw [CatalogueBLinearHigherB.congr_graphField] at hβ'
        exact key _ hβ' (Or.inr (Or.inl
          (LinearPilot.psl_graphField_pComponents hn3 hf hK A σ hσ (hβ' ▸ hβ))))

section Unitary

open CFSG.LocalAnalysis.ComponentInitial FourGroupEvenCanonical UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.ComponentClassification.UnbalancedCatalog.UnitaryFieldTransfer

theorem psu_outer_fixed_rank {J : Type} [Group J] {n e : ℕ}
    (hadm : StatedLieAdmissible .PSU n 2 e) (hm : LieModel J .PSU n 2 e) (α : MulAut J)
    (hα : orderOf α = 2) (hαo : α ∉ (MulAut.conj : J →* MulAut J).range) :
    SpFixedRankOrNoPComponent (fixedSubgroup α) e (fun r => n = 2 * r ∨ n = 2 * r + 1) := by
  obtain ⟨K, _, h, ⟨ψ⟩⟩ := CatLeafProof.nonempty_mulEquiv_primeFormP_of_lieModel hadm hm
  have hn : 3 ≤ n := hadm.2.2.1
  have hq : ¬(n = 3 ∧ 2 ^ e = 2) := fun h3 => hadm.2.2.2 (by rw [h3.1, h3.2])
  have : Finite K := h.finite
  have : Finite J := Finite.of_equiv _ ψ.symm.toEquiv
  have hC : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_one
  have hβ : orderOf (MulAut.congr ψ α) = 2 :=
    (orderOf_injective (MulAut.congr ψ).toMonoidHom (MulAut.congr ψ).injective α).trans hα
  have hβo : MulAut.congr ψ α ∉
      inner (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
    rw [FixedFourGroup.congr_mem_inner_iff]
    exact hαo
  obtain ⟨hcases, -, -, hDinner⟩ := even_unitary_involution_matrix_lifts h hC hn hq _ hβ
  rcases hcases with hid | hbar
  · exfalso
    apply hβo
    refine hDinner _ ?_ hβ
    rw [← ker_primeFormFieldFactor h hC hn hq, MonoidHom.mem_ker]
    exact hid
  obtain ⟨-, -, C₀, hC₀, hcase₀, -, -, -, -, ⟨θ, -, hθβ⟩, -⟩ :=
    even_unitary_antiunitary_involution_descent h hC hn hq _ hβ hbar
  have hc : MulAut.congr θ (primeFormFieldHom h hC₀ (primeFormFieldFactor h hC hn hq
      (MulAut.congr ψ α))) = MulAut.congr ψ α := MulEquiv.ext fun x => (hθβ x).symm
  refine spFixedRankOrNoPComponent_of_mulEquiv ((fixedSubgroupCongrEquiv ψ α).trans
    ((MulEquiv.subgroupCongr (congrArg fixedSubgroup hc)).symm.trans
      (fixedSubgroupCongrEquiv θ _).symm)) ?_
  have := fixedField_finite h
  rcases F4Pilot.psu_fieldBar_cases h hn hq hC₀ hcase₀ _ hbar with ⟨r, hr1, hnr, ⟨Φ⟩⟩ | hch
  · exact Or.inl ⟨h.fixedField, inferInstance, inferInstance, r, h.card_fixedField, hr1, hnr,
      ⟨Φ⟩⟩
  · exact Or.inr (CatLeafProof.not_isPComponent_of_isCharacteristicP hch)

end Unitary

section Symplectic

open CFSG.LocalAnalysis.ComponentInitial SymplecticFlag SymplecticHigher
open CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.ComponentClassification.UnbalancedCatalog.SpChain

theorem psp_outer_fixed_rank {J : Type} [Group J] {n e : ℕ}
    (hadm : StatedLieAdmissible .PSp n 2 e) (hm : LieModel J .PSp n 2 e) (α : MulAut J)
    (hα : orderOf α = 2) (hαo : α ∉ (MulAut.conj : J →* MulAut J).range) :
    SpFixedRankOrNoPComponent (fixedSubgroup α) (e / 2) (fun r => r = n) ∨
      (IsSimpleGroup (fixedSubgroup α) ∧ StatedLieAdmissible .twistedB2 0 2 e ∧
        LieModel (fixedSubgroup α) .twistedB2 0 2 e) := by
  obtain ⟨K, _, _, hK, ⟨eJ⟩⟩ := CatLeafProof.nonempty_mulEquiv_psp_of_lieModel hadm hm
  have hf : 1 ≤ e := hadm.2.1
  have hn : 2 ≤ n := hadm.2.2.1
  have hnf : (n, 2 ^ e) ≠ (2, 2) := hadm.2.2.2
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  have : NeZero n := ⟨by omega⟩
  have : Finite J := Finite.of_equiv _ eJ.symm.toEquiv
  have hβ : orderOf (MulAut.congr eJ α) = 2 :=
    (orderOf_injective (MulAut.congr eJ).toMonoidHom (MulAut.congr eJ).injective α).trans hα
  have hβ2 : MulAut.congr eJ α * MulAut.congr eJ α = 1 := by
    rw [← sq, ← hβ, pow_orderOf_eq_one]
  have hβo : MulAut.congr eJ α ∉ inner (StatedProj (StatedSp n K)) := by
    rw [FixedFourGroup.congr_mem_inner_iff]
    exact hαo
  let Ψ := fixedSubgroupCongrEquiv eJ α
  have hE : MulAut.congr eJ α ∈ spSemilinearAutGroup n K →
      SpFixedRankOrNoPComponent (fixedSubgroup α) (e / 2) (fun r => r = n) := by
    intro hmem
    obtain ⟨g, σ, hgσ⟩ := exists_eq_spInner_mul_fieldAut hmem
    have hσ : σ ≠ 1 := by
      rintro rfl
      rw [map_one, mul_one] at hgσ
      exact hβo (hgσ ▸ spInner_mem_inner g)
    obtain ⟨k, _, _, hk, -, ⟨Φ⟩⟩ := F4Pilot.psp_field_fixed hn hf hK hβ2 g σ hgσ hσ
    exact Or.inl ⟨k, inferInstance, inferInstance, n, hk, by omega, rfl, ⟨Ψ.trans Φ⟩⟩
  by_cases hn3 : 3 ≤ n
  · left
    apply hE
    rw [(SymplecticHigher.automorphism_generation (K := K) hn3).1]
    exact mem_top _
  · obtain rfl : n = 2 := by omega
    obtain ⟨-, -, -, -, ⟨γ, hγ⟩, hall⟩ := even_symplectic_two_exterior_square_automorphism hf hK
    obtain ⟨-, -, -, -, -, -, -, -, -, -, heven, hodd⟩ := hall γ hγ
    rcases Nat.even_or_odd e with hfe | hfo
    · exact Or.inl (hE (heven hfe _ hβ))
    · obtain ⟨s, hs⟩ := hodd hfo _ hβ hβo
      obtain ⟨m, rfl⟩ := hfo
      have hm : 1 ≤ m := by
        by_contra h0
        obtain rfl : m = 0 := by omega
        exact hnf rfl
      rw [eq_exceptionalAut hγ] at hs
      obtain ⟨hS, hadmB, hLie⟩ := LinearPilot.psp_suzuki_fixed hm hK hβ2 s hs
      exact Or.inr ⟨Ψ.isSimpleGroup, hadmB, LieType.CurtisTits.lieModel_of_mulEquiv Ψ.symm hLie⟩

end Symplectic

end CFSG.SeitzReduction.RankOne
