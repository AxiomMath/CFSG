module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcFieldOrders
public import CFSG.RankThree.PartOne.KE.OddE6NoninnerCore
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcFieldEntrywise

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.DefChar CFSG.LieType.SeitzGeneration CFSG.LieType.Chevalley
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.TauCetiBridge CFSG.RankThree.Chevalley
open CFSG.LocalAnalysis.ComponentInitial (finite_field_prime_power_characteristic)

section Rational


theorem fixer_of_rational {τ : Tag} {K : Type} [Field K] [Finite K] (σ : K ≃+* K)
    (hfixer : ∀ (k : Subfield K) (S : Subgroup (MulAut (adjointGroup τ K))),
      S = fixingSubgroup (MulAut (adjointGroup τ K))
          {j : adjointGroup τ K | (j : ModGL τ K) ∈
            (adjointGroup τ k).map (baseChangeGL k.subtype)} →
        (S : Set (MulAut (adjointGroup τ K))) =
            Set.range (fun σ : K ≃ₐ[k] K => entrywiseAdjointAut τ σ.toRingEquiv) ∧
          IsCyclic S ∧ Nat.card S = Module.finrank k K) :
    ∀ β : MulAut (adjointGroup τ K),
      (∀ j : adjointGroup τ K, (j : ModGL τ K) ∈ fixedFieldImage τ σ → β j = j) →
        ∃ η : K ≃+* K, (∀ c, σ c = c → η c = c) ∧ β = entrywiseAdjointAut τ η := by
  intro β hβ
  have hS := (hfixer (fixSubfield σ) _ rfl).1
  have hβS : β ∈ ((fixingSubgroup (MulAut (adjointGroup τ K))
      {j : adjointGroup τ K | (j : ModGL τ K) ∈
        (adjointGroup τ (fixSubfield σ)).map (baseChangeGL (fixSubfield σ).subtype)} :
          Subgroup (MulAut (adjointGroup τ K))) : Set (MulAut (adjointGroup τ K))) :=
    (mem_fixingSubgroup_iff _).2 fun j hj => hβ j hj
  rw [hS] at hβS
  obtain ⟨σ', rfl⟩ := hβS
  refine ⟨σ'.toRingEquiv, fun c hc => ?_, rfl⟩
  have h1 := σ'.commutes (⟨c, hc⟩ : fixSubfield σ)
  exact h1

theorem fieldCoreAt_E7_odd {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f) (K : Type)
    [Field K] (hK : Nat.card K = ℓ ^ f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hdvd : ∀ σ : K ≃+* K, orderOf σ = p →
      ¬ Nat.Coprime p (Nat.card (adjointGroup Tag.E7 (fixSubfield σ))))
    {x : MulAut (adjointGroup Tag.E7 K)} (hxp : orderOf x = p)
    (hxo : x ∉ (MulAut.conj : adjointGroup Tag.E7 K →* MulAut (adjointGroup Tag.E7 K)).range) :
    FieldCoreAt p x := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hℓ.pos f).ne')
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : CharP K ℓ := finite_field_prime_power_characteristic hℓ hf hK
  have : Fact p.Prime := ⟨hp⟩
  have : CharP (AlgebraicClosure K) ℓ :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective ℓ
  have hαp : orderOf (⟨x, Subgroup.mem_top x⟩ :
      (⊤ : Subgroup (MulAut (adjointGroup Tag.E7 K)))) = p := by
    rw [Subgroup.orderOf_mk]
    exact hxp
  obtain ⟨-, ⟨σ, δ, hσp, hδ⟩, -⟩ :=
    odd_E7_noninner_odd_prime_field_descent_and_local_core_trivial hℓ hℓ2 hf K hK hp hp2 ⊤ le_top
      ⟨x, Subgroup.mem_top x⟩ hxo hαp
  obtain ⟨-, -, -, -, ρ, -, -, -, -, -, -, -, -, hfixer⟩ :=
    CFSG.RankThree.OddE7Rational.odd_E7_rational_inner_diagonal_field_automorphism_structure hℓ
      hℓ2 hf K hK (AlgebraicClosure K) (iterateFrobenius (AlgebraicClosure K) ℓ f)
      (fun c => by rw [iterateFrobenius_def, hK]) _ _ rfl rfl
  obtain ⟨hJC, hsimple, hnc, -, hNδ, hnormal, hcent⟩ :=
    odd_entrywise_canonical_core_data_of_fixer (τ := .E7) hℓ2 σ (fixer_of_rational σ hfixer)
  exact fieldCoreAt_of_conj (fieldCoreAt_entrywise_of_data hσp hJC hsimple hnc hNδ hnormal hcent
    (hdvd σ hσp)) δ hδ

theorem fieldCoreAt_E6_odd {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f) (K : Type)
    [Field K] (hK : Nat.card K = ℓ ^ f) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hdvd : ∀ σ : K ≃+* K, orderOf σ = p →
      ¬ Nat.Coprime p (Nat.card (adjointGroup Tag.E6 (fixSubfield σ))))
    {x : MulAut (adjointGroup Tag.E6 K)} (hxp : orderOf x = p)
    (hxo : x ∉ (MulAut.conj : adjointGroup Tag.E6 K →* MulAut (adjointGroup Tag.E6 K)).range) :
    FieldCoreAt p x := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hℓ.pos f).ne')
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : CharP K ℓ := finite_field_prime_power_characteristic hℓ hf hK
  have : Fact p.Prime := ⟨hp⟩
  have : CharP (AlgebraicClosure K) ℓ :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective ℓ
  have hαp : orderOf (⟨x, Subgroup.mem_top x⟩ :
      (⊤ : Subgroup (MulAut (adjointGroup Tag.E6 K)))) = p := by
    rw [Subgroup.orderOf_mk]
    exact hxp
  obtain ⟨-, ⟨σ, δ, hσp, hδ⟩, -⟩ :=
    CFSG.RankThree.PartOne.KE.odd_E6_noninner_large_prime_field_descent_and_local_core_trivial hℓ
      hℓ2 hf K hK hp hp3 ⊤ le_top ⟨x, Subgroup.mem_top x⟩ hxo hαp
  obtain ⟨-, -, -, -, ρ, -, -, -, -, -, -, -, -, -, -, -, hfixer⟩ :=
    CFSG.RankThree.PartOne.KE.odd_E6_rational_inner_diagonal_graph_field_automorphism_structure
      hℓ hℓ2 hf K hK (AlgebraicClosure K) (iterateFrobenius (AlgebraicClosure K) ℓ f)
      (fun c => by rw [iterateFrobenius_def, hK]) _ _ rfl rfl
  obtain ⟨hJC, hsimple, hnc, -, hNδ, hnormal, hcent⟩ :=
    odd_entrywise_canonical_core_data_of_fixer (τ := .E6) hℓ2 σ (fixer_of_rational σ hfixer)
  exact fieldCoreAt_of_conj (fieldCoreAt_entrywise_of_data hσp hJC hsimple hnc hNδ hnormal hcent
    (hdvd σ hσp)) δ hδ

end Rational

section Balance


theorem isLocallyBalancedAbs_adjointE7_fieldOdd {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hf : 1 ≤ f) (K : Type) [Field K] (hK : Nat.card K = ℓ ^ f) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hcnt : degCount Tag.E7 (orderOf ((Nat.card K : ℕ) : ZMod p)) = 2) :
    IsLocallyBalancedAbs p 3 (adjointGroup Tag.E7 K) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hℓ.pos f).ne')
  refine isLocallyBalancedAbs_adjoint_of_fieldCore K hp
    (rankLE2_E7_of_degCount_eq_two K hp hcnt) fun x hxp hxo => ?_
  refine fieldCoreAt_E7_odd hℓ hℓ2 hf K hK hp hp2
    (fun σ hσp => not_coprime_card_adjointE7 (fixSubfield σ) hp ?_) hxp hxo
  rw [card_fixSubfield_cast hℓ hf hK hp hσp]
  exact hcnt

theorem isLocallyBalancedAbs_adjointE6_fieldOdd {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hf : 1 ≤ f) (K : Type) [Field K] (hK : Nat.card K = ℓ ^ f) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hcnt : degCount Tag.E6 (orderOf ((Nat.card K : ℕ) : ZMod p)) = 2) :
    IsLocallyBalancedAbs p 3 (adjointGroup Tag.E6 K) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hℓ.pos f).ne')
  refine isLocallyBalancedAbs_adjoint_of_fieldCore K hp
    (rankLE2_E6_of_degCount_eq_two K hp hcnt) fun x hxp hxo => ?_
  refine fieldCoreAt_E6_odd hℓ hℓ2 hf K hK hp hp3
    (fun σ hσp => not_coprime_card_adjointE6 (fixSubfield σ) hp ?_) hxp hxo
  rw [card_fixSubfield_cast hℓ hf hK hp hσp]
  exact hcnt

end Balance

section Family


theorem crossCharFamAt_E7_fieldOdd :
    CrossCharFamAt .E7 (regimeExcFieldOdd TauCeti.LieTypeIndex.E7 (degCount Tag.E7)) := by
  rintro ⟨d, hv⟩ _ p hp hp2 hc ⟨q, hd, hcnt, hpf, hq2⟩
  change d = _ at hd
  subst hd
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e7 q hv
  rw [← hK] at hcnt
  exact IsLocallyBalancedAbs.of_mulEquiv e (isLocallyBalancedAbs_adjointE7_fieldOdd q.prime_p hq2
    q.exponent_pos K (hK.trans (TauCeti.PrimePower.card_def q)) hp hp2 hcnt)

theorem crossCharFamAt_E6_fieldOdd :
    CrossCharFamAt .E6 (regimeExcFieldOdd TauCeti.LieTypeIndex.E6 (degCount Tag.E6)) := by
  rintro ⟨d, hv⟩ _ p hp hp2 hc ⟨q, hd, hcnt, hpf, hq2⟩
  change d = _ at hd
  subst hd
  have hpq : p ≠ q.p := fun h => hc (by simp [h])
  have hp5 := five_le_of_count_le (k := 2) (by decide) hp hp2 (not_dvd_card_of_ne hp hpq) hcnt.le
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e6 q hv
  rw [← hK] at hcnt
  exact IsLocallyBalancedAbs.of_mulEquiv e (isLocallyBalancedAbs_adjointE6_fieldOdd q.prime_p hq2
    q.exponent_pos K (hK.trans (TauCeti.PrimePower.card_def q)) hp (by omega) hcnt)

end Family

end CFSG.HardMathSupport.Timmesfeld.CrossChar
