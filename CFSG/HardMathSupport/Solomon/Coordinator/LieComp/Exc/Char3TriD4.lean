module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Char3Good
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.NotA6
public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.ExcTriThree
public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.ExcTriClassA

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Dickson.DefCharOuter.Export
  CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3

set_option linter.unusedSectionVars false


theorem isEmpty_alt6_adjointGroup_G2 {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f)
    {k : Type} [Field k] [Finite k] (hk : Nat.card k = ℓ ^ f) :
    IsEmpty (↥(adjointGroup Tag.G2 k) ≃* alternatingGroup (Fin 6)) := by
  have h3f : 3 ≤ ℓ ^ f := ExcTriClassA.three_le_pow_of_odd_prime hℓ hℓ2 hf
  have hZ : Subgroup.center (adjointGroup Tag.G2 k) = ⊥ := center_adjointGroup_eq_bot
  let eQ : ↥(adjointGroup Tag.G2 k) ≃* AdjointQuotient Tag.G2 k :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm
  let q₀ : TauCeti.PrimePower := ⟨ℓ, f, hℓ, hf⟩
  have hq₀ : Nat.card k = q₀.card := by rw [hk, TauCeti.PrimePower.card_def]
  have hv : (TauCeti.LieTypeIndex.G2 q₀).Valid := by
    refine (TauCeti.LieTypeIndex.valid_iff _).2 ⟨?_, ?_⟩
    · rw [TauCeti.LieTypeIndex.inStandardRange_iff]
      show 3 ≤ q₀.card
      rw [TauCeti.PrimePower.card_def]
      exact h3f
    · rw [TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
      exact fun h => h
  obtain ⟨φ⟩ := CFSG.TauCetiBridge.untwistedBridge_G2 q₀ hv hℓ2 k hq₀
  exact ⟨fun x => (isEmpty_cat_alt6 ⟨.G2 q₀, hv⟩ (Or.inl rfl)).false
    ((eQ.trans φ).symm.trans x)⟩

theorem char3Good_fixSubgroup_fieldActor {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (3 ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (3 ^ f)) :
    Char3Good ↥(fixSubgroup (fieldActor (t := TwistTag.D4) σ σ)) := by
  classical
  haveI := CFSG.HardMathSupport.Dickson.Sec6.I923.TriD4Aux.finite_graphFixedRootGroup_D4 σ
  have hs := isSimpleGroup_fixSubgroup_fieldActor_D4 3 f Nat.prime_three (by norm_num) K hK σ hσ
  have hnab := nonabelian_fixSubgroup_fieldActor_D4 3 f Nat.prime_three (by norm_num) K hK σ hσ
  obtain ⟨hchev, -, -⟩ := ExcTriClassA.chevFacts_fixSubgroup_fieldActor_D4 Nat.prime_three
    (by norm_num) hf hK σ hσ
  have hcard : Nat.card (fixSubfield σ) = 3 ^ f :=
    CFSG.RankThree.PartOne.KGD.card_fixSubfield_cube Nat.prime_three hf hK σ hσ
  haveI : Finite (fixSubfield σ) := Subtype.finite
  have hG2 := isEmpty_alt6_adjointGroup_G2 Nat.prime_three (by norm_num) hf hcard
  let e := ExcTriClassA.fixSubgroupFieldActorEquivG2 Nat.prime_three (by norm_num) hf hK σ hσ
  exact Char3Good.of_simple hnab hchev ⟨fun x => hG2.false (e.symm.trans x)⟩

theorem char3Good_fixSubgroup_trialityD4 {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    [CharP K 3] (hK : Nat.card K = (3 ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (3 ^ f))
    (β : MulAut ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) (hβ3 : β ^ 3 = 1)
    (hout : β ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
    Char3Good ↥(fixSubgroup β) := by
  classical
  haveI := CFSG.HardMathSupport.Dickson.Sec6.I923.TriD4Aux.finite_graphFixedRootGroup_D4 σ
  exact three_of_classes_gen hf hK σ hσ (fun γ => Char3Good ↥(fixSubgroup γ))
    (fun ε γ h => Char3Good.of_conj_aut ε γ h) (fun γ h => Char3Good.of_inv γ h)
    (char3Good_fixSubgroup_fieldActor hf hK σ hσ)
    (fun hc hc0 => Char3Good.of_noComponent (exc_noComponent_classB hf hK σ hσ hc hc0))
    β hβ3 hout

theorem lieCompExport_char3_outer_trialityD4 :
    ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
      ∀ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid), q.p = 3 →
        Nonempty (S ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hv⟩).Group) →
        ∀ β : MulAut S, β ^ 3 = 1 → (∀ a : S, MulAut.conj a ≠ β) →
          LieCompExport 3 β ∨ NoThreeComponents β := by
  intro S _ _ _ _ q hv hq3 ⟨e⟩ β hβ3 hout
  classical
  obtain ⟨f, hf, K, _, _, σ, hK, hσ, ⟨e₁⟩⟩ := exc_exists_graphFixed_of_tauCeti q hv e hq3
  haveI : CharP K 3 := exc_charP_three_of_card K hK
  haveI : Finite (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
    Finite.of_equiv S e₁.toEquiv
  refine lieCompExport_or_noThreeComponents_of_char3Good β
    (Char3Good.of_mulEquiv (fixSubgroupCongrEquiv e₁ β) ?_)
  have hαp : MulAut.congr e₁ β ^ 3 = 1 := by rw [← map_pow, hβ3, map_one]
  have hαin : MulAut.congr e₁ β ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
    rintro ⟨g, hg⟩
    refine hout (e₁.symm g) ?_
    apply (MulAut.congr e₁).injective
    rw [CFSG.ComponentClassification.OuterAutomorphisms.congr_conj, e₁.apply_symm_apply]
    exact hg
  exact char3Good_fixSubgroup_trialityD4 hf hK σ hσ _ hαp hαin

theorem lieCompExport_char3_outer_of_trialityD4_idx :
    ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
      ∀ idx : TauCeti.ValidLieTypeIndex, (∃ q, idx.1 = .trialityD4 q) → lieIndexChar idx.1 = 3 →
        Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group) →
        ∀ β : MulAut S, β ^ 3 = 1 → (∀ a : S, MulAut.conj a ≠ β) →
          LieCompExport 3 β ∨ NoThreeComponents β := by
  intro S _ _ hs hna idx ⟨q, hq⟩ h3 he β hβ hout
  obtain ⟨d, hv⟩ := idx
  have hq' : d = .trialityD4 q := hq
  subst hq'
  exact lieCompExport_char3_outer_trialityD4 S hs hna q hv h3 he β hβ hout

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
