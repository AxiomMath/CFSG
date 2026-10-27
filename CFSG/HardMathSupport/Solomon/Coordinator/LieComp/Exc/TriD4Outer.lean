module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TriD4
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.GroupsFine
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.G2Subgroup

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec8
  CFSG.PGLModel

set_option linter.unusedSectionVars false


theorem ringChar_subfield {K : Type} [Field K] {ℓ : ℕ} (hℓ : ringChar K = ℓ) (k : Subfield K) :
    ringChar k = ℓ := by
  haveI : CharP K ℓ := hℓ ▸ ringChar.charP K
  haveI : CharP k ℓ := (k.subtype.charP_iff k.subtype_injective ℓ).2 inferInstance
  exact ringChar.eq k ℓ

noncomputable def fixSubgroupConjEquiv {Y : Type*} [Group Y] (β α : MulAut Y) :
    ↥(fixSubgroup α) ≃* ↥(fixSubgroup (β * α * β⁻¹)) := by
  have hc : MulAut.congr (β : Y ≃* Y) α = β * α * β⁻¹ := by
    ext x
    rfl
  exact (fixSubgroupCongrEquiv (β : Y ≃* Y) α).trans (MulEquiv.subgroupCongr (by rw [hc]))

theorem nonempty_fixSubgroup_fieldActor_equiv_G2 {ℓ f : ℕ} [Fact ℓ.Prime] (hℓ3 : ℓ ≠ 3)
    (hf : 1 ≤ f) (hℓ2 : ℓ = 2 ∨ 5 ≤ ℓ) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) :
    Nonempty (↥(fixSubgroup (fieldActor (t := TwistTag.D4) σ σ)) ≃*
      ↥(adjointGroup Tag.G2 (fixSubfield σ))) := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  have hK3 : Nat.card K = ℓ ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  haveI : CharP K ℓ := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    hℓ (by omega) hK3
  rcases hℓ2 with rfl | h5
  · obtain ⟨e⟩ := KFacts.nonempty_fixedPoints_fieldActor_mulEquiv_g2 (σ := σ)
      (ringChar.eq K 2)
    have hfix : fixSubgroup (fieldActor (t := TwistTag.D4) σ σ) =
        (fieldActor (t := TwistTag.D4) σ σ).toMonoidHom.eqLocus (MonoidHom.id _) :=
      Subgroup.ext fun _ => Iff.rfl
    exact ⟨(MulEquiv.subgroupCongr hfix).trans e⟩
  · have hσ3 : ∀ c, σ (σ (σ c)) = c := CFSG.LieType.Chevalley.ringEquiv_cube_apply_eq hK hσ
    have hp2 : ℓ ≠ 2 := by omega
    have hJC := GH74.GLS.Stage2.Bender.Thm1.d4_trialityFieldImage_self_le σ
    have hFJ : (fixSubgroup (fieldActor (t := TwistTag.D4) σ σ)).map
        (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype = trialityFieldImage σ σ := by
      ext x
      constructor
      · rintro ⟨g, hg, rfl⟩
        exact (GH74.GLS.Stage2.Bender.Thm1.d4_mem_trialityFieldImage_self_iff σ hσ3 g).2 hg
      · intro hx
        exact ⟨⟨x, hJC hx⟩,
          (GH74.GLS.Stage2.Bender.Thm1.d4_mem_trialityFieldImage_self_iff σ hσ3 _).1 hx, rfl⟩
    let e : ↥(fixSubgroup (fieldActor (t := TwistTag.D4) σ σ)) ≃* ↥(trialityFieldImage σ σ) :=
      (Subgroup.equivMapOfInjective _ (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype
        Subtype.val_injective).trans (MulEquiv.subgroupCongr hFJ)
    have hk3 : (3 : ℕ∞) ≤ ENat.card (fixSubfield σ) := by
      obtain ⟨q, hqp, hqcard⟩ := exists_primePower_card_subfield (ringChar.eq K ℓ) (fixSubfield σ)
      haveI : Finite (fixSubfield σ) := Subtype.finite
      rw [ENat.card_eq_coe_natCard (fixSubfield σ)]
      have h3 : 3 ≤ q.card := by
        rw [TauCeti.PrimePower.card_def]
        calc 3 ≤ 5 := by norm_num
          _ ≤ ℓ := h5
          _ = q.p := hqp.symm
          _ ≤ q.p ^ q.exponent := Nat.le_self_pow q.exponent_pos.ne' _
      rw [hqcard]
      exact_mod_cast h3
    exact ⟨e.trans (Seitz.TrialityOdd.Inner.trialityFieldImageEquivG2 σ hk3)⟩

theorem charP_of_card_pow_three {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 3) : CharP K ℓ := by
  have hK3 : Nat.card K = ℓ ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  exact CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hℓ
    (by omega) hK3

theorem compsWith_fixSubgroup_fieldActor {P : (X : Type) → [Group X] → Prop}
    (hP : IsComponentProperty P) {ℓ f : ℕ} [Fact ℓ.Prime] (hℓ3 : ℓ ≠ 3) (hf : 1 ≤ f)
    (hℓ2 : ℓ = 2 ∨ 5 ≤ ℓ) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 3)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (hPG2 : CompsWith P ↥(adjointGroup Tag.G2 (fixSubfield σ))) :
    CompsWith P ↥(fixSubgroup (fieldActor (t := TwistTag.D4) σ σ)) := by
  obtain ⟨e⟩ := nonempty_fixSubgroup_fieldActor_equiv_G2 hℓ3 hf hℓ2 hK σ hσ
  exact CompsWith.of_mulEquiv hP e hPG2

theorem compsFine_fixSubgroup_fieldActor {ℓ f : ℕ} [Fact ℓ.Prime] (hℓ3 : ℓ ≠ 3) (hf : 1 ≤ f)
    (hℓ2 : ℓ = 2 ∨ 5 ≤ ℓ) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 3)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) :
    CompsFine ℓ ↥(fixSubgroup (fieldActor (t := TwistTag.D4) σ σ)) := by
  rw [compsFine_iff_compsWith]
  haveI : CharP K ℓ := charP_of_card_pow_three Fact.out hf hK
  haveI : Finite (fixSubfield σ) := Subtype.finite
  refine compsWith_fixSubgroup_fieldActor (isComponentProperty_componentFactor ℓ) hℓ3 hf hℓ2 hK σ
    hσ ?_
  exact (compsFine_iff_compsWith _ _).1
    (compsFine_adjointGroup_G2 (ringChar_subfield (ringChar.eq K ℓ) (fixSubfield σ)))

@[expose] def TrialityOddA2Comps : Prop :=
  ∀ (ℓ f : ℕ) [Fact ℓ.Prime], 5 ≤ ℓ → 1 ≤ f → ∀ (K₃ : Type) [Field K₃] [Finite K₃],
    Nat.card K₃ = (ℓ ^ f) ^ 3 → ∀ (Fr : K₃ ≃+* K₃), (∀ c, Fr c = c ^ (ℓ ^ f)) →
    ∀ φ : MulAut ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom), φ ^ 3 = 1 →
      φ ∉ (MulAut.conj : ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom) →*
        MulAut ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom)).range →
      (¬ ∃ β : MulAut ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom),
        φ = β * fieldActor (t := TwistTag.D4) Fr Fr * β⁻¹ ∨
          φ = β * (fieldActor (t := TwistTag.D4) Fr Fr)⁻¹ * β⁻¹) →
      CompsFine ℓ ↥(fixSubgroup φ)

@[expose] def TrialityOddA2CompsWith (P : (X : Type) → [Group X] → Prop) (ℓ f : ℕ) [Fact ℓ.Prime] :
    Prop :=
  5 ≤ ℓ → 1 ≤ f → ∀ (K₃ : Type) [Field K₃] [Finite K₃],
    Nat.card K₃ = (ℓ ^ f) ^ 3 → ∀ (Fr : K₃ ≃+* K₃), (∀ c, Fr c = c ^ (ℓ ^ f)) →
    ∀ φ : MulAut ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom), φ ^ 3 = 1 →
      φ ∉ (MulAut.conj : ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom) →*
        MulAut ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom)).range →
      (¬ ∃ β : MulAut ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom),
        φ = β * fieldActor (t := TwistTag.D4) Fr Fr * β⁻¹ ∨
          φ = β * (fieldActor (t := TwistTag.D4) Fr Fr)⁻¹ * β⁻¹) →
      CompsWith P ↥(fixSubgroup φ)

theorem compsWith_triality_outer {P : (X : Type) → [Group X] → Prop}
    (hP : IsComponentProperty P) {ℓ f : ℕ} [Fact ℓ.Prime]
    (hodd : TrialityOddA2CompsWith P ℓ f)
    (hPG2 : ∀ {F : Type} [Field F] [Finite F], Nat.card F = ℓ ^ f →
      CompsWith P ↥(adjointGroup Tag.G2 F))
    (hPGL : ∀ {F : Type} [Field F] [Finite F] (π : Bool), (π = true → 2 < ℓ ^ f) →
      Nat.card F = Sec4.piCard π (ℓ ^ f) →
      CompsWith P ↥(projImage (Sec4.glPi π 3 (ℓ ^ f) F)))
    (hℓ3 : ℓ ≠ 3) (hf : 1 ≤ f) {K₃ : Type} [Field K₃] [Finite K₃]
    (hK₃ : Nat.card K₃ = (ℓ ^ f) ^ 3) (Fr : K₃ ≃+* K₃) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f))
    (φ : MulAut ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom)) (hφ3 : φ ^ 3 = 1)
    (hφ : φ ∉ (MulAut.conj : ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom) →*
      MulAut ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom)).range) :
    CompsWith P ↥(fixSubgroup φ) := by
  have hℓ : ℓ.Prime := Fact.out
  have hℓ2 : ℓ = 2 ∨ 5 ≤ ℓ := by
    have h2 := hℓ.two_le
    by_cases h5 : 5 ≤ ℓ
    · exact Or.inr h5
    · left
      have h4 : ℓ ≠ 4 := fun h => by rw [h] at hℓ; exact absurd hℓ (by norm_num)
      omega
  have hq : 2 ≤ ℓ ^ f := by
    have h3 : ℓ ≤ ℓ ^ f := Nat.le_self_pow (by omega) ℓ
    have h4 := hℓ.two_le
    omega
  have hF : Nat.card (fixSubfield Fr) = ℓ ^ f :=
    CFSG.GH74.GLS.Stage4.Hex.card_fixedField_of_cube Fr.toRingHom hq hK₃ hFr
  haveI : Finite (fixSubfield Fr) := Subtype.finite
  have hG2 := compsWith_fixSubgroup_fieldActor hP hℓ3 hf hℓ2 hK₃ Fr hFr (hPG2 hF)
  by_cases hconj : ∃ β : MulAut ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom),
      φ = β * fieldActor (t := TwistTag.D4) Fr Fr * β⁻¹ ∨
        φ = β * (fieldActor (t := TwistTag.D4) Fr Fr)⁻¹ * β⁻¹
  · obtain ⟨β, hβ | hβ⟩ := hconj
    · rw [hβ]
      exact CompsWith.of_mulEquiv hP (fixSubgroupConjEquiv β _).symm hG2
    · rw [hβ]
      exact CompsWith.of_mulEquiv hP ((fixSubgroupConjEquiv β _).symm.trans
        (MulEquiv.subgroupCongr (fixSubgroup_inv_eq _))) hG2
  · rcases hℓ2 with rfl | h5
    · rcases Item8KFacts2Proof.isStdGraphFieldConj_or_nonempty_autFix_equiv hf hK₃ hFr hφ3 hφ with
        hstd | he₂
      · exact absurd hstd hconj
      · obtain ⟨e₂⟩ := he₂
        have hfixφ : fixSubgroup φ = Sec4.autFix φ := Subgroup.ext fun _ => Iff.rfl
        let ef : ↥(fixSubgroup φ) ≃* ↥(Sec4.autFix φ) := MulEquiv.subgroupCongr hfixφ
        rcases Nat.even_or_odd f with hfe | hfo
        · obtain ⟨F, _, _, hF', ⟨e₃⟩⟩ := kF82D4SecondCentY0Even_holds f hfe hf K₃ Fr hK₃ hFr
          have hf2 : 2 ≤ f := by
            obtain ⟨k, hk⟩ := hfe
            omega
          have h2 : 2 < 2 ^ f :=
            lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) hf2)
          exact CompsWith.of_mulEquiv hP (ef.trans (e₂.trans e₃))
            (hPGL (π := true) (fun _ => h2) hF')
        · obtain ⟨F, _, _, hF', ⟨e₃⟩⟩ := kF82D4SecondCentY0_holds f hfo K₃ Fr hK₃ hFr
          exact CompsWith.of_mulEquiv hP (ef.trans (e₂.trans e₃))
            (hPGL (π := false) (fun h => absurd h (by decide)) hF')
    · exact hodd h5 hf K₃ hK₃ Fr hFr φ hφ3 hφ hconj

theorem compsFine_triality_outer (hodd : TrialityOddA2Comps) {ℓ f : ℕ} [Fact ℓ.Prime] (hℓ3 : ℓ ≠ 3)
    (hf : 1 ≤ f) {K₃ : Type} [Field K₃] [Finite K₃] (hK₃ : Nat.card K₃ = (ℓ ^ f) ^ 3)
    (Fr : K₃ ≃+* K₃) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f))
    (φ : MulAut ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom)) (hφ3 : φ ^ 3 = 1)
    (hφ : φ ∉ (MulAut.conj : ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom) →*
      MulAut ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom)).range) :
    CompsFine ℓ ↥(fixSubgroup φ) := by
  rw [compsFine_iff_compsWith]
  refine compsWith_triality_outer (isComponentProperty_componentFactor ℓ) ?_ ?_ ?_ hℓ3 hf hK₃ Fr hFr
    φ hφ3 hφ
  · intro h5 hf' K₃' _ _ hK₃' Fr' hFr' φ' hφ3' hφ' hconj'
    exact (compsFine_iff_compsWith _ _).1 (hodd ℓ f h5 hf' K₃' hK₃' Fr' hFr' φ' hφ3' hφ' hconj')
  · intro F _ _ hF
    haveI : Fintype F := Fintype.ofFinite F
    have hFc : Fintype.card F = ℓ ^ f := by rw [← Nat.card_eq_fintype_card]; exact hF
    have hcharP : CharP F ℓ := charP_of_card_eq_prime_pow hFc
    exact (compsFine_iff_compsWith _ _).1 (compsFine_adjointGroup_G2 (ringChar.eq F ℓ))
  · intro F _ _ π hπ2 hF
    exact (compsFine_iff_compsWith _ _).1 (compsFine_projImage_glPi (π := π) (p := ℓ) (f := f)
      ⟨Fact.out, hf, hF⟩ hπ2)

theorem trialityOuterExport_of (hodd : TrialityOddA2Comps) : TrialityOuterExport := by
  intro ℓ f _ hℓ3 hf K₃ _ _ hK₃ Fr hFr φ hφ3 hφ
  exact lieCompExport_of_compsFine
    (D4Dual.perfectInLayer_triality_outer_three hℓ3 hf hK₃ Fr hFr φ hφ3 hφ)
    (compsFine_triality_outer hodd hℓ3 hf hK₃ Fr hFr φ hφ3 hφ)

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
