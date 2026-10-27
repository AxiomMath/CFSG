module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxOrthogonal
public import CFSG.LocalAnalysis.ComponentClassification.InnAutDerivedD4
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TriA2Minus
public import CFSG.Adapters.CatalogueFieldBridges.Exceptional

public section

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp.TriA2
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec8
  CFSG.RankThree.PartTwo.Sec4 CFSG.PGLModel CFSG.LocalAnalysis.ComponentInitial
  CFSG.HardMathSupport.Lang.D4Three
open scoped MatrixGroups

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie


theorem isComponentProperty_catalogueOver (ℓ q : ℕ) :
    IsComponentProperty (CatalogueOver ℓ q) where
  of_mulEquiv := fun e h => h.of_mulEquiv e

theorem catalogueOver_adjointGroup_G2 {ℓ f : ℕ} [Fact ℓ.Prime] (hf : 1 ≤ f)
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = ℓ ^ f) (hF3 : 3 ≤ Nat.card F) :
    CatalogueOver ℓ (ℓ ^ f) ↥(adjointGroup Tag.G2 F) := by
  classical
  haveI : Fintype F := Fintype.ofFinite F
  let q : TauCeti.PrimePower := ⟨ℓ, f, Fact.out, hf⟩
  have hq : Nat.card F = q.card := by
    rw [hF]
    exact (TauCeti.PrimePower.card_def q).symm
  have hv : (TauCeti.LieTypeIndex.G2 q).Valid := by
    refine (TauCeti.LieTypeIndex.valid_iff _).2 ⟨?_, ?_⟩
    · have h3 : 3 ≤ q.card := by rw [← hq]; exact hF3
      simpa [TauCeti.LieTypeIndex.inStandardRange_iff, TauCeti.PrimePower.card_def] using h3
    · simp [TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
  obtain ⟨e⟩ := CFSG.Adapters.CatalogueFieldBridges.nonempty_adjointGroup_catEquiv
    CFSG.TauCetiBridge.Even.chevalleyBridgesAll.g2 hv hq
  have hZ : Subgroup.center ↥(adjointGroup Tag.G2 F) = ⊥ := center_adjointGroup_eq_bot
  refine ⟨.lie ⟨.G2 q, hv⟩, ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans
    QuotientGroup.quotientBot).trans e⟩, ?_⟩
  · refine Or.inl ⟨?_, ?_, ?_⟩
    · exact TauCeti.LieTypeIndex.characteristic_G2 q
    · simp only [fieldSize]
      exact hq.symm.trans hF
    · simp [suzRee]

theorem exists_ne_comm_commutator_adjointGroup_G2_two {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2) :
    ∃ a b : ↥(commutator ↥(adjointGroup Tag.G2 F)), a * b ≠ b * a := by
  obtain ⟨hDs, hDcard⟩ := ExcCopy.g2Two_derived_exc hF
  haveI := hDs
  by_contra hcon
  push Not at hcon
  let _ : CommGroup ↥(commutator ↥(adjointGroup Tag.G2 F)) :=
    { (inferInstance : Group ↥(commutator ↥(adjointGroup Tag.G2 F))) with mul_comm := hcon }
  have hp := IsSimpleGroup.prime_card (α := ↥(commutator ↥(adjointGroup Tag.G2 F)))
  rw [hDcard] at hp
  exact absurd hp (by norm_num)

theorem catalogueOver_commutator_adjointGroup_G2_two {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2) :
    CatalogueOver 2 2 ↥(commutator ↥(adjointGroup Tag.G2 F)) := by
  classical
  have hLie := CFSG.Quasithin.EmptyFaithfulMultiple.g2TwoDerivedUnitaryTransport_holds F hF
  obtain ⟨hDs, -⟩ := ExcCopy.g2Two_derived_exc hF
  haveI := hDs
  have hDnc := exists_ne_comm_commutator_adjointGroup_G2_two hF
  have hZ : Subgroup.center ↥(commutator ↥(adjointGroup Tag.G2 F)) = ⊥ :=
    b3Lie_center_eq_bot hDnc
  rcases hLie with ⟨-, hM⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · obtain ⟨hp, hf, hv, ⟨e⟩⟩ := nonempty_equiv_catalog_psu _ 2 3 1 hM
    have hDM : (commutator ↥(adjointGroup .G2 F)).map (adjointGroup .G2 F).subtype =
        ⁅adjointGroup .G2 F, adjointGroup .G2 F⁆ := by
      rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype]
    let eD : ↥(commutator ↥(adjointGroup .G2 F)) ≃*
        ↥⁅adjointGroup .G2 F, adjointGroup .G2 F⁆ :=
      ((commutator ↥(adjointGroup .G2 F)).equivMapOfInjective _
        (adjointGroup .G2 F).subtype_injective).trans (MulEquiv.subgroupCongr hDM)
    refine ⟨TauCeti.CFSGIndex.lie ⟨_, hv⟩,
      ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans
        (eD.trans e)⟩, ?_⟩
    exact Or.inr (Or.inl ⟨rfl, rfl, Or.inr
      ⟨⟨3, 1, hp, hf⟩, rfl, by simp [TauCeti.PrimePower.card_def]⟩⟩)
  all_goals exact absurd h0 (by norm_num)

theorem compsWith_catalogueOver_adjointGroup_G2 {ℓ f : ℕ} [Fact ℓ.Prime] (hf : 1 ≤ f)
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = ℓ ^ f) :
    CompsWith (CatalogueOver ℓ (ℓ ^ f)) ↥(adjointGroup Tag.G2 F) := by
  classical
  haveI : Fintype F := Fintype.ofFinite F
  by_cases h2 : Nat.card F = 2
  · obtain ⟨hDs, -⟩ := ExcCopy.g2Two_derived_exc h2
    haveI := hDs
    have hpow : ℓ ^ f = 2 := hF.symm.trans h2
    obtain ⟨hℓ, hf1⟩ := Nat.prime_two.pow_eq_iff.mp hpow
    subst hℓ
    subst hf1
    exact compsWith_of_commutator
      (LieSemisimple.isQuasisimple_of_isSimpleGroup hDs
        (exists_ne_comm_commutator_adjointGroup_G2_two h2))
      (catalogueOver_commutator_adjointGroup_G2_two h2)
  · have hF3 : 3 ≤ Nat.card F := by
      have h1 : 1 < Nat.card F := Finite.one_lt_card
      omega
    have hperf := ExcCopy.isPerfect_adjointGroup .G2 F (fun _ => hF3)
    obtain ⟨hs, hnc⟩ := ExcCopy.isSimpleGroup_adjointGroup_of_perfect .G2 F hperf
    haveI := hs
    exact compsWith_of_simple (isComponentProperty_catalogueOver ℓ (ℓ ^ f)) hnc
      (catalogueOver_adjointGroup_G2 hf hF hF3)

theorem catalogueOver_projImage_slPi {π : Bool} {p f : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Sec4.PiField π p f K) (hq2 : 2 < p ^ f) :
    CatalogueOver p (p ^ f) ↥(projImage (Sec4.slPi π 3 (p ^ f) K)) := by
  classical
  haveI := hK.finite
  haveI : Fintype K := Fintype.ofFinite K
  have hp := hK.prime
  haveI : Fact p.Prime := ⟨hp⟩
  let g₀ : ↥(Sec4.slPi π 3 (p ^ f) K) →* ↥(projImage (Sec4.slPi π 3 (p ^ f) K)) :=
    (Matrix.ProjGenLinGroup.mk : GL (Fin 3) K →* _).subgroupMap (Sec4.slPi π 3 (p ^ f) K)
  have hg₀ : Function.Surjective g₀ := MonoidHom.subgroupMap_surjective _ _
  have hg₀k := ker_subgroupMap_mk_le_center (Sec4.slPi π 3 (p ^ f) K)
  cases π
  · have hKcard : Fintype.card K = (p ^ f) ^ 2 := by
      rw [← Nat.card_eq_fintype_card, hK.card]
      rfl
    have hcharP : CharP K p :=
      charP_of_card_eq_prime_pow (f := 2 * f) (by rw [hKcard, ← pow_mul, mul_comm])
    have hring : ringChar K = p := ringChar.eq K p
    have hmq : ((3 : ℕ), p ^ f) ≠ ((3 : ℕ), 2) := fun h => by
      have := (Prod.mk.inj h).2
      omega
    have hcat := catalogueOver_of_surjective_su hKcard (by norm_num) hmq g₀ hg₀ hg₀k
    rwa [hring] at hcat
  · have hKcard : Fintype.card K = p ^ f := by
      rw [← Nat.card_eq_fintype_card, hK.card]
      rfl
    have hcharP : CharP K p := charP_of_card_eq_prime_pow hKcard
    have hring : ringChar K = p := ringChar.eq K p
    let eSL : Matrix.SpecialLinearGroup (Fin 3) K ≃* ↥(Sec4.slPi true 3 (p ^ f) K) :=
      (MonoidHom.ofInjective
        (Matrix.SpecialLinearGroup.toGL_injective (n := Fin 3) (R := K))).trans
        (MulEquiv.subgroupCongr (CFSG.Open.StatedAPI.statedSL_eq_range_toGL 3 K).symm)
    have hcat := catalogueOver_of_surjective_sl (E := K) (m := 3) (by norm_num)
      (fun h => absurd h (by norm_num)) (g₀.comp eSL.toMonoidHom) (hg₀.comp eSL.surjective) (by
        rw [← MonoidHom.comap_ker]
        exact (Subgroup.comap_mono hg₀k).trans
          (Subgroup.comap_center_le_center (f := eSL.toMonoidHom) eSL.injective))
    rwa [hring, hKcard] at hcat

theorem compsWith_catalogueOver_projImage_glPi {π : Bool} {p f : ℕ} {K : Type} [Field K]
    [Finite K] (hK : Sec4.PiField π p f K) (hπ2 : π = true → 2 < p ^ f) :
    CompsWith (CatalogueOver p (p ^ f)) ↥(projImage (Sec4.glPi π 3 (p ^ f) K)) := by
  classical
  haveI := hK.finite
  haveI : Fintype K := Fintype.ofFinite K
  have hp := hK.prime
  haveI : Fact p.Prime := ⟨hp⟩
  intro J hJ
  by_cases hq2 : 2 < p ^ f
  · haveI : Finite (Matrix.ProjGenLinGroup (Fin 3) K) :=
      Finite.of_surjective (Matrix.ProjGenLinGroup.mk : GL (Fin 3) K →* _)
        (QuotientGroup.mk'_surjective _)
    haveI : Finite ↥(projImage (Sec4.glPi π 3 (p ^ f) K)) := Subtype.finite
    have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
    have hR := Item8KFacts2Proof.perfectResidual_projImage_glPi_eq hK hq2
    have hSP : projImage (Sec4.slPi π 3 (p ^ f) K) ≤ projImage (Sec4.glPi π 3 (p ^ f) K) :=
      Subgroup.map_mono (Sec4.slPi_le_glPi hπ)
    let eR : ↥(CFSG.perfectResidual ↥(projImage (Sec4.glPi π 3 (p ^ f) K))) ≃*
        ↥(projImage (Sec4.slPi π 3 (p ^ f) K)) :=
      (MulEquiv.subgroupCongr hR).trans (Subgroup.subgroupOfEquivOfLe hSP)
    have hperfS : Group.IsPerfect (projImage (Sec4.slPi π 3 (p ^ f) K)) :=
      Sec13.isPerfect_projImage_slPi hK hq2
    have hsS := Item8KFacts2Proof.isSimpleGroup_projImage_slPi hK hq2
    haveI := hsS
    have hqS : CFSG.IsQuasisimple ↥(projImage (Sec4.slPi π 3 (p ^ f) K)) :=
      (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup
        (Item8KFacts2Proof.exists_ne_comm_of_isPerfect hperfS)).1
    have hqR : CFSG.IsQuasisimple
        ↥(CFSG.perfectResidual ↥(projImage (Sec4.glPi π 3 (p ^ f) K))) :=
      CFSG.IsQuasisimple.of_mulEquiv eR hqS
    have hPJ : CatalogueOver p (p ^ f)
        ↥(CFSG.perfectResidual ↥(projImage (Sec4.glPi π 3 (p ^ f) K))) :=
      (catalogueOver_projImage_slPi hK hq2).of_mulEquiv eR.symm
    exact compsWith_of_perfectResidual hqR hPJ J hJ
  · have h2 : p ^ f = 2 := by
      have := hp.two_le
      have h3 : p ≤ p ^ f := Nat.le_self_pow (by have := hK.one_le; omega) p
      omega
    cases π
    · haveI := Sec13.isSolvable_projImage_glPi_two hK h2
      exfalso
      obtain ⟨hp', hs⟩ := hJ.2.2
      haveI := hs.toNontrivial
      haveI : Nontrivial ↥J := (QuotientGroup.mk'_surjective (Subgroup.center ↥J)).nontrivial
      exact absurd hp' (ne_of_lt (Group.IsSolvable.commutator_lt_top_of_nontrivial ↥J))
    · exact absurd (hπ2 rfl) hq2

@[expose] def TrialityOddA2CompsCatalogue (ℓ f : ℕ) [Fact ℓ.Prime] : Prop :=
  5 ≤ ℓ → 1 ≤ f → ∀ (K₃ : Type) [Field K₃] [Finite K₃],
    Nat.card K₃ = (ℓ ^ f) ^ 3 → ∀ (Fr : K₃ ≃+* K₃), (∀ c, Fr c = c ^ (ℓ ^ f)) →
    ∀ φ : MulAut ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom), φ ^ 3 = 1 →
      φ ∉ (MulAut.conj : ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom) →*
        MulAut ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom)).range →
      (¬ ∃ β : MulAut ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom),
        φ = β * fieldActor (t := TwistTag.D4) Fr Fr * β⁻¹ ∨
          φ = β * (fieldActor (t := TwistTag.D4) Fr Fr)⁻¹ * β⁻¹) →
      CompsWith (CatalogueOver ℓ (ℓ ^ f)) ↥(fixSubgroup φ)

theorem compsWith_catalogueOver_fixSubgroup_fieldActor {ℓ f : ℕ} [Fact ℓ.Prime]
    (hℓ3 : ℓ ≠ 3) (hf : 1 ≤ f) (hℓ2 : ℓ = 2 ∨ 5 ≤ ℓ) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) :
    CompsWith (CatalogueOver ℓ (ℓ ^ f)) ↥(fixSubgroup (fieldActor (t := TwistTag.D4) σ σ)) := by
  obtain ⟨e⟩ := nonempty_fixSubgroup_fieldActor_equiv_G2 hℓ3 hf hℓ2 hK σ hσ
  have hq : 2 ≤ ℓ ^ f := by
    have h2 : ℓ.Prime := Fact.out
    have h3 : ℓ ≤ ℓ ^ f := Nat.le_self_pow (by omega) ℓ
    have h4 := h2.two_le
    omega
  have hF : Nat.card (fixSubfield σ) = ℓ ^ f :=
    CFSG.GH74.GLS.Stage4.Hex.card_fixedField_of_cube σ.toRingHom hq hK hσ
  haveI : Finite (fixSubfield σ) := Subtype.finite
  exact CompsWith.of_mulEquiv (isComponentProperty_catalogueOver ℓ (ℓ ^ f)) e
    (compsWith_catalogueOver_adjointGroup_G2 hf hF)

theorem compsWith_catalogueOver_triality_outer {ℓ f : ℕ} [Fact ℓ.Prime]
    (hodd : TrialityOddA2CompsCatalogue ℓ f) (hℓ3 : ℓ ≠ 3) (hf : 1 ≤ f) {K₃ : Type} [Field K₃]
    [Finite K₃]
    (hK₃ : Nat.card K₃ = (ℓ ^ f) ^ 3) (Fr : K₃ ≃+* K₃) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f))
    (φ : MulAut ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom)) (hφ3 : φ ^ 3 = 1)
    (hφ : φ ∉ (MulAut.conj : ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom) →*
      MulAut ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom)).range) :
    CompsWith (CatalogueOver ℓ (ℓ ^ f)) ↥(fixSubgroup φ) := by
  have hℓ : ℓ.Prime := Fact.out
  have hℓ2 : ℓ = 2 ∨ 5 ≤ ℓ := by
    have h2 := hℓ.two_le
    by_cases h5 : 5 ≤ ℓ
    · exact Or.inr h5
    · left
      have h4 : ℓ ≠ 4 := fun h => by rw [h] at hℓ; exact absurd hℓ (by norm_num)
      omega
  have hG2 := compsWith_catalogueOver_fixSubgroup_fieldActor hℓ3 hf hℓ2 hK₃ Fr hFr
  by_cases hconj : ∃ β : MulAut ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom),
      φ = β * fieldActor (t := TwistTag.D4) Fr Fr * β⁻¹ ∨
        φ = β * (fieldActor (t := TwistTag.D4) Fr Fr)⁻¹ * β⁻¹
  · obtain ⟨β, hβ | hβ⟩ := hconj
    · rw [hβ]
      exact CompsWith.of_mulEquiv (isComponentProperty_catalogueOver ℓ (ℓ ^ f))
        (fixSubgroupConjEquiv β _).symm hG2
    · rw [hβ]
      exact CompsWith.of_mulEquiv (isComponentProperty_catalogueOver ℓ (ℓ ^ f))
        ((fixSubgroupConjEquiv β _).symm.trans
          (MulEquiv.subgroupCongr (fixSubgroup_inv_eq _))) hG2
  · rcases hℓ2 with rfl | h5
    · rcases Item8KFacts2Proof.isStdGraphFieldConj_or_nonempty_autFix_equiv hf hK₃ hFr hφ3 hφ with
        hstd | he₂
      · exact absurd hstd hconj
      · obtain ⟨e₂⟩ := he₂
        have hfixφ : fixSubgroup φ = Sec4.autFix φ := Subgroup.ext fun _ => Iff.rfl
        let ef : ↥(fixSubgroup φ) ≃* ↥(Sec4.autFix φ) := MulEquiv.subgroupCongr hfixφ
        rcases Nat.even_or_odd f with hfe | hfo
        · obtain ⟨F, _, _, hF, ⟨e₃⟩⟩ := kF82D4SecondCentY0Even_holds f hfe hf K₃ Fr hK₃ hFr
          have hPi : Sec4.PiField true 2 f F := ⟨Nat.prime_two, hf, hF⟩
          have hf2 : 2 ≤ f := by
            obtain ⟨k, hk⟩ := hfe
            omega
          have h2 : 2 < 2 ^ f :=
            lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) hf2)
          exact CompsWith.of_mulEquiv (isComponentProperty_catalogueOver 2 (2 ^ f))
            (ef.trans (e₂.trans e₃)) (compsWith_catalogueOver_projImage_glPi hPi (fun _ => h2))
        · obtain ⟨F, _, _, hF, ⟨e₃⟩⟩ := kF82D4SecondCentY0_holds f hfo K₃ Fr hK₃ hFr
          have hPi : Sec4.PiField false 2 f F := ⟨Nat.prime_two, hf, hF⟩
          exact CompsWith.of_mulEquiv (isComponentProperty_catalogueOver 2 (2 ^ f))
            (ef.trans (e₂.trans e₃)) (compsWith_catalogueOver_projImage_glPi hPi
              (fun h => absurd h (by decide)))
    · exact hodd h5 hf K₃ hK₃ Fr hFr φ hφ3 hφ hconj

theorem trialityOddA2CompsCatalogue_holds (ℓ f : ℕ) [Fact ℓ.Prime] :
    TrialityOddA2CompsCatalogue ℓ f := by
  intro h5 hf K₃ _ _ hK₃ Fr hFr φ hφ3 hφ hconj
  have hPsl : ∀ {E : Type} [Field E] [Finite E], Nat.card E = ℓ ^ f →
      ∀ {Q : Type} [Group Q] [Finite Q] (ρ : SL(3, E) →* Q),
        Function.Surjective ρ → ρ.ker ≤ Subgroup.center SL(3, E) →
        CatalogueOver ℓ (ℓ ^ f) Q := by
    intro E _ _ hE Q _ _ ρ hρ hk
    haveI : Fintype E := Fintype.ofFinite E
    have hEc : Fintype.card E = ℓ ^ f := by rw [← Nat.card_eq_fintype_card]; exact hE
    haveI : CharP E ℓ := charP_of_card_eq_prime_pow hEc
    have hring : ringChar E = ℓ := ringChar.eq E ℓ
    have hcat := catalogueOver_of_surjective_sl (E := E) (m := 3) (by norm_num)
      (fun h => absurd h (by norm_num)) ρ hρ hk
    rwa [hring, hEc] at hcat
  have hPsu : ∀ {E : Type} [Field E] [Finite E], Nat.card E = (ℓ ^ f) ^ 2 →
      ∀ {Q : Type} [Group Q] [Finite Q] (g : ↥(StatedSU 3 (ℓ ^ f) E) →* Q),
        Function.Surjective g → g.ker ≤ Subgroup.center ↥(StatedSU 3 (ℓ ^ f) E) →
        CatalogueOver ℓ (ℓ ^ f) Q := by
    intro E _ _ hE Q _ _ g hg hk
    haveI : Fintype E := Fintype.ofFinite E
    have hEc : Fintype.card E = (ℓ ^ f) ^ 2 := by
      rw [← Nat.card_eq_fintype_card]; exact hE
    haveI : CharP E ℓ := charP_of_card_eq_prime_pow (f := 2 * f)
      (by rw [hEc, ← pow_mul, mul_comm])
    have hring : ringChar E = ℓ := ringChar.eq E ℓ
    have hmq : ((3 : ℕ), ℓ ^ f) ≠ ((3 : ℕ), 2) := by
      intro h
      have hle : ℓ ^ f = 2 := (Prod.mk.inj h).2
      have h55 : 5 ≤ ℓ ^ f := h5.trans (Nat.le_self_pow (by omega) ℓ)
      omega
    have hcat := catalogueOver_of_surjective_su (K := E) (m := 3) (q := ℓ ^ f) hEc
      (by norm_num) hmq g hg hk
    rwa [hring] at hcat
  have hPG2 : ∀ {E : Type} [Field E] [Finite E], Nat.card E = ℓ ^ f →
      CompsWith (CatalogueOver ℓ (ℓ ^ f)) ↥(adjointGroup Tag.G2 E) :=
    fun hE => compsWith_catalogueOver_adjointGroup_G2 hf hE
  exact trialityOddA2CompsWith_of_toral (isComponentProperty_catalogueOver ℓ (ℓ ^ f))
    (a2PlusCompsWith_holds (isComponentProperty_catalogueOver ℓ (ℓ ^ f)) hPsl)
    (a2MinusCompsWith_holds (isComponentProperty_catalogueOver ℓ (ℓ ^ f)) hPsu) hPG2
    h5 hf K₃ hK₃ Fr hFr φ hφ3 hφ hconj

theorem catalogueOver_component_d4_graph {ℓ f : ℕ} [Fact ℓ.Prime]
    (hℓ3 : ℓ ≠ 3) (hf : 1 ≤ f) {F : Type} [Field F]
    [Finite F]
    (hF : Nat.card F = ℓ ^ f) (g : adjointGroup Tag.D4 F) (a : Fin Tag.D4.rank → Fˣ)
    {ε : ℕ} (hε : ε = 1 ∨ ε = 2)
    (hα : (MulAut.conj g * (exactNormalAut Tag.D4 F a 1 0 * d4Graph F ε)) ^ 3 = 1)
    (J : Subgroup (adjointGroup Tag.D4 F))
    (hJ : IsComponentOf J
      (fixSubgroup (MulAut.conj g * (exactNormalAut Tag.D4 F a 1 0 * d4Graph F ε)))) :
    CatalogueOver ℓ (ℓ ^ f) ↥J := by
  classical
  obtain ⟨K₃, _, _, Fr, hK₃, hFr, φ, hφ3, hφout, ⟨e⟩⟩ :=
    D4Dual.exists_dual_fixEquiv hf F hF
      (MulAut.conj g * (exactNormalAut Tag.D4 F a 1 0 * d4Graph F ε)) hα g a hε rfl
  have hC := compsWith_catalogueOver_triality_outer (trialityOddA2CompsCatalogue_holds ℓ f)
    hℓ3 hf hK₃ Fr hFr φ hφ3 hφout
  have hα' : CompsWith (CatalogueOver ℓ (ℓ ^ f))
      ↥(fixSubgroup (MulAut.conj g * (exactNormalAut Tag.D4 F a 1 0 * d4Graph F ε))) :=
    CompsWith.of_mulEquiv (isComponentProperty_catalogueOver ℓ (ℓ ^ f)) e hC
  have hJ' : IsComponentOf
      (J.subgroupOf (fixSubgroup (MulAut.conj g * (exactNormalAut Tag.D4 F a 1 0 * d4Graph F ε))))
      ⊤ := (LargeExtraspecial.S5.isComponentOf_iff_subgroupOf hJ.1).1 hJ
  exact (hα' _ hJ').of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJ.1)

theorem compIdxAt_D4 (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.D 4 q).Valid)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpc : p ≠ (TauCeti.LieTypeIndex.D 4 q).characteristic) :
    CompIdxAt p (.D 4 q) (TauCeti.CFSGIndex.lie ⟨.D 4 q, hv⟩).Group := by
  classical
  let F := ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D 4 q, hv⟩)
  haveI : Finite F := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hFcard : Nat.card F = q.p ^ q.exponent := by
    change Nat.card ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D 4 q, hv⟩) =
      q.p ^ q.exponent
    rw [TauCeti.ValidLieTypeIndex.card_fixedField,
      TauCeti.ValidLieTypeIndex.fieldOrder_eq_characteristic_pow,
      TauCeti.ValidLieTypeIndex.characteristic, TauCeti.ValidLieTypeIndex.fieldExponent,
      TauCeti.LieTypeIndex.characteristic_D, TauCeti.LieTypeIndex.fieldExponent_D]
  have hcharD : (TauCeti.LieTypeIndex.D 4 q).characteristic = q.p :=
    TauCeti.LieTypeIndex.characteristic_D 4 q
  have hfieldD : fieldSize (.D 4 q) = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
  have hpℓ : p ≠ q.p := fun h => hpc (by rw [hcharD, h])
  have hSC : CFSG.Open.StatedClassicalModel (adjointGroup Tag.D4 F) .POmegaPlus 4 q.p q.exponent :=
    ⟨⟨q.prime_p, q.exponent_pos, by norm_num⟩, F, inferInstance, inferInstance, hFcard,
      ⟨(CFSG.HardMathSupport.Lang.Coordinator.D4Bridge.nonempty_statedProj_equiv_adjointGroup
        F).some.symm⟩⟩
  have hineq : ∀ h : adjointGroup Tag.D4 F, h ^ p = 1 →
      ∀ J : Subgroup (adjointGroup Tag.D4 F),
        IsComponentOf J (fixSubgroup (MulAut.conj h)) →
        ∃ i : TauCeti.CFSGIndex,
          Nonempty (↥J ⧸ Subgroup.center ↥J ≃* i.Group) ∧ compRelC (.D 4 q) i := by
    intro h hh J hJ
    obtain ⟨j, hj, i, ⟨eJ⟩, hidx⟩ :=
      catalogueOver_component_conj_omega (t := .POmegaPlus) (Or.inr (Or.inl rfl)) hSC hp hp2
        hpℓ h hh J hJ
    exact ⟨i, ⟨eJ⟩, compRelC_of_idxOver (d := .D 4 q) (i := i) (j := j) hj (by
      simpa [hcharD, hfieldD] using hidx)⟩
  have hcoord : CompIdxAt p (.D 4 q) (adjointGroup Tag.D4 F) := by
    intro β hβmem hβp hβ1 J hJ
    have hpow : ∀ h : adjointGroup Tag.D4 F, (MulAut.conj h) ^ p = 1 → h ^ p = 1 :=
      fun h hh => CFSG.mulAutConj_injective_of_center_eq_bot center_adjointGroup_eq_bot
        (by rw [map_pow, hh, map_one])
    by_cases hp3 : p = 3
    · subst hp3
      rcases CFSG.ComponentClassification.OuterAutomorphisms.innAutDerived_D4_three_cases
        hβmem hβp with ⟨h, hβeq⟩ | ⟨g, a, ε, hε, hβeq⟩
      · rw [hβeq] at hβp hJ
        exact hineq h (hpow h hβp) J hJ
      · rw [hβeq] at hβp hJ
        have hcat : CatalogueOver q.p (q.p ^ q.exponent) ↥J :=
          catalogueOver_component_d4_graph (ℓ := q.p) (f := q.exponent)
            (fun h => hpℓ h.symm) q.exponent_pos hFcard g a hε hβp J hJ
        obtain ⟨i, ⟨eJ⟩, hidx⟩ := hcat
        exact ⟨i, ⟨eJ⟩, compRelC_of_idxOver (d := .D 4 q) (i := i) (j := 1) le_rfl (by
          simpa [hcharD, hfieldD] using hidx)⟩
    · obtain ⟨h, hβeq⟩ :=
        CFSG.ComponentClassification.OuterAutomorphisms.exists_conj_eq_of_mem_innAutDerived_D4
          hp hp2 hp3 hβmem hβp
      rw [hβeq] at hβp hJ
      exact hineq h (hpow h hβp) J hJ
  have e₁ := CFSG.RankThree.PartTwo.Census.Carrier.SpinD.typeDGroupEquivStatedProj_of_valid 4 q hv
  have e₂ :=
    (CFSG.HardMathSupport.Lang.Coordinator.D4Bridge.nonempty_statedProj_equiv_adjointGroup F).some
  exact compIdxAt_of_mulEquiv (e₁.trans e₂).symm hcoord

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie
