module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2015NLTD4NC
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FRResTD4
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2015NLRed
public import CFSG.RankThree.PartTwo.Sec4.Item417Res7ProofD4Odd

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.GLTheoremA.I2015

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.Assembly CFSG.StandardType CFSG.LocalAnalysis.GLTheoremA.MI
open CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 (PiField glPi slPi ModThree)
open CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley (graphFixedRootGroup fieldActor)
open scoped commutatorElement

@[expose] def TD4NCore (N : ℕ) (D : Type) [Group D] : Prop :=
  ∃ E : Subgroup D, IsSimpleGroup ↥E ∧ (∃ x y : ↥E, x * y ≠ y * x) ∧
    (∀ T : Subgroup D, ⁅T, T⁆ = T → T ≤ E) ∧ TD4NoSL2 N ↥E

theorem td4n_core_of_equiv {S : Type} [Group S] {C : Subgroup S} {D : Type} [Group D] {N : ℕ}
    (e : ↥C ≃* D) (h : TD4NCore N D) :
    ∃ E : Subgroup S, E ≤ C ∧ IsSimpleGroup ↥E ∧ (∃ x y : ↥E, x * y ≠ y * x) ∧
      (∀ T : Subgroup S, T ≤ C → ⁅T, T⁆ = T → T ≤ E) ∧ TD4NoSL2 N ↥E := by
  obtain ⟨E', hs, hna, hperf, hN⟩ := h
  let e1 : ↥E' ≃* ↥(E'.map e.symm.toMonoidHom) :=
    E'.equivMapOfInjective e.symm.toMonoidHom e.symm.injective
  let e2 : ↥(E'.map e.symm.toMonoidHom) ≃* ↥((E'.map e.symm.toMonoidHom).map C.subtype) :=
    (E'.map e.symm.toMonoidHom).equivMapOfInjective C.subtype C.subtype_injective
  let eE : ↥E' ≃* ↥((E'.map e.symm.toMonoidHom).map C.subtype) := e1.trans e2
  refine ⟨(E'.map e.symm.toMonoidHom).map C.subtype, Subgroup.map_subtype_le _,
    eE.isSimpleGroup_congr.1 hs, ?_, ?_, TD4NoSL2.of_mulEquiv eE.symm hN⟩
  · obtain ⟨x, y, hxy⟩ := hna
    exact ⟨eE x, eE y, fun hh => hxy (eE.injective (by rw [map_mul, map_mul]; exact hh))⟩
  · intro T hTC hTp
    have hTT : (T.subgroupOf C).map C.subtype = T := Subgroup.map_subgroupOf_eq_of_le hTC
    have hT'p : ⁅T.subgroupOf C, T.subgroupOf C⁆ = T.subgroupOf C := by
      apply Subgroup.map_injective C.subtype_injective
      rw [Subgroup.map_commutator, hTT, hTp]
    have hTm : ⁅(T.subgroupOf C).map e.toMonoidHom, (T.subgroupOf C).map e.toMonoidHom⁆ =
        (T.subgroupOf C).map e.toMonoidHom := by
      rw [← Subgroup.map_commutator, hT'p]
    have h1 := hperf _ hTm
    rw [← hTT]
    refine Subgroup.map_mono (fun x hx => ?_)
    exact ⟨e x, h1 ⟨x, hx, rfl⟩, by simp⟩

section ProjImage

variable {π : Bool} {f : ℕ} {F : Type} [Field F]

theorem td4n_core_projImage (hK : PiField π 2 f F)
    (hmod : ModThree π (2 ^ f)) (hq2 : 2 < 2 ^ f) (hf : cond π 2 3 ≤ f) (N : ℕ) :
    TD4NCore N ↥(CFSG.PGLModel.projImage (glPi π 3 (2 ^ f) F)) := by
  haveI := hK.finite
  haveI : Finite (Matrix.ProjGenLinGroup (Fin 3) F) :=
    Finite.of_surjective (Matrix.ProjGenLinGroup.mk : GL (Fin 3) F →* _)
      (QuotientGroup.mk'_surjective _)
  have hπ : π = false → CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 f F :=
    fun h => by subst h; exact hK.unitary
  have hSP : CFSG.PGLModel.projImage (slPi π 3 (2 ^ f) F) ≤
      CFSG.PGLModel.projImage (glPi π 3 (2 ^ f) F) := Subgroup.map_mono (Sec4.slPi_le_glPi hπ)
  haveI : Finite ↥(CFSG.PGLModel.projImage (glPi π 3 (2 ^ f) F)) := Subtype.finite
  have hcomm := Sec13.commutator_projImage_glPi hK hq2
  set E := (CFSG.PGLModel.projImage (slPi π 3 (2 ^ f) F)).subgroupOf
      (CFSG.PGLModel.projImage (glPi π 3 (2 ^ f) F)) with hEdef
  let eE : ↥E ≃* ↥(CFSG.PGLModel.projImage (slPi π 3 (2 ^ f) F)) :=
    Subgroup.subgroupOfEquivOfLe hSP
  have hs : IsSimpleGroup ↥(CFSG.PGLModel.projImage (slPi π 3 (2 ^ f) F)) :=
    CFSG.RankThree.PartTwo.Sec8.Item8KFacts2Proof.isSimpleGroup_projImage_slPi hK hq2
  have hperf : Group.IsPerfect ↥(CFSG.PGLModel.projImage (slPi π 3 (2 ^ f) F)) :=
    Sec13.isPerfect_projImage_slPi hK hq2
  haveI : Nontrivial ↥(CFSG.PGLModel.projImage (slPi π 3 (2 ^ f) F)) := hs.toNontrivial
  have hsE : IsSimpleGroup ↥E := eE.isSimpleGroup_congr.2 hs
  have hnaE : ∃ x y : ↥E, x * y ≠ y * x := by
    obtain ⟨a, b, hab⟩ :=
      CFSG.RankThree.PartTwo.Sec8.Item8KFacts2Proof.exists_ne_comm_of_isPerfect hperf
    exact ⟨eE.symm a, eE.symm b,
      fun hh => hab (eE.symm.injective (by rw [map_mul, map_mul]; exact hh))⟩
  have hf2 : 2 ≤ f := by
    cases π <;> simp at hf <;> omega
  haveI : Finite ↥E := Subtype.finite
  have hcardE : Nat.card ↥E * 3 =
      (2 ^ f) ^ 3 * ((2 ^ f) ^ 2 - 1) * cond π ((2 ^ f) ^ 3 - 1) ((2 ^ f) ^ 3 + 1) := by
    rw [Nat.card_congr eE.toEquiv]
    exact Sec13.card_projImage_slPi_mul_three hK hmod
  refine ⟨E, hsE, hnaE, ?_, td4n_noSL2_of_psl3_card hsE hnaE hf2 (c := cond π ((2 ^ f) ^ 3 - 1)
    ((2 ^ f) ^ 3 + 1)) (by cases π <;> simp) hcardE N⟩
  intro T hT
  rw [← hT, ← hcomm, commutator_def]
  exact Subgroup.commutator_mono le_top le_top

end ProjImage

section G2


variable {k : Type} [Field k] [Finite k] {f : ℕ}

theorem td4n_core_adjointG2 (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f) :
    TD4NCore ((2 ^ f) ^ 3) ↥(adjointGroup .G2 k) := by
  have hle : ∀ (E : Type) [Group E] [Finite E], (2 ^ f) ^ 9 ≤ Nat.card E →
      TD4NoSL2 ((2 ^ f) ^ 3) E := fun E _ _ h =>
    td4n_noSL2_of_card_ge (by rw [← pow_mul]; simpa using h)
  rcases Nat.eq_or_lt_of_le hf with h1 | h2
  · subst h1
    obtain ⟨E, hs, hna, hperf, hidx, -⟩ := FR.Res.datumCore_adjointG2_two (by simpa using hk)
    have hD := CFSG.ComponentClassification.ExcSelector.card_adjointGroup_G2_two
      (k := k) (by simpa using hk)
    haveI : Finite ↥E := Subtype.finite
    refine ⟨E, hs, hna, hperf, hle _ ?_⟩
    rcases hidx with h | h <;> omega
  · have h4 : 4 ≤ 2 ^ f := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h2
    have hq := CFSG.LieType.Steinberg.Adjoint.isQuasisimple_g2_of_three_le_card (K := k)
      (by omega)
    obtain ⟨hs, a, b, hab⟩ :=
      CFSG.HardMathSupport.Dickson.Sec6.I923.TriD4Aux.isSimple_of_isQuasisimple_center_bot hq
        CFSG.LieType.Chevalley.center_adjointGroup_eq_bot
    refine ⟨⊤, (Subgroup.topEquiv).isSimpleGroup_congr.2 hs, ⟨⟨a, trivial⟩, ⟨b, trivial⟩,
      fun hh => hab (congrArg Subtype.val hh)⟩, fun T _ => le_top, hle _ ?_⟩
    rw [Subgroup.card_top, CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2, hk]
    unfold CFSG.Open.ordG2
    set q := 2 ^ f with hq'
    have h5 : q ^ 5 ≤ q ^ 6 - 1 := by
      have : q ^ 6 = q * q ^ 5 := by ring
      have h5pos : 1 ≤ q ^ 5 := Nat.one_le_pow _ _ (by omega)
      have : 4 * q ^ 5 ≤ q * q ^ 5 := Nat.mul_le_mul_right _ h4
      omega
    have h1' : q ≤ q ^ 2 - 1 := by
      have : q ^ 2 = q * q := by ring
      have : 4 * q ≤ q * q := Nat.mul_le_mul_right _ h4
      omega
    calc q ^ 9 ≤ q ^ 12 := Nat.pow_le_pow_right (by omega) (by norm_num)
      _ = q ^ 6 * q ^ 5 * q := by ring
      _ ≤ q ^ 6 * (q ^ 6 - 1) * (q ^ 2 - 1) :=
        Nat.mul_le_mul (Nat.mul_le_mul le_rfl h5) h1'

end G2

section TD4


theorem td4n_core {S : Type} [Group S] [Finite S] (hchev : IsChevSimple 2 S) (hTD4 : IsTD4Simple S)
    {β : MulAut S} (hβ3 : β ^ 3 = 1) (hβout : β ∉ (MulAut.conj : S →* MulAut S).range)
    (hT : ∃ T : Subgroup S, T ≤ FP.fixSub β ∧ ⁅T, T⁆ = T ∧ T ≠ ⊥) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (σ : K ≃+* K) (_ : σ ^ 3 = 1)
      (_ : S ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom) (E : Subgroup S),
      E ≤ FP.fixSub β ∧ IsSimpleGroup ↥E ∧ (∃ x y : ↥E, x * y ≠ y * x) ∧
        (∀ T : Subgroup S, T ≤ FP.fixSub β → ⁅T, T⁆ = T → T ≤ E) ∧ TD4NoSL2 (Nat.card K) ↥E := by
  obtain ⟨T, hTC, hTp, hTne⟩ := hT
  have hp3 : Nat.Prime 3 := Nat.prime_three
  obtain ⟨q, hv, ⟨eS⟩⟩ := FR.Res.td4_index' hTD4
  have hq2 : q.p = 2 := by
    by_contra hne
    exact FR.Res.td4_odd_false' hv hne eS hchev
  obtain ⟨K, _, _, σ, hK, hσ, -, ⟨eC⟩⟩ :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_catEquiv_trialityD4 q hv
  have hf : 1 ≤ q.exponent := q.exponent_pos
  have hK' : Nat.card K = (2 ^ q.exponent) ^ 3 := by rw [hK, hq2]
  have hσ' : ∀ c, σ c = c ^ 2 ^ q.exponent := fun c => by rw [hσ c, hq2]
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hcharK : CharP K 2 := by
    have := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (p := 2) (f := q.exponent * 3)
      (by rw [Fintype.card_eq_nat_card, hK', ← pow_mul])
  have hσ3 : σ ^ 3 = 1 := by
    apply RingEquiv.ext
    intro c
    have := Fintype.ofFinite K
    change σ (σ (σ c)) = c
    rw [hσ', hσ', hσ', ← pow_mul, ← pow_mul]
    have h1 : 2 ^ q.exponent * (2 ^ q.exponent * 2 ^ q.exponent) = Fintype.card K := by
      rw [Fintype.card_eq_nat_card, hK']
      ring
    rw [h1, FiniteField.pow_card]
  let e' : S ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom := eS.trans eC
  have hφ3 : MulAut.congr e' β ^ 3 = 1 := by rw [← map_pow, hβ3, map_one]
  have hφout : ¬ CFSG.RankThree.PartTwo.KFacts.IsInnerAut (MulAut.congr e' β) :=
    fun h => hβout ((FQ.congr_mem_range_conj e' _).1 h)
  have eFix : ↥(FP.fixSub β) ≃* ↥(Sec4.autFix (MulAut.congr e' β)) :=
    (FR.fixSubEquivCongr e' β).trans (MulEquiv.subgroupCongr (FR.Res.fixSub_eq_autFix _))
  suffices key : ∃ (Y : Type) (_ : Group Y), Nonempty (↥(FP.fixSub β) ≃* Y) ∧
      TD4NCore (Nat.card K) Y by
    obtain ⟨Y, _, ⟨e⟩, hc⟩ := key
    obtain ⟨E, hEC, hE, hna, hperf, hN⟩ := td4n_core_of_equiv e hc
    exact ⟨K, inferInstance, inferInstance, hcharK, σ, hσ3, e', E, hEC, hE, hna, hperf, hN⟩
  set φ := MulAut.congr e' β with hφ
  rcases CFSG.RankThree.PartTwo.Sec8.Item8KFacts2Proof.isStdGraphFieldConj_or_nonempty_autFix_equiv
      hf hK' hσ' hφ3 hφout with ⟨β', hβ' | hβ'⟩ | ⟨e2⟩
  ·
    have eA : ↥(Sec4.autFix φ) ≃* ↥(Sec4.autFix (fieldActor (t := TwistTag.D4) σ σ)) := by
      rw [hβ', ← CFSG.RankThree.PartTwo.Sec8.LangTwistedProof.mulAut_congr_eq]
      exact Sec4.autFixCongrEquiv β' _
    obtain ⟨eG⟩ := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.nonempty_fixSubgroup_fieldActor_equiv_G2
      (ℓ := 2) (by norm_num) hf (Or.inl rfl) hK' σ hσ'
    have hkc : Nat.card (CFSG.LieType.Chevalley.fixSubfield σ) = 2 ^ q.exponent :=
      CFSG.RankThree.PartOne.KGD.card_fixSubfield_cube Nat.prime_two hf hK' σ hσ'
    haveI : Finite (CFSG.LieType.Chevalley.fixSubfield σ) := Subtype.finite
    refine ⟨_, inferInstance, ⟨eFix.trans (eA.trans ((MulEquiv.subgroupCongr rfl).trans eG))⟩, ?_⟩
    rw [hK']
    exact td4n_core_adjointG2 hf hkc
  ·
    have eA : ↥(Sec4.autFix φ) ≃* ↥(Sec4.autFix (fieldActor (t := TwistTag.D4) σ σ)) := by
      rw [hβ', ← CFSG.RankThree.PartTwo.Sec8.LangTwistedProof.mulAut_congr_eq]
      exact (Sec4.autFixCongrEquiv β' _).trans (MulEquiv.subgroupCongr (FR.Res.autFix_inv'' _))
    obtain ⟨eG⟩ := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.nonempty_fixSubgroup_fieldActor_equiv_G2
      (ℓ := 2) (by norm_num) hf (Or.inl rfl) hK' σ hσ'
    have hkc : Nat.card (CFSG.LieType.Chevalley.fixSubfield σ) = 2 ^ q.exponent :=
      CFSG.RankThree.PartOne.KGD.card_fixSubfield_cube Nat.prime_two hf hK' σ hσ'
    haveI : Finite (CFSG.LieType.Chevalley.fixSubfield σ) := Subtype.finite
    refine ⟨_, inferInstance, ⟨eFix.trans (eA.trans ((MulEquiv.subgroupCongr rfl).trans eG))⟩, ?_⟩
    rw [hK']
    exact td4n_core_adjointG2 hf hkc
  ·
    obtain ⟨e2⟩ := e2
    rcases Nat.even_or_odd q.exponent with hfe | hfo
    · obtain ⟨F, _, _, hF, ⟨e3⟩⟩ :=
        CFSG.RankThree.PartTwo.Sec8.kF82D4SecondCentY0Even_holds q.exponent hfe hf K σ hK' hσ'
      have hPi : PiField true 2 q.exponent F := ⟨Nat.prime_two, hf, hF⟩
      have hf2 : 2 ≤ q.exponent := by
        obtain ⟨k, hk⟩ := hfe
        omega
      have hq4 : 2 < 2 ^ q.exponent :=
        lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) hf2)
      exact ⟨_, inferInstance, ⟨eFix.trans (e2.trans e3)⟩,
        td4n_core_projImage hPi (FR.Res.modThree_two_pow (π := true) hfe) hq4 (by simpa using hf2) _⟩
    · obtain ⟨F, _, _, hF, ⟨e3⟩⟩ :=
        CFSG.RankThree.PartTwo.Sec8.kF82D4SecondCentY0_holds q.exponent hfo K σ hK' hσ'
      have hPi : PiField false 2 q.exponent F := ⟨Nat.prime_two, hf, hF⟩
      by_cases h1 : q.exponent = 1
      · exfalso
        have hsol : Group.IsSolvable
            ↥(CFSG.PGLModel.projImage (glPi false 3 (2 ^ q.exponent) F)) :=
          Sec13.isSolvable_projImage_glPi_two hPi (by simp [h1])
        let eT := eFix.trans (e2.trans e3)
        haveI : Group.IsSolvable ↥(FP.fixSub β) :=
          Group.isSolvable_of_isSolvable_injective (f := eT.toMonoidHom) eT.injective
        exact FR.false_of_perfect_solvable hTC hTp hTne inferInstance
      · have hf3 : 3 ≤ q.exponent := by
          obtain ⟨k, hk⟩ := hfo
          omega
        have hq4 : 2 < 2 ^ q.exponent :=
          lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) hf3)
        exact ⟨_, inferInstance, ⟨eFix.trans (e2.trans e3)⟩,
          td4n_core_projImage hPi (FR.Res.modThree_two_pow (π := false) hfo) hq4
            (by simpa using hf3) _⟩

end TD4

end CFSG.LocalAnalysis.GLTheoremA.I2015

end
