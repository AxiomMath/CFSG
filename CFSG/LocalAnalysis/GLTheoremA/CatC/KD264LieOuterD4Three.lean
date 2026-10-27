module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOuter
public import CFSG.HardMathSupport.Lang.D4Three.PowNormalForm
public import CFSG.GroupTheory.MemOfSqMemOfPowThree
public import CFSG.GroupTheory.PLayer.Conj
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4FieldInner
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27D4AmbientForm
public import CFSG.RankThree.Chevalley.SteinbergCBTrialityTransposition
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TriD4Outer
public import CFSG.HardMathSupport.Lang.Coordinator.D4Bridge.Bridge

public section

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ExcCopy
open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
open CFSG.HardMathSupport.Lang.D4Three CFSG.HardMathSupport.Lang.E6Descent
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.StandardType.RecipeExcLang CFSG.RankThree.Chevalley
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open scoped commutatorElement

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

section CertSmall


section Graph

variable {K : Type} [Field K]

private noncomputable abbrev d4TrialityGL (K : Type) [Field K] : ModGL Tag.D4 K :=
  (trialityTransposition K : ModGL Tag.D4 K)

private noncomputable abbrev d4TrialityAutGL (K : Type) [Field K] :
    MulAut (ModGL Tag.D4 K) :=
  (trialityTranspositionAut K : MulAut (ModGL Tag.D4 K))

private theorem d4TrialityGL_mul_self : d4TrialityGL K * d4TrialityGL K = 1 := by
  show (trialityTransposition K : ModGL Tag.D4 K) * (trialityTransposition K : ModGL Tag.D4 K) = 1
  exact trialityTransposition_mul_self (K := K)

private theorem d4TrialityGL_inv : (d4TrialityGL K)⁻¹ = d4TrialityGL K :=
  inv_eq_of_mul_eq_one_right (d4TrialityGL_mul_self (K := K))

private theorem d4TrialityGL_conj_d4P :
    d4TrialityGL K * d4P K * (d4TrialityGL K)⁻¹ = (d4P K)⁻¹ := by
  show d4TrialityAutGL K (d4P K) = (d4P K)⁻¹
  exact trialityTranspositionAut_diagramMap (K := K)

private theorem map_d4TrialityAutGL_adjointGroup :
    (adjointGroup Tag.D4 K).map (d4TrialityAutGL K).toMonoidHom = adjointGroup Tag.D4 K := by
  show (adjointGroup TwistTag.D4.tag K).map
      (MulEquiv.toMonoidHom (trialityTranspositionAut K)) = adjointGroup TwistTag.D4.tag K
  exact map_trialityTranspositionAut_adjointGroup (K := K)

private noncomputable def d4TrialityAut (K : Type) [Field K] :
    MulAut (adjointGroup Tag.D4 K) :=
  mulAutRestrict (adjointGroup Tag.D4 K) (d4TrialityAutGL K)
    (map_d4TrialityAutGL_adjointGroup (K := K))

private theorem coe_d4TrialityAut (x : adjointGroup Tag.D4 K) :
    ((d4TrialityAut K x : adjointGroup Tag.D4 K) : ModGL Tag.D4 K) =
      d4TrialityGL K * (x : ModGL Tag.D4 K) * (d4TrialityGL K)⁻¹ := by
  rw [d4TrialityAut, CFSG.LieType.Chevalley.coe_mulAutRestrict]
  show d4TrialityAutGL K (x : ModGL Tag.D4 K) = d4TrialityGL K * (x : ModGL Tag.D4 K) *
    (d4TrialityGL K)⁻¹
  rfl

private theorem d4TrialityAut_mul_self : d4TrialityAut K * d4TrialityAut K = 1 := by
  refine MulEquiv.ext fun x => Subtype.ext ?_
  rw [MulAut.mul_apply, MulAut.one_apply, coe_d4TrialityAut, coe_d4TrialityAut,
    d4TrialityGL_inv]
  have hAA : d4TrialityGL K * d4TrialityGL K = 1 := d4TrialityGL_mul_self (K := K)
  calc d4TrialityGL K * (d4TrialityGL K * (x : ModGL Tag.D4 K) * d4TrialityGL K) *
        d4TrialityGL K =
      (d4TrialityGL K * d4TrialityGL K) * (x : ModGL Tag.D4 K) *
        (d4TrialityGL K * d4TrialityGL K) := by group
    _ = (x : ModGL Tag.D4 K) := by rw [hAA, one_mul, mul_one]

private theorem d4TrialityAut_inv : (d4TrialityAut K)⁻¹ = d4TrialityAut K :=
  inv_eq_of_mul_eq_one_right (d4TrialityAut_mul_self (K := K))

private theorem coe_inv_d4Graph_one (x : adjointGroup Tag.D4 K) :
    (((d4Graph K 1)⁻¹ x : adjointGroup Tag.D4 K) : ModGL Tag.D4 K) =
      (d4P K)⁻¹ * (x : ModGL Tag.D4 K) * d4P K := by
  have h : (d4P K) * (((d4Graph K 1)⁻¹ x : adjointGroup Tag.D4 K) : ModGL Tag.D4 K) *
      (d4P K)⁻¹ = (x : ModGL Tag.D4 K) := by
    have h1 : ((d4Graph K 1) ((d4Graph K 1)⁻¹ x) : ModGL Tag.D4 K) = (x : ModGL Tag.D4 K) := by
      rw [MulAut.apply_inv_self]
    rw [coe_d4Graph] at h1
    simpa using h1
  calc (((d4Graph K 1)⁻¹ x : adjointGroup Tag.D4 K) : ModGL Tag.D4 K) =
      (d4P K)⁻¹ * ((d4P K) * (((d4Graph K 1)⁻¹ x : adjointGroup Tag.D4 K) : ModGL Tag.D4 K) *
        (d4P K)⁻¹) * d4P K := by group
    _ = (d4P K)⁻¹ * (x : ModGL Tag.D4 K) * d4P K := by rw [h]

private theorem d4TrialityAut_conj_d4Graph_one :
    d4TrialityAut K * d4Graph K 1 * (d4TrialityAut K)⁻¹ = (d4Graph K 1)⁻¹ := by
  refine MulEquiv.ext fun x => Subtype.ext ?_
  rw [d4TrialityAut_inv, MulAut.mul_apply, MulAut.mul_apply, coe_d4TrialityAut,
    coe_d4Graph, coe_d4TrialityAut, coe_inv_d4Graph_one]
  have hAP : d4TrialityGL K * d4P K * (d4TrialityGL K)⁻¹ = (d4P K)⁻¹ :=
    d4TrialityGL_conj_d4P (K := K)
  have hAA : d4TrialityGL K * d4TrialityGL K = 1 := d4TrialityGL_mul_self (K := K)
  have hAinv : (d4TrialityGL K)⁻¹ = d4TrialityGL K := d4TrialityGL_inv (K := K)
  calc d4TrialityGL K *
        (d4P K * (d4TrialityGL K * (x : ModGL Tag.D4 K) * (d4TrialityGL K)⁻¹) *
          (d4P K)⁻¹) * (d4TrialityGL K)⁻¹
      = (d4TrialityGL K * d4P K * (d4TrialityGL K)⁻¹) *
          (d4TrialityGL K * (d4TrialityGL K * (x : ModGL Tag.D4 K) *
            (d4TrialityGL K)⁻¹) * (d4TrialityGL K)⁻¹) *
          (d4TrialityGL K * d4P K * (d4TrialityGL K)⁻¹)⁻¹ := by group
    _ = (d4P K)⁻¹ * (x : ModGL Tag.D4 K) * ((d4P K)⁻¹)⁻¹ := by
        rw [hAP]
        have hx : d4TrialityGL K * (d4TrialityGL K * (x : ModGL Tag.D4 K) *
            (d4TrialityGL K)⁻¹) * (d4TrialityGL K)⁻¹ = (x : ModGL Tag.D4 K) := by
          rw [hAinv]
          calc d4TrialityGL K * (d4TrialityGL K * (x : ModGL Tag.D4 K) * d4TrialityGL K) *
                d4TrialityGL K =
              (d4TrialityGL K * d4TrialityGL K) * (x : ModGL Tag.D4 K) *
                (d4TrialityGL K * d4TrialityGL K) := by group
            _ = (x : ModGL Tag.D4 K) := by rw [hAA, one_mul, mul_one]
        rw [hx]
    _ = (d4P K)⁻¹ * (x : ModGL Tag.D4 K) * d4P K := by rw [inv_inv]

private theorem d4Graph_one_pow_three : d4Graph K 1 ^ 3 = 1 := by
  have hP3 : d4P K ^ 3 = 1 := diagramMap_pow_order TwistTag.D4 K
  refine MulEquiv.ext fun x => Subtype.ext ?_
  rw [pow_three, MulAut.mul_apply, MulAut.mul_apply, MulAut.one_apply]
  simp only [coe_d4Graph, pow_one]
  calc d4P K * (d4P K * (d4P K * (x : ModGL Tag.D4 K) * (d4P K)⁻¹) * (d4P K)⁻¹) *
        (d4P K)⁻¹ = (d4P K * d4P K * d4P K) * (x : ModGL Tag.D4 K) *
          (d4P K * d4P K * d4P K)⁻¹ := by group
    _ = (x : ModGL Tag.D4 K) := by
        have hP3' : d4P K * d4P K * d4P K = 1 := by
          calc d4P K * d4P K * d4P K = d4P K ^ 3 := by rw [pow_three]; group
            _ = 1 := hP3
        rw [hP3', one_mul, inv_one, mul_one]

private theorem commutatorElement_d4TrialityAut_d4Graph_one :
    ⁅d4TrialityAut K, d4Graph K 1⁆ = d4Graph K 1 := by
  rw [commutatorElement_def, d4TrialityAut_conj_d4Graph_one]
  have h3 : d4Graph K 1 ^ 3 = 1 := d4Graph_one_pow_three (K := K)
  have hinv : (d4Graph K 1)⁻¹ = d4Graph K 1 ^ 2 := by
    rw [inv_eq_iff_mul_eq_one, ← pow_succ', show 1 + 2 = 3 by norm_num]
    exact h3
  rw [hinv, ← pow_add, show 2 + 2 = 3 + 1 by norm_num, pow_add, h3, one_mul, pow_one]

private theorem d4Graph_one_mem_commutator :
    d4Graph K 1 ∈ commutator (MulAut (adjointGroup Tag.D4 K)) := by
  rw [← commutatorElement_d4TrialityAut_d4Graph_one]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

private theorem d4Graph_two_eq_sq :
    d4Graph K 2 = d4Graph K 1 * d4Graph K 1 := by
  refine MulEquiv.ext fun x => Subtype.ext ?_
  rw [MulAut.mul_apply, coe_d4Graph, coe_d4Graph, coe_d4Graph]
  change d4P K ^ 2 * ((x : adjointGroup Tag.D4 K) : ModGL Tag.D4 K) * (d4P K ^ 2)⁻¹ =
    d4P K * (d4P K * ((x : adjointGroup Tag.D4 K) : ModGL Tag.D4 K) * (d4P K)⁻¹) * (d4P K)⁻¹
  rw [pow_two, mul_inv_rev]
  group

theorem mem_innAutDerived_of_graphType {K : Type} [Field K]
    (g : adjointGroup Tag.D4 K) (a : Fin Tag.D4.rank → Kˣ) {ε : ℕ}
    (hε : ε = 1 ∨ ε = 2)
    (hα : (MulAut.conj g * (exactNormalAut Tag.D4 K a 1 0 * d4Graph K ε)) ^ 3 = 1) :
    MulAut.conj g * (exactNormalAut Tag.D4 K a 1 0 * d4Graph K ε) ∈
      innAutDerived (adjointGroup Tag.D4 K) := by
  have hβ : (MulAut.conj g * exactNormalAut Tag.D4 K a 1 0) ^ 2 ∈
      innAutDerived (adjointGroup Tag.D4 K) := by
    obtain ⟨h, hh⟩ := exists_inner_sq_conj_mul_exactNormalAut_one g a
    rw [hh]
    exact inner_le_innAutDerived _ ⟨h, rfl⟩
  have hγ : d4Graph K ε ∈ commutator (MulAut (adjointGroup Tag.D4 K)) := by
    rcases hε with rfl | rfl
    · exact d4Graph_one_mem_commutator (K := K)
    · rw [d4Graph_two_eq_sq]
      exact Subgroup.pow_mem _ (d4Graph_one_mem_commutator (K := K)) 2
  exact mem_of_mul_mem_of_sq_mem_of_pow_three (mul_assoc _ _ _).symm
    (commutator_le_innAutDerived _ hγ) hβ hα

end Graph

end CertSmall

section CertField


private theorem glaPLayer_entrywiseAdjointAut_ne_bot {K : Type} [Field K] [Finite K]
    (σ : K ≃+* K) (hσ3 : σ ^ 3 = 1) :
    GLAPLayer 3 (fixSubgroup (entrywiseAdjointAut Tag.D4 σ)) ≠ ⊥ := by
  classical
  haveI : Finite (ModGL Tag.D4 K) := finite_modGL
  let k := fixSubfield σ
  haveI : Finite k := Subtype.finite
  have hperf : Group.IsPerfect (adjointGroup Tag.D4 k) :=
    ExcCopy.isPerfect_adjointGroup .D4 k (fun h => absurd h (by decide))
  obtain ⟨hs, hnc⟩ := ExcCopy.isSimpleGroup_adjointGroup_of_perfect .D4 k hperf
  obtain ⟨ι, hι, hJC, hnorm, -⟩ := ExcCopy.exists_fixed_structure .D4 σ
  let e : adjointGroup Tag.D4 k ≃* ι.range := MonoidHom.ofInjective hι
  have hq : CFSG.IsQuasisimple ↥(adjointGroup Tag.D4 k) :=
    LieSemisimple.isQuasisimple_of_isSimpleGroup hs hnc
  have hTq : CFSG.IsQuasisimple ι.range := CFSG.LocalCores.isQuasisimple_of_mulEquiv e hq
  have hTp : 3 ∣ Nat.card ι.range := by
    rw [← Nat.card_congr e.toEquiv]
    exact (by norm_num : (3 : ℕ) ∣ 27).trans (twentySeven_dvd_card_adjointGroup_D4 k)
  refine glaPLayer_fixSubgroup_ne_bot_of_quasisimple Nat.prime_three hJC ?_ hTq hTp
  intro f hf t ht
  have h := hnorm.conj_mem (⟨t, hJC ht⟩ : ↥(fixSubgroup (entrywiseAdjointAut Tag.D4 σ)))
    (Subgroup.mem_subgroupOf.2 ht) (⟨f, hf⟩ : ↥(fixSubgroup (entrywiseAdjointAut Tag.D4 σ)))
  simpa [Subgroup.mem_subgroupOf] using h

end CertField

section CertSmallTwo


private theorem isSimpleGroup_and_not_commutative_twistedOne {ℓ e : ℕ} (hℓ : ℓ.Prime) (he : 1 ≤ e)
    {K : Type} [Field K] (hK : Nat.card K = (ℓ ^ e) ^ 3) (σ : K ≃+* K) (r : ℕ)
    (hr : r = 1 ∨ r = 2) (hσ : ∀ c, σ c = c ^ ((ℓ ^ e) ^ r)) :
    IsSimpleGroup ↥(fixSubgroup (twistedEntrywiseAut TwistTag.D4 1 σ)) ∧
      ∃ x y : ↥(fixSubgroup (twistedEntrywiseAut TwistTag.D4 1 σ)), x * y ≠ y * x := by
  classical
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : CharP K ℓ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic (k := e * 3) hℓ
      (by omega) (by rw [hK, pow_mul])
  haveI : CharP (AlgebraicClosure K) ℓ :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective ℓ
  obtain ⟨-, -, hfixeq, hs, hnc⟩ :=
    triality_both_field_orientations_simple_full_ambient_fixed_group ℓ e hℓ he K hK
      (AlgebraicClosure K) r hr σ.toRingHom hσ
      (iterateFrobenius (AlgebraicClosure K) ℓ e) (fun c => by simp [iterateFrobenius_def])
  let eΓ : ↥(fixSubgroup (twistedEntrywiseAut TwistTag.D4 1 σ)) ≃*
      ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
    (fixedSubgroupTwistedEntrywiseAutOneEquiv (t := TwistTag.D4) σ).trans
      (MulEquiv.subgroupCongr hfixeq)
  haveI : IsSimpleGroup ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := hs
  refine ⟨eΓ.isSimpleGroup, ?_⟩
  obtain ⟨x, y, hxy⟩ := hnc
  exact ⟨eΓ.symm x, eΓ.symm y, fun h => hxy (by
    have h1 := congrArg eΓ h
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h1
    exact h1)⟩

private theorem isSimpleGroup_and_not_commutative_twisted {ℓ e : ℕ} (hℓ : ℓ.Prime) (he : 1 ≤ e)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ e) ^ 3) (T : K ≃+* K)
    (hT : ∀ c, T c = c ^ (ℓ ^ e)) (j : ℤ) (hj : j % 3 = 1 ∨ j % 3 = 2) :
    IsSimpleGroup ↥(fixSubgroup (twistedEntrywiseAut TwistTag.D4 j T)) ∧
      ∃ x y : ↥(fixSubgroup (twistedEntrywiseAut TwistTag.D4 j T)), x * y ≠ y * x := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have hq3 : ∀ c : K, c ^ ((ℓ ^ e) ^ 3) = c := fun c => by
    rw [← hK, Nat.card_eq_fintype_card, FiniteField.pow_card]
  have hT3 : T ^ 3 = 1 := by
    refine RingEquiv.ext fun c => ?_
    change T (T (T c)) = c
    rw [hT, hT, hT, ← pow_mul, ← pow_mul,
      show ℓ ^ e * (ℓ ^ e * ℓ ^ e) = (ℓ ^ e) ^ 3 by ring, hq3]
  have hinv : ∀ c, T⁻¹ c = c ^ ((ℓ ^ e) ^ 2) := by
    have h1 : T⁻¹ = T ^ 2 := inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact hT3)
    intro c
    rw [h1, pow_two]
    change T (T c) = _
    rw [hT, hT, ← pow_mul, sq]
  have hper : twistedEntrywiseAut TwistTag.D4 j T =
      twistedEntrywiseAut TwistTag.D4 (j % 3) T := by
    have h := twistedEntrywiseAut_add_mul_order TwistTag.D4 (j % 3) (j / 3) T
    rw [show j % 3 + j / 3 * ((TwistTag.D4.order : ℕ) : ℤ) = j by
      change j % 3 + j / 3 * 3 = j
      omega] at h
    exact h
  have hfix : fixSubgroup (twistedEntrywiseAut TwistTag.D4 j T) =
      fixSubgroup (twistedEntrywiseAut TwistTag.D4 (j % 3) T) := by rw [hper]
  rw [hfix]
  rcases hj with hj | hj
  · rw [hj]
    exact isSimpleGroup_and_not_commutative_twistedOne hℓ he hK T 1 (Or.inl rfl)
      (fun c => by simpa using hT c)
  · rw [hj]
    have hmain := isSimpleGroup_and_not_commutative_twistedOne hℓ he hK T⁻¹ 2 (Or.inr rfl) hinv
    have hfix2 : fixSubgroup (twistedEntrywiseAut TwistTag.D4 2 T) =
        fixSubgroup (twistedEntrywiseAut TwistTag.D4 1 T⁻¹) :=
      fixedSubgroup_twistedEntrywiseAut_D4_two T
    let e2 : ↥(fixSubgroup (twistedEntrywiseAut TwistTag.D4 2 T)) ≃*
        ↥(fixSubgroup (twistedEntrywiseAut TwistTag.D4 1 T⁻¹)) :=
      MulEquiv.subgroupCongr hfix2
    haveI : IsSimpleGroup ↥(fixSubgroup (twistedEntrywiseAut TwistTag.D4 1 T⁻¹)) := hmain.1
    refine ⟨e2.isSimpleGroup, ?_⟩
    obtain ⟨x, y, hxy⟩ := hmain.2
    exact ⟨e2.symm x, e2.symm y, fun h => hxy (by simpa using congrArg e2 h)⟩

private theorem glaPLayer_twistedEntrywise_ne_bot {K : Type} [Field K] [Finite K]
    {ℓ e : ℕ} (hℓ : ℓ.Prime) (he : 1 ≤ e) (hK : Nat.card K = (ℓ ^ e) ^ 3)
    (T : K ≃+* K) (hT : ∀ c, T c = c ^ (ℓ ^ e)) (j : ℤ)
    (hj : j % 3 = 1 ∨ j % 3 = 2)
    (hdvd : 3 ∣ Nat.card ↥(fixSubgroup (twistedEntrywiseAut TwistTag.D4 j T))) :
    GLAPLayer 3 (fixSubgroup (twistedEntrywiseAut TwistTag.D4 j T)) ≠ ⊥ := by
  obtain ⟨hs, hnc⟩ := isSimpleGroup_and_not_commutative_twisted hℓ he hK T hT j hj
  have hq : CFSG.IsQuasisimple ↥(fixSubgroup (twistedEntrywiseAut TwistTag.D4 j T)) :=
    LieSemisimple.isQuasisimple_of_isSimpleGroup hs hnc
  refine glaPLayer_fixSubgroup_ne_bot_of_quasisimple Nat.prime_three
    (x := twistedEntrywiseAut TwistTag.D4 j T)
    (T := fixSubgroup (twistedEntrywiseAut TwistTag.D4 j T)) le_rfl ?_ hq hdvd
  intro f hf t ht
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hf ht) (Subgroup.inv_mem _ hf)

private theorem glaPLayer_graphField_ne_bot {K : Type} [Field K] [Finite K]
    {α : MulAut (adjointGroup Tag.D4 K)} (hα3 : α ^ 3 = 1)
    (g : adjointGroup Tag.D4 K) (a : Fin Tag.D4.rank → Kˣ) (σ : K ≃+* K)
    (hσ1 : σ ≠ 1) (hσ3 : σ ^ 3 = 1) {ε : ℕ} (hε : ε = 1 ∨ ε = 2)
    (h3 : 3 ∣ Nat.card (adjointGroup Tag.D4 K))
    (hαeq : α = MulAut.conj g * (exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε)) :
    GLAPLayer 3 (fixSubgroup α) ≠ ⊥ := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨f, hℓp, hKf⟩ := FiniteField.card K (ringChar K)
  have hKf' : Nat.card K = ringChar K ^ (f : ℕ) := by
    rw [Nat.card_eq_fintype_card]
    exact hKf
  have hord : orderOf σ = 3 := orderOf_eq_prime hσ3 hσ1
  obtain ⟨e, T, he, hef, hT, hσT⟩ :=
    exists_frobenius_eq_or_inv_of_orderOf_three hℓp f.pos K hKf' σ hord
  have hK' : Nat.card K = (ringChar K ^ e) ^ 3 := by rw [hKf', ← hef, pow_mul]
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK', ← pow_mul]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ ringChar K ^ 2 := Nat.pow_le_pow_left hℓp.two_le 2
      _ ≤ ringChar K ^ (e * 3) := Nat.pow_le_pow_right hℓp.pos (by omega)
  have h3dvdα : 3 ∣ Nat.card ↥(fixSubgroup α) := by
    have hmod := CFSG.HardMathSupport.Lang.Proving.card_modEq_card_fixedPoints_of_pow_prime α hα3
    have hcard : Nat.card {y : adjointGroup Tag.D4 K // α y = y} = Nat.card (fixSubgroup α) :=
      Nat.card_congr (Equiv.refl _)
    rw [← hcard, Nat.dvd_iff_mod_eq_zero, ← hmod]
    exact Nat.dvd_iff_mod_eq_zero.1 h3
  haveI : Fact (ringChar K).Prime := ⟨hℓp⟩
  rcases hσT with hσT | hσT
  · have hαT : α = MulAut.conj g * (exactNormalAut Tag.D4 K a T 0 * d4Graph K ε) := by
      rw [hαeq, hσT]
    obtain ⟨ψ, hψ⟩ :=
      exists_conj_eq_twistedEntrywiseAut_of_normalForm K hKf' hK4 he hef T hT α hα3 g a ε hαT
    have hdvd : 3 ∣ Nat.card ↥(fixSubgroup (twistedEntrywiseAut TwistTag.D4 (ε : ℤ) T)) := by
      have e' : ↥(fixSubgroup α) ≃*
          ↥(fixSubgroup (twistedEntrywiseAut TwistTag.D4 (ε : ℤ) T)) :=
        (fixSubgroupConjEquiv ψ α).trans (MulEquiv.subgroupCongr (by rw [hψ]; rfl))
      rw [← Nat.card_congr e'.toEquiv]
      exact h3dvdα
    have hδ := glaPLayer_twistedEntrywise_ne_bot hℓp he hK' T hT (ε : ℤ)
      (by rcases hε with rfl | rfl <;> norm_num) hdvd
    exact glaPLayer_fixSubgroup_ne_bot_of_conj Nat.prime_three hψ hδ
  · have hαT : α = MulAut.conj g * (exactNormalAut Tag.D4 K a T⁻¹ 0 * d4Graph K ε) := by
      rw [hαeq, hσT]
    obtain ⟨ψ, hψ⟩ := exists_conj_inv_eq_twistedEntrywiseAut_of_normalForm K hKf' hK4 he hef
      T T⁻¹ hT (mul_inv_cancel T) α hα3 g a ε hαT
    have hdvd : 3 ∣
        Nat.card ↥(fixSubgroup (twistedEntrywiseAut TwistTag.D4 (-(ε : ℤ)) T)) := by
      have e' : ↥(fixSubgroup α) ≃*
          ↥(fixSubgroup (twistedEntrywiseAut TwistTag.D4 (-(ε : ℤ)) T)) :=
        ((MulEquiv.subgroupCongr (fixSubgroup_inv_eq α)).symm.trans
          ((fixSubgroupConjEquiv ψ α⁻¹).trans (MulEquiv.subgroupCongr (by rw [hψ]; rfl))))
      rw [← Nat.card_congr e'.toEquiv]
      exact h3dvdα
    have hδ := glaPLayer_twistedEntrywise_ne_bot hℓp he hK' T hT (-(ε : ℤ))
      (by rcases hε with rfl | rfl <;> norm_num) hdvd
    have hδ' : GLAPLayer 3 (fixSubgroup α⁻¹) ≠ ⊥ :=
      glaPLayer_fixSubgroup_ne_bot_of_conj Nat.prime_three hψ hδ
    rwa [fixSubgroup_inv_eq α] at hδ'

end CertSmallTwo

section CertTarget


theorem outerPLayerAt_adjointD4_three {K : Type} [Field K] [Finite K] (hK3 : ringChar K ≠ 3)
    (h3 : 3 ∣ Nat.card (adjointGroup Tag.D4 K)) : OuterPLayerAt 3 (adjointGroup Tag.D4 K) := by
  intro α hα3 hαout
  obtain ⟨g, a, σ, ε, hε3, hσ3, hαeq⟩ := exists_cube_normal_form_sigma α hα3
  interval_cases ε
  · have hα0 : α = MulAut.conj g * exactNormalAut Tag.D4 K a σ 0 := by
      rw [hαeq, d4Graph_zero, mul_one]
    by_cases hσ1 : σ = 1
    · subst hσ1
      rw [hα0] at hα3 hαout
      obtain ⟨h, hh⟩ := d4_inner_of_diag hK3 g a hα3
      exact absurd (hh ▸ (inner_le_innAutDerived _ ⟨h, rfl⟩)) hαout
    · rw [hα0] at hα3 ⊢
      obtain ⟨ψ, hψ⟩ :=
        ExcCopy.exists_conj_eq_entrywiseAdjointAut .D4 Nat.prime_three g a σ hσ1 hσ3 hα3
      exact glaPLayer_fixSubgroup_ne_bot_of_conj Nat.prime_three hψ
        (glaPLayer_entrywiseAdjointAut_ne_bot σ hσ3)
  · by_cases hσ1 : σ = 1
    · subst hσ1
      rw [hαeq] at hα3 hαout
      exact absurd (mem_innAutDerived_of_graphType g a (Or.inl rfl) hα3) hαout
    · exact glaPLayer_graphField_ne_bot hα3 g a σ hσ1 hσ3 (Or.inl rfl) h3 hαeq
  · by_cases hσ1 : σ = 1
    · subst hσ1
      rw [hαeq] at hα3 hαout
      exact absurd (mem_innAutDerived_of_graphType g a (Or.inr rfl) hα3) hαout
    · exact glaPLayer_graphField_ne_bot hα3 g a σ hσ1 hσ3 (Or.inr rfl) h3 hαeq

end CertTarget

section CertBridge


theorem outerPLayerAt_pomegaPlus_four_three {ℓ f : ℕ} (h3ℓ : 3 ≠ ℓ) {G : Type} [Group G]
    [Finite G] (h : CFSG.Open.StatedClassicalModel G .POmegaPlus 4 ℓ f)
    (h3 : 3 ∣ Nat.card G) : OuterPLayerAt 3 G := by
  obtain ⟨⟨hℓ, hf, -⟩, K, hfield, hfinite, hK, ⟨eG⟩⟩ := h
  letI := hfield
  letI := hfinite
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : CharP K ℓ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hℓ hf hK
  have hK3 : ringChar K ≠ 3 := by
    rw [ringChar.eq K ℓ]
    exact fun h' => h3ℓ h'.symm
  obtain ⟨eC⟩ :=
    CFSG.HardMathSupport.Lang.Coordinator.D4Bridge.nonempty_statedProj_equiv_adjointGroup K
  have h3' : 3 ∣ Nat.card (adjointGroup Tag.D4 K) := by
    rw [← Nat.card_congr (eG.trans eC).toEquiv]
    exact h3
  exact outerPLayerAt_congr Nat.prime_three (eG.trans eC).symm
    (outerPLayerAt_adjointD4_three hK3 h3')

end CertBridge

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
