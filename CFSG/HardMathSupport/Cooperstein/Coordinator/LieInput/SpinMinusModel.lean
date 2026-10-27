module

public import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDOdd
public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.SUModel
public import CFSG.RankThree.PartOne.CTP.SU4EvenBridge
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.GraphTwisted
import all TauCeti.GroupTheory.SpecificGroups.CFSG.TypeD
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Frobenius
import all TauCeti.Algebra.CharP.Frobenius.Fixed
public import CFSG.Adapters.ClassicalCatalogReverse

public noncomputable section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput

open TauCeti TauCeti.TypeDSpinCarrier CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
  CFSG.RankThree.PartTwo.Census.Carrier.SpinD

theorem exists_twist_root_of {L : Type} [Field L] [IsAlgClosed L] (θ : L →+* L) (S : Subfield L)
    (hS : ∀ x, x ∈ S ↔ θ x = x) (b c : S) (hirr : ∀ s : S, s ^ 2 + b * s + c ≠ 0) :
    ∃ ω : L, ω ≠ θ ω ∧ θ (θ ω) = ω ∧ -(ω + θ ω) = (b : L) ∧ ω * θ ω = (c : L) := by
  have hdeg : (Polynomial.C (1 : L) * Polynomial.X ^ 2 + Polynomial.C (b : L) * Polynomial.X +
      Polynomial.C (c : L)).degree ≠ 0 := by
    rw [Polynomial.degree_quadratic one_ne_zero]
    decide
  obtain ⟨ω, hω⟩ := IsAlgClosed.exists_root _ hdeg
  have hroot : ω ^ 2 + (b : L) * ω + c = 0 := by
    simpa [Polynomial.IsRoot] using hω
  have hθb : θ b = b := (hS b).1 b.2
  have hθc : θ c = c := (hS c).1 c.2
  have hroot' : θ ω ^ 2 + (b : L) * θ ω + c = 0 := by
    have h := congrArg θ hroot
    rwa [map_add, map_add, map_mul, map_pow, hθb, hθc, map_zero] at h
  have hne : ω ≠ θ ω := by
    intro h
    have hmem : ω ∈ S := (hS ω).2 h.symm
    refine hirr ⟨ω, hmem⟩ (Subtype.ext ?_)
    simpa using hroot
  have hsum : ω + θ ω = -(b : L) := by
    have h : (ω - θ ω) * (ω + θ ω + b) = 0 := by linear_combination hroot - hroot'
    rcases mul_eq_zero.1 h with h1 | h1
    · exact absurd (sub_eq_zero.1 h1) hne
    · linear_combination h1
  refine ⟨ω, hne, ?_, by rw [hsum]; ring, ?_⟩
  · have h := congrArg θ hsum
    rw [map_add, map_neg, hθb] at h
    linear_combination h - hsum
  · linear_combination ω * hsum - hroot

theorem exists_typeTwistedD_equiv_of_irr (r : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.twistedD r q).Valid)
    (b c : ↥(ValidLieTypeIndex.fixedField ⟨.twistedD r q, hv⟩))
    (hirr : ∀ s, s ^ 2 + b * s + c ≠ 0) :
    Nonempty (ValidLieTypeIndex.Group ⟨.twistedD r q, hv⟩ ≃*
      StatedProj (StatedOmega
        (StatedQuadMinus r ↥(ValidLieTypeIndex.fixedField ⟨.twistedD r q, hv⟩) b c))) := by
  have hr : 4 ≤ r := (LieTypeIndex.inStandardRange_iff _).mp ((LieTypeIndex.valid_iff _).mp hv).1
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
  have hS : ∀ x, x ∈ ValidLieTypeIndex.fixedField ⟨.twistedD (m + 1) q, hv⟩ ↔
      iterateFrobenius (ValidLieTypeIndex.Closure ⟨.twistedD (m + 1) q, hv⟩)
        (ValidLieTypeIndex.characteristic ⟨.twistedD (m + 1) q, hv⟩)
        (ValidLieTypeIndex.fieldExponent ⟨.twistedD (m + 1) q, hv⟩) x = x := by
    intro x
    rw [ValidLieTypeIndex.mem_fixedField, iterateFrobenius_def,
      ValidLieTypeIndex.fieldOrder_eq_characteristic_pow]
  have := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField ⟨.twistedD (m + 1) q, hv⟩
  obtain ⟨ω, hω, hθω, hb, hc⟩ := exists_twist_root_of _ _ hS b c hirr
  have hb' : coefB (iterateFrobenius (ValidLieTypeIndex.Closure ⟨.twistedD (m + 1) q, hv⟩)
      (ValidLieTypeIndex.characteristic ⟨.twistedD (m + 1) q, hv⟩)
      (ValidLieTypeIndex.fieldExponent ⟨.twistedD (m + 1) q, hv⟩)) _ hS hθω = b := Subtype.ext hb
  have hc' : coefC (iterateFrobenius (ValidLieTypeIndex.Closure ⟨.twistedD (m + 1) q, hv⟩)
      (ValidLieTypeIndex.characteristic ⟨.twistedD (m + 1) q, hv⟩)
      (ValidLieTypeIndex.fieldExponent ⟨.twistedD (m + 1) q, hv⟩)) _ hS hθω = c := Subtype.ext hc
  have e := dcqEquivTwistedFixed hr _ _ _ hS hω hθω
  rw [hb', hc'] at e
  exact ⟨e⟩

open CFSG.ClassicalInvolution.Upgrade CFSG.Adapters.RankTwoModelTransports CFSG.AGLEmbedding in
theorem isClassicalTwoOrG2_of_statedPOmegaMinus {G : Type} [Group G] {k f : ℕ}
    (h : StatedClassicalModel G .POmegaMinus k 2 f) : IsClassicalTwoOrG2 G := by
  obtain ⟨hadm, K, hfield, hfinite, hK, b, c, hirr, ⟨θ⟩⟩ := h
  let _ := hfield
  let _ := hfinite
  obtain ⟨hp, hf, hn⟩ := hadm
  let q : PrimePower := ⟨2, f, hp, by omega⟩
  have hv : (LieTypeIndex.twistedD k q).Valid := by
    rw [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff,
      LieTypeIndex.isDuplicateRepresentative_iff]
    exact ⟨hn, not_false⟩
  let d : ValidLieTypeIndex := ⟨.twistedD k q, hv⟩
  obtain ⟨φ⟩ := CFSG.ClassicalModels.nonempty_ringEquiv_validIndex_fixedField d K
    (by rw [hK]; simp [d, ValidLieTypeIndex.fieldOrder, q, TauCeti.PrimePower.card_def])
  obtain ⟨eT⟩ := exists_typeTwistedD_equiv_of_irr k q hv (φ b) (φ c) (irreducible_map φ hirr)
  exact Or.inl ⟨d, rfl, ⟨(θ.trans (statedProjCongr (glCongr φ)
    (map_statedOmega φ (statedQuadMinus_comp φ rfl rfl)) (glCongr_statedScalars φ))).trans
    eT.symm⟩⟩

section Short

open CFSG.LieType.Universal.Spin.Twisted CFSG.Timmesfeld.RankTwo CFSG.LieType.Steinberg
  CFSG.SectionRank.EvenCover CFSG.LieType.CurtisTits CFSG.LieType.RootSystem Matrix

variable
  (n : ℕ) {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}
  (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)

theorem charP_shortField : CharP (ShortField b c) 2 :=
  charP_of_injective_algebraMap (algebraMap F (ShortField b c)).injective 2

theorem card_shortField : Nat.card (ShortField b c) = Nat.card F ^ 2 := by
  rw [Nat.card_congr (QuadraticAlgebra.equivProd (-c) b), Nat.card_prod, sq]

theorem four_le_card_shortField : 4 ≤ Nat.card (ShortField b c) := by
  rw [card_shortField]
  have : 2 ≤ Nat.card F := by
    have := Finite.one_lt_card (α := F)
    omega
  nlinarith

include hirr in
noncomputable def shortEquiv (i : Fin (n - 1)) (hi : ¬ i.val + 1 < n - 1) :
    Matrix.SpecialLinearGroup (Fin 2) (ShortField b c) ≃*
      ↥(rankOne (minusDatum n hirr).rootGroup i) := by
  haveI := fact_shortField hirr
  haveI := finite_shortField (b := b) (c := c)
  haveI := charP_shortField (b := b) (c := c)
  let R := shortRels n hirr i
  have hex := exists_hom_of_rankOneRels R
  let Θ := hex.choose
  have hx : ∀ a, Θ (sl2Upper a) = R.x a := hex.choose_spec.1
  have hy : ∀ a, Θ (sl2Lower a) = R.y a := hex.choose_spec.2
  have hrange : Θ.range = R.sub := by
    apply le_antisymm
    · rintro _ ⟨g, rfl⟩
      have hg : g ∈ (sl2Rels (ShortField b c)).sub := by rw [sl2Rels_sub]; exact Subgroup.mem_top g
      refine Subgroup.closure_induction (p := fun g _ => Θ g ∈ R.sub) ?_ ?_ ?_ ?_ hg
      · rintro _ (⟨a, rfl⟩ | ⟨a, rfl⟩)
        · rw [show (sl2Rels (ShortField b c)).x a = sl2Upper a from sl2Rels_x a, hx]
          exact R.x_mem_sub a
        · rw [show (sl2Rels (ShortField b c)).y a = sl2Lower a from sl2Rels_y a, hy]
          exact R.y_mem_sub a
      · rw [map_one]; exact one_mem _
      · intro x y _ _ hx hy
        rw [map_mul]; exact mul_mem hx hy
      · intro x _ hx
        rw [map_inv]; exact inv_mem hx
    · rw [RankOneRels.sub, Subgroup.closure_le]
      rintro _ (⟨a, rfl⟩ | ⟨a, rfl⟩)
      · exact ⟨sl2Upper a, hx a⟩
      · exact ⟨sl2Lower a, hy a⟩
  have hquasi := (isChevComponent_sl (F := ShortField b c) (k := 2)
    (Or.inr ⟨rfl, four_le_card_shortField⟩)).1
  have hinj : Function.Injective Θ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    haveI : Θ.ker.Normal := MonoidHom.normal_ker Θ
    rcases le_center_or_eq_top_of_isQuasisimple hquasi Θ.ker with hz | htop
    · rw [eq_bot_iff]
      intro g hg
      obtain ⟨r, hr2, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp (hz hg)
      have hr1 : r = 1 := by
        have h2 : r ^ 2 = 1 := by simpa using hr2
        have : (r - 1) ^ 2 = 0 := by
          have h2' : (2 : ShortField b c) = 0 := CharTwo.two_eq_zero
          linear_combination h2 + (1 - r) * h2'
        exact sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp this)
      rw [Subgroup.mem_bot]
      apply Subtype.ext
      rw [← hr, hr1]
      simp
    · exfalso
      have h1 : Θ (sl2Upper (1 : ShortField b c)) = 1 := by
        have : sl2Upper (1 : ShortField b c) ∈ Θ.ker := by rw [htop]; exact Subgroup.mem_top _
        exact this
      rw [hx] at h1
      have h2 : shortPosHom n hirr i (.ofAdd (fieldCoord (1 : ShortField b c))) = 1 := h1
      rw [fieldCoord_one] at h2
      have h3 := twShortRoot_injective n hirr i true
        (h2.trans (twShortRoot_ofAdd_zero n hirr i true).symm)
      exact planeOne_ne_zero (K := F) (Multiplicative.ofAdd.injective h3)
  exact (MonoidHom.ofInjective hinj).trans
    (MulEquiv.subgroupCongr (hrange.trans ((shortRels_sub n hirr i).trans
      (rankOne_minusRootGroup_of_not_lt n hirr hi).symm)))

end Short

section Chev

open CFSG.AGLEmbedding

variable
  {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}
  (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)

include hirr in
theorem isChevComponent_spinMinus {k : ℕ} (hk : 4 ≤ k) :
    CFSG.IsQuasisimple (spinGroup (quadMinus k F b c)) ∧
      IsClassicalTwoOrG2 (spinGroup (quadMinus k F b c) ⧸
        Subgroup.center (spinGroup (quadMinus k F b c))) := by
  obtain ⟨f, hf1, hfcard⟩ := CFSG.AGLEmbedding.ParabHub.exists_card_eq_two_pow F
  exact ⟨isQuasisimple_spinGroup_quadMinus hk hirr,
    isClassicalTwoOrG2_of_statedPOmegaMinus
      (statedClassicalModel_spin_quadMinus ⟨Nat.prime_two, hf1, hk⟩ hfcard hirr)⟩

include hirr in
theorem chev_spinMinus_three :
    CFSG.IsQuasisimple (spinGroup (quadMinus 3 F b c)) ∧
      IsClassicalTwoOrG2 (spinGroup (quadMinus 3 F b c) ⧸
        Subgroup.center (spinGroup (quadMinus 3 F b c))) := by
  obtain ⟨f, hf1, hfcard⟩ := CFSG.AGLEmbedding.ParabHub.exists_card_eq_two_pow F
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let K := GaloisField 2 (2 * f)
  have hKcard : Nat.card K = (2 ^ f) ^ 2 := by
    rw [GaloisField.card _ _ (by omega), ← pow_mul, mul_comm]
  haveI : CharP K 2 := inferInstance
  obtain ⟨_, e, -⟩ := CFSG.RankThree.PartOne.CTP.SU4Even.exists_equiv_su_four_even
    (F := F) (K := K) hfcard hKcard hirr
  have hnq : ((4 : ℕ), 2 ^ f) ≠ (3, 2) := fun h => by
    have := congrArg Prod.fst h
    simp at this
  have hsu := isChevComponent_su (F := K) (f := f) hKcard (n' := 4) (by norm_num) hnq
  exact ⟨isQuasisimple_of_mulEquiv e.symm hsu.1,
    isClassicalTwoOrG2_of_mulEquiv (CFSG.Quasithin.SmithC27.quotCenterCongr e.symm) hsu.2⟩

end Chev

end CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput
