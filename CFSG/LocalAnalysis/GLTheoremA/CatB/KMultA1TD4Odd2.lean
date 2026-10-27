module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.KMultA1
public import CFSG.LocalAnalysis.GLTheoremA.CatB.KMultA1TD4Odd
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator.Bridge
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs2311v
public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.ExcTriThree
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.R2Aux.G2Part3
public import CFSG.LocalAnalysis.SeitzReduction.CrossChar
public import CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridgeHolds
public import CFSG.Assembly.InCatalogConverse
public import CFSG.RankThree.PartTwo.Sec11.SetUp1118ProofCarrier
public import CFSG.RankThree.PartTwo.Sec13.Item136PGL
public import CFSG.RankThree.PartTwo.Sec13.Item138NMod9
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowLiePGL
public import CFSG.HardMathSupport.Lang.Triality.G2ClassOrder
public import CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3.FieldActorFixed
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TriD4Outer
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorBasic
public import CFSG.GH74.GLS.IVK.Proofs2.GHInvShape
public import CFSG.Assembly.Subnormal
public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.ClosingMinus.Escape.Final
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FRResTD4
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FRResTwF4
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs2311t2

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.KMultA1TD4Odd

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.ComponentClassification.CatLeaf
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem data_g2n
    {T : Type} [Group T] {n : ℕ} (hT : catalogIs T (S10.isG2n n)) :
    Finite T ∧ IsSimpleGroup T ∧ ¬ Group.IsSolvable T ∧ StatedLieAdmissible .G2 0 2 n ∧
      Nat.card T * lieOrderDivisor .G2 0 (2 ^ n) = lieOrderNumerator .G2 0 (2 ^ n) := by
  obtain ⟨i, hi, ⟨e⟩⟩ := hT
  cases i with
  | cyclic p hp => simp [S10.isG2n, onLie] at hi
  | alternating m hm => simp [S10.isG2n, onLie] at hi
  | sporadic s => simp [S10.isG2n, onLie] at hi
  | lie idx =>
    obtain ⟨d, hv⟩ := idx
    cases d with
    | G2 q =>
      simp only [S10.isG2n, onLie] at hi
      obtain ⟨hp, hn⟩ := hi
      obtain ⟨hfin, hsimp⟩ := CFSG.Assembly.lie_finite_simple ⟨.G2 q, hv⟩
      haveI : Finite (TauCeti.CFSGIndex.lie ⟨.G2 q, hv⟩).Group := hfin
      haveI : IsSimpleGroup (TauCeti.CFSGIndex.lie ⟨.G2 q, hv⟩).Group := hsimp
      haveI : Finite T := Finite.of_equiv _ e.symm.toEquiv
      haveI : IsSimpleGroup T := e.isSimpleGroup
      haveI : Group.IsPerfect (TauCeti.CFSGIndex.lie ⟨.G2 q, hv⟩).Group :=
        CFSG.RankThree.PartTwo.Sec11.SetUp1118Proof.isPerfect_lie_G2 q hv
      haveI : Nontrivial (TauCeti.CFSGIndex.lie ⟨.G2 q, hv⟩).Group := IsSimpleGroup.toNontrivial
      have hns : ¬ Group.IsSolvable T := by
        intro hs
        exact Group.IsPerfect.not_isSolvable _
          (Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective)
      have hq : q.card = 2 ^ n := by rw [TauCeti.PrimePower.card_def, hp, hn]
      have h3 : 3 ≤ q.card := by
        have h := ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
        simpa only [TauCeti.LieTypeIndex.inStandardRange_iff] using h
      have hn1 : 1 ≤ n := by rw [← hn]; exact q.exponent_pos
      refine ⟨inferInstance, inferInstance, hns, ⟨Nat.prime_two, hn1, rfl, hq ▸ h3⟩, ?_⟩
      have hcard := CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds ⟨.G2 q, hv⟩ T ⟨e⟩
      rw [hcard]
      show CFSG.Open.orderG2 q.card * 1 = _
      rw [hq, mul_one]
      rfl
    | _ => simp [S10.isG2n, onLie] at hi

@[expose] def IsFixedLieShape (ℓ : ℕ) (t' : StatedLieTag) (n' : ℕ) : Prop :=
  (t' = .G2 ∧ n' = 0) ∨ (t' = .PSL ∧ n' = 3) ∨ (t' = .PSU ∧ n' = 3) ∨ (t' = .PSL ∧ n' = 2 ∧ ℓ = 3)

theorem false_of_lieOrder {t : StatedLieTag} {n m M : ℕ} (hadm : StatedLieAdmissible t n 2 m)
    (hM : M * lieOrderDivisor t n (2 ^ m) = lieOrderNumerator t n (2 ^ m))
    {t' : StatedLieTag} {n' ℓ f : ℕ} (hsh : IsFixedLieShape ℓ t' n')
    (hadm' : StatedLieAdmissible t' n' ℓ f) (hℓ2 : ℓ ≠ 2)
    (hM' : M * lieOrderDivisor t' n' (ℓ ^ f) = lieOrderNumerator t' n' (ℓ ^ f)) : False := by
  have hf : 1 ≤ f := hadm'.2.1
  have h3 : 3 ∣ 3 ^ f := dvd_pow_self 3 (by omega)
  rcases CFSG.SeitzReduction.CrossChar.crossChar_arith hadm hadm' hℓ2 hM hM' with
    ⟨-, -, -, rfl, rfl, h5⟩ | ⟨-, -, -, rfl, rfl, h7⟩ | ⟨-, -, -, rfl, -, -⟩
  · rcases hsh with ⟨h, -⟩ | ⟨-, h⟩ | ⟨h, -⟩ | ⟨-, -, rfl⟩
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · rw [h5] at h3
      exact absurd h3 (by decide)
  · rcases hsh with ⟨h, -⟩ | ⟨-, h⟩ | ⟨h, -⟩ | ⟨-, -, rfl⟩
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · rw [h7] at h3
      exact absurd h3 (by decide)
  · rcases hsh with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> exact absurd h (by decide)

theorem three_le_pow_of_odd {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f) : 3 ≤ ℓ ^ f := by
  have h2 := hℓ.two_le
  have h3 : 3 ≤ ℓ := by omega
  calc 3 ≤ ℓ := h3
    _ = ℓ ^ 1 := (pow_one ℓ).symm
    _ ≤ ℓ ^ f := Nat.pow_le_pow_right hℓ.pos hf

section G2Fix


theorem order_g2Class {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    {T : Type} [Group T] [IsSimpleGroup T]
    (h : SubnQuot ↥(CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup
      (fieldActor (t := TwistTag.D4) σ σ)) T) :
    StatedLieAdmissible .G2 0 ℓ f ∧
      Nat.card T * lieOrderDivisor .G2 0 (ℓ ^ f) = lieOrderNumerator .G2 0 (ℓ ^ f) := by
  haveI := CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3.isSimpleGroup_fixSubgroup_fieldActor_D4
    ℓ f hℓ hℓ2 K hK σ hσ
  haveI : Nontrivial T := IsSimpleGroup.toNontrivial
  have hcard := h.card_eq_of_isSimpleGroup
  have h2 := CFSG.HardMathSupport.Lang.Triality.card_fixed_fieldActor_D4_of_frobenius hℓ hf hK σ hσ
  refine ⟨⟨hℓ, hf, rfl, three_le_pow_of_odd hℓ hℓ2 hf⟩, ?_⟩
  rw [hcard]
  show _ * 1 = _
  rw [mul_one, ← h2]
  rfl

end G2Fix

theorem order_pglClass {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hℓ3 : ℓ ≠ 3) (hf : 1 ≤ f)
    {X T : Type} [Group X] [Group T] [IsSimpleGroup T] (hT : ¬ Group.IsSolvable T)
    (hX : CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHigh3.IsPGLPiThree X (ℓ ^ f))
    (h : SubnQuot X T) :
    ∃ (t' : StatedLieTag) (n' : ℕ), IsFixedLieShape ℓ t' n' ∧ StatedLieAdmissible t' n' ℓ f ∧
      Nat.card T * lieOrderDivisor t' n' (ℓ ^ f) = lieOrderNumerator t' n' (ℓ ^ f) := by
  obtain ⟨π, p, f', F, _, hF, hpf, hmod, ⟨e⟩⟩ := hX
  have h5 : 5 ≤ ℓ ^ f :=
    CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311v.five_le_pow_inputs2311v hℓ hℓ2 hℓ3 hf
  rw [← hpf] at e hmod
  have h2 : 2 < p ^ f' := by omega
  have hπ : π = false → CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f' F := fun h => by
    subst h; exact hF.unitary
  set P := CFSG.PGLModel.projImage (CFSG.RankThree.PartTwo.Sec4.glPi π 3 (p ^ f') F) with hP
  have hSP : CFSG.PGLModel.projImage (CFSG.RankThree.PartTwo.Sec4.slPi π 3 (p ^ f') F) ≤ P :=
    Subgroup.map_mono (CFSG.RankThree.PartTwo.Sec4.slPi_le_glPi hπ)
  have h1 : SubnQuot ↥P T := h.of_mulEquiv e
  haveI : Group.IsSolvable (↥P ⧸ commutator ↥P) := isSolvable_quot_commutator
  have h3 : SubnQuot ↥(commutator ↥P) T := h1.normal hT (commutator ↥P)
  have h4 : SubnQuot ↥(CFSG.PGLModel.projImage (CFSG.RankThree.PartTwo.Sec4.slPi π 3 (p ^ f') F)) T :=
    h3.of_mulEquiv ((MulEquiv.subgroupCongr
      (CFSG.RankThree.PartTwo.Sec13.commutator_projImage_glPi hF h2)).trans
        (Subgroup.subgroupOfEquivOfLe hSP))
  haveI := CFSG.RankThree.PartTwo.Sec4.RonanK429Lie.isSimpleGroup_projImage_slPi hF (Or.inr h2)
  haveI : Nontrivial T := IsSimpleGroup.toNontrivial
  have hcard := h4.card_eq_of_isSimpleGroup
  have h6 := CFSG.RankThree.PartTwo.Sec13.card_projImage_slPi_mul_three hF hmod
  rw [← hcard, hpf] at h6
  rw [hpf] at hmod
  set q := ℓ ^ f with hq
  have hq2 : q ≠ 2 := by omega
  cases π with
  | false =>
    have hmod' : q % 3 = 2 := hmod
    refine ⟨.PSU, 3, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)),
      ⟨hℓ, hf, le_rfl, fun h => hq2 (Prod.mk.inj h).2⟩, ?_⟩
    have hD : lieOrderDivisor .PSU 3 q = 3 := by
      show Nat.gcd 3 (q + 1) = 3
      exact Nat.gcd_eq_left (Nat.dvd_of_mod_eq_zero (by omega))
    have hN : lieOrderNumerator .PSU 3 q = q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) := by
      show q ^ (3 * (3 - 1) / 2) * ∏ i ∈ Finset.Icc 2 3, (if Even i then q ^ i - 1 else q ^ i + 1) = _
      rw [show Finset.Icc 2 3 = {2, 3} by decide, Finset.prod_pair (by decide),
        if_pos (by decide : Even 2), if_neg (by decide : ¬ Even 3)]
    rw [hD, hN, h6]
    simp only [Bool.cond_false]
    ring
  | true =>
    have hmod' : q % 3 = 1 := hmod
    refine ⟨.PSL, 3, Or.inr (Or.inl ⟨rfl, rfl⟩),
      ⟨hℓ, hf, by norm_num, fun h => by simp at h, fun h => by simp at h⟩, ?_⟩
    have hD : lieOrderDivisor .PSL 3 q = 3 := by
      show Nat.gcd 3 (q - 1) = 3
      exact Nat.gcd_eq_left (Nat.dvd_of_mod_eq_zero (by omega))
    have hN : lieOrderNumerator .PSL 3 q = q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) := by
      show q ^ (3 * (3 - 1) / 2) * ∏ i ∈ Finset.Icc 2 3, (q ^ i - 1) = _
      rw [show Finset.Icc 2 3 = {2, 3} by decide, Finset.prod_pair (by decide)]
    rw [hD, hN, h6]
    simp only [Bool.cond_true]
    ring

section G2Top


theorem order_g2TopCentralizer {K : Type} [Field K] [Finite K] [CharP K 3] {y : K} (hy : y ≠ 0)
    {T : Type} [Group T] [IsSimpleGroup T] (hT : ¬ Group.IsSolvable T)
    (h : SubnQuot ↥(Subgroup.centralizer
      ({CFSG.HardMathSupport.Dickson.Sec6.I923.R2Aux.g2Top K y} : Set ↥(adjointGroup .G2 K))) T) :
    4 ≤ Nat.card K ∧ 2 * Nat.card T = Nat.card K * (Nat.card K ^ 2 - 1) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set D : Subgroup (adjointGroup .G2 K) :=
    Subgroup.centralizer {CFSG.HardMathSupport.Dickson.Sec6.I923.R2Aux.g2Top K y} with hDdef
  set Q' : Subgroup (adjointGroup .G2 K) :=
    (CFSG.HardMathSupport.Dickson.Sec6.I923.R2Aux.g2Q K).subgroupOf (adjointGroup .G2 K) with hQ'def
  have hmemQ' : ∀ g : adjointGroup .G2 K, g ∈ Q' ↔
      (g : ModGL .G2 K) ∈ CFSG.HardMathSupport.Dickson.Sec6.I923.R2Aux.g2Q K := fun g => Iff.rfl
  have hmemD : ∀ g : adjointGroup .G2 K, g ∈ D ↔
      (g : ModGL .G2 K) * pinnedX .G2 K CFSG.ComponentClassification.UnbalancedCatalog.g2c y =
        pinnedX .G2 K CFSG.ComponentClassification.UnbalancedCatalog.g2c y * (g : ModGL .G2 K) := by
    intro g
    rw [hDdef, Subgroup.mem_centralizer_singleton_iff]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have hdec : ∀ g ∈ D, ∃ q ∈ CFSG.HardMathSupport.Dickson.Sec6.I923.R2Aux.g2Q K,
      ∃ l ∈ CFSG.ComponentClassification.UnbalancedCatalog.g2RankOne K
        CFSG.ComponentClassification.UnbalancedCatalog.g2ir, (g : ModGL .G2 K) = q * l :=
    fun g hg => CFSG.HardMathSupport.Dickson.Sec6.I923.R2Aux.exists_mem_mul_of_commute_c g.2 hy
      ((hmemD g).1 hg)
  have hQn : ∀ g ∈ D, ∀ n ∈ Q', g * n * g⁻¹ ∈ Q' := by
    intro g hg n hn
    obtain ⟨q, hq, l, hl, hgql⟩ := hdec g hg
    rw [hmemQ'] at hn ⊢
    have h1 : ((g * n * g⁻¹ : adjointGroup .G2 K) : ModGL .G2 K) =
        q * (l * (n : ModGL .G2 K) * l⁻¹) * q⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hgql, mul_inv_rev]
      group
    rw [h1]
    exact mul_mem (mul_mem hq
      (CFSG.HardMathSupport.Dickson.Sec6.I923.R2Aux.g2RankOne_normalizes_g2Q hl hn)) (inv_mem hq)
  have hQp : IsPGroup 3 Q' :=
    (CFSG.HardMathSupport.Dickson.Sec6.I923.R2Aux.g2Q_isPGroup (K := K) 3).comap_of_injective
      (adjointGroup .G2 K).subtype (adjointGroup .G2 K).subtype_injective
  set N0 : Subgroup ↥D := Q'.subgroupOf D with hN0
  haveI hN0n : N0.Normal := ⟨fun n hn g => by
    rw [hN0, Subgroup.mem_subgroupOf] at hn ⊢
    exact hQn g g.2 n hn⟩
  haveI hN0p : IsPGroup 3 ↥N0 := hQp.comap_of_injective D.subtype D.subtype_injective
  haveI : Group.IsNilpotent ↥N0 := IsPGroup.isNilpotent hN0p
  haveI : Group.IsSolvable ↥N0 := inferInstance
  set L'' : Subgroup (adjointGroup .G2 K) :=
    (CFSG.ComponentClassification.UnbalancedCatalog.g2RankOne K
      CFSG.ComponentClassification.UnbalancedCatalog.g2ir).subgroupOf (adjointGroup .G2 K) with hL''
  have hL''mem : ∀ g : adjointGroup .G2 K, g ∈ L'' ↔
      (g : ModGL .G2 K) ∈ CFSG.ComponentClassification.UnbalancedCatalog.g2RankOne K
        CFSG.ComponentClassification.UnbalancedCatalog.g2ir := fun g => Iff.rfl
  have hL''D : L'' ≤ D := fun g hg => (hmemD g).2
    ((CFSG.HardMathSupport.Dickson.Sec6.I923.R2Aux.commute_g2RankOne_pinnedX_c ((hL''mem g).1 hg) y).eq)
  let ψ : ↥L'' →* ↥D ⧸ N0 := (QuotientGroup.mk' N0).comp (Subgroup.inclusion hL''D)
  have hψ : Function.Surjective ψ := by
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨q, hq, l, hl, hgql⟩ := hdec g g.2
    set qP : adjointGroup .G2 K :=
      ⟨q, CFSG.HardMathSupport.Dickson.Sec6.I923.R2Aux.g2Q_le_adjointGroup hq⟩ with hqP_def
    set lP : adjointGroup .G2 K :=
      ⟨l, CFSG.ComponentClassification.UnbalancedCatalog.g2RankOne_le_adjointGroup _ hl⟩ with hlP_def
    have hqP : qP ∈ Q' := (hmemQ' _).2 hq
    have hlP : lP ∈ L'' := (hL''mem _).2 hl
    have hgeq : (g : adjointGroup .G2 K) = qP * lP := Subtype.ext hgql
    refine ⟨⟨lP, hlP⟩, ?_⟩
    show QuotientGroup.mk (Subgroup.inclusion hL''D ⟨lP, hlP⟩) = QuotientGroup.mk g
    rw [QuotientGroup.eq, hN0, Subgroup.mem_subgroupOf]
    have e : (((Subgroup.inclusion hL''D ⟨lP, hlP⟩)⁻¹ * g : ↥D) : adjointGroup .G2 K) =
        lP⁻¹ * qP * lP⁻¹⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hgeq]
      simp only [Subgroup.coe_inclusion]
      group
    rw [e]
    exact hQn lP⁻¹ (inv_mem (hL''D hlP)) qP hqP
  have h1 : SubnQuot (↥D ⧸ N0) T := h.quotient hT N0
  have h2 : SubnQuot ↥L'' T := h1.comap ψ hψ
  obtain ⟨eL⟩ := CFSG.HardMathSupport.Dickson.Sec6.I923.R2Aux.nonempty_mulEquiv_g2RankOne (K := K)
  have h3 : SubnQuot (Matrix.SpecialLinearGroup (Fin 2) K) T :=
    h2.of_mulEquiv ((Subgroup.subgroupOfEquivOfLe
      (CFSG.ComponentClassification.UnbalancedCatalog.g2RankOne_le_adjointGroup _)).trans eL.symm)
  have h4 : 4 ≤ Nat.card K := by
    by_contra hlt
    have hdvd : (3 : ℕ) ∣ Nat.card K := by
      haveI : Fintype K := Fintype.ofFinite K
      rw [Nat.card_eq_fintype_card]
      obtain ⟨n, -, hn⟩ := FiniteField.card K 3
      rw [hn]
      exact dvd_pow_self 3 (PNat.ne_zero n)
    have h3K : 3 ≤ Nat.card K := Nat.le_of_dvd Nat.card_pos hdvd
    have hK3 : Nat.card K = 3 := by omega
    haveI := CFSG.GH74.GLS.IVK.GHInv.isSolvable_sl2_of_card_three hK3
    exact not_subnQuot_of_isSolvable hT h3
  refine ⟨h4, ?_⟩
  obtain ⟨-, hsimp, -⟩ := CFSG.GH74.GLS.IVK.GHInv.isQuasisimple_sl2 (K := K) h4
  haveI := hsimp
  have hcard := h3.card_eq_centerQuot hT
  have hchar : ringChar K ≠ 2 := by rw [ringChar.eq K 3]; norm_num
  rw [hcard]
  exact CFSG.ComponentClassification.ExcSelector.two_mul_card_centralQuotient_of_equiv_sl2 hchar
    (MulEquiv.refl _)

end G2Top

section ClassB


theorem order_classB {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] [CharP K 3]
    (hK : Nat.card K = (3 ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (3 ^ f)) {c : K}
    (hc : σ c = c) (hc0 : c ≠ 0) {T : Type} [Group T] [IsSimpleGroup T] (hT : ¬ Group.IsSolvable T)
    (h : SubnQuot ↥(CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup
      (MulAut.conj (CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3.longElt hf hK σ hσ
        (Or.inr (Or.inr rfl)) c hc) * fieldActor (t := TwistTag.D4) σ σ)) T) :
    StatedLieAdmissible .PSL 2 3 f ∧
      Nat.card T * lieOrderDivisor .PSL 2 (3 ^ f) = lieOrderNumerator .PSL 2 (3 ^ f) := by
  rw [CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3.fixSubgroup_conj_mul_fieldActor_eq hf hK σ hσ
    hc hc0] at h
  have hzJ := CFSG.HardMathSupport.Dickson.Sec6.I923.R2Aux.longElt_mem_fix hf hK σ hσ
    (Or.inr (Or.inr rfl)) hc
  have h1 := h.of_mulEquiv (CFSG.HardMathSupport.Dickson.Sec6.I923.R2Aux.infCentralizerEquiv _ _ hzJ
    (CFSG.HardMathSupport.Dickson.Sec6.I923.R2Aux.fixEquivG2 hf hK σ hσ))
  obtain ⟨g, c'', hc'', hE⟩ :=
    CFSG.HardMathSupport.Dickson.Sec6.I923.R2Aux.exists_conj_g2Top hf hK σ hσ hc hc0
  rw [hE] at h1
  have e := CFSG.HardMathSupport.Dickson.Sec6.I923.R2Aux.centralizerEquiv (MulAut.conj g).symm
    (g * CFSG.HardMathSupport.Dickson.Sec6.I923.R2Aux.g2Top (fixSubfield σ) c'' * g⁻¹)
  have hconj : (MulAut.conj g).symm
      (g * CFSG.HardMathSupport.Dickson.Sec6.I923.R2Aux.g2Top (fixSubfield σ) c'' * g⁻¹) =
      CFSG.HardMathSupport.Dickson.Sec6.I923.R2Aux.g2Top (fixSubfield σ) c'' := by
    simp [MulAut.conj_symm_apply, mul_assoc]
  rw [hconj] at e
  obtain ⟨h4, hcard⟩ := order_g2TopCentralizer hc'' hT (h1.of_mulEquiv e)
  have hk : Nat.card (fixSubfield σ) = 3 ^ f :=
    CFSG.RankThree.PartOne.KGD.card_fixSubfield_cube Nat.prime_three hf hK σ hσ
  rw [hk] at h4 hcard
  have hodd : Odd (3 ^ f) := Odd.pow (by decide)
  refine ⟨⟨Nat.prime_three, hf, le_rfl, fun h => ?_, fun h => ?_⟩, ?_⟩
  · have := (Prod.mk.inj h).2
    omega
  · have := (Prod.mk.inj h).2
    omega
  · have hD : lieOrderDivisor .PSL 2 (3 ^ f) = 2 := by
      show Nat.gcd 2 (3 ^ f - 1) = 2
      obtain ⟨k, hk⟩ := hodd
      exact Nat.gcd_eq_left (Nat.dvd_of_mod_eq_zero (by omega))
    have hN : lieOrderNumerator .PSL 2 (3 ^ f) = 3 ^ f * ((3 ^ f) ^ 2 - 1) := by
      show (3 ^ f) ^ (2 * (2 - 1) / 2) * ∏ i ∈ Finset.Icc 2 2, ((3 ^ f) ^ i - 1) = _
      rw [Finset.Icc_self, Finset.prod_singleton]
      norm_num
    rw [hD, hN, mul_comm, hcard]

end ClassB

section Orders


theorem exists_lieOrder_of_subnQuot {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (β : MulAut ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hβ3 : β ^ 3 = 1)
    (hβout : β ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner
      ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    {T : Type} [Group T] [IsSimpleGroup T] (hT : ¬ Group.IsSolvable T)
    (h : SubnQuot ↥(CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup β) T) :
    ∃ (t' : StatedLieTag) (n' : ℕ), IsFixedLieShape ℓ t' n' ∧ StatedLieAdmissible t' n' ℓ f ∧
      Nat.card T * lieOrderDivisor t' n' (ℓ ^ f) = lieOrderNumerator t' n' (ℓ ^ f) := by
  by_cases hℓ3 : ℓ = 3
  · subst hℓ3
    haveI := CFSG.HardMathSupport.Dickson.DefCharOuter.Export.exc_charP_three_of_card K hK
    refine CFSG.HardMathSupport.Dickson.DefCharOuter.Export.three_of_classes_gen hf hK σ hσ
      (fun γ => SubnQuot ↥(CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup γ) T →
        ∃ (t' : StatedLieTag) (n' : ℕ), IsFixedLieShape 3 t' n' ∧ StatedLieAdmissible t' n' 3 f ∧
          Nat.card T * lieOrderDivisor t' n' (3 ^ f) = lieOrderNumerator t' n' (3 ^ f))
      ?_ ?_ ?_ ?_ β hβ3 hβout h
    · intro ε γ hP hγ
      exact hP (hγ.of_mulEquiv
        (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.fixSubgroupConjEquiv ε γ))
    · intro γ hP hγ
      rw [← CFSG.HardMathSupport.Dickson.DefCharOuter.Export.exc_fixSubgroup_inv γ] at hγ
      exact hP hγ
    · intro hA
      exact ⟨.G2, 0, Or.inl ⟨rfl, rfl⟩, order_g2Class Nat.prime_three (by norm_num) hf hK σ hσ hA⟩
    · intro c hc hc0 hB
      exact ⟨.PSL, 2, Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)),
        order_classB hf hK σ hσ hc hc0 hT hB⟩
  · by_cases hG : CFSG.LieType.SeitzGeneration.ExcWideThree.TriOddIsGLine σ β
    · obtain ⟨φ, hφ⟩ := hG
      have h1 := h.of_mulEquiv
        (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.fixSubgroupConjEquiv φ β)
      have h2 : SubnQuot ↥(CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup
          (fieldActor (t := TwistTag.D4) σ σ)) T := by
        rcases hφ with hφ | hφ
        · rw [hφ] at h1
          exact h1
        · rw [hφ, CFSG.HardMathSupport.Dickson.DefCharOuter.Export.exc_fixSubgroup_inv] at h1
          exact h1
      exact ⟨.G2, 0, Or.inl ⟨rfl, rfl⟩, order_g2Class hℓ hℓ2 hf hK σ hσ h2⟩
    · have hX := CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311v.triOddA2FixPGL_holds ℓ f hℓ
        hℓ2 hℓ3 hf K hK σ hσ β hβ3 hβout hG
      refine order_pglClass hℓ hℓ2 hℓ3 hf hT hX (h.of_mulEquiv (MulEquiv.subgroupCongr ?_))
      ext x
      exact Iff.rfl

theorem not_subnQuot_fixSub_of_charTwo {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid) (hq : q.p ≠ 2) {S : Type} [Group S]
    (e₀ : S ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hv⟩).Group) (β : MulAut S) (hβ3 : β ^ 3 = 1)
    (hβout : β ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner S)
    {T : Type} [Group T] [IsSimpleGroup T] (hT : ¬ Group.IsSolvable T) {t : StatedLieTag} {n m : ℕ}
    (hadm : StatedLieAdmissible t n 2 m)
    (hM : Nat.card T * lieOrderDivisor t n (2 ^ m) = lieOrderNumerator t n (2 ^ m)) :
    ¬ SubnQuot ↥(CFSG.LocalAnalysis.GLTheoremA.FP.fixSub β) T := by
  intro h0
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e₁⟩⟩ :=
    CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator.exists_cat_model_trialityD4_odd hv hq
  set E : S ≃* ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := e₀.trans e₁ with hE
  have h0' : SubnQuot ↥(CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup β) T := h0
  have h1 := h0'.of_mulEquiv
    (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.fixSubgroupCongrEquiv E β)
  have hβ'3 : MulAut.congr E β ^ 3 = 1 := by rw [← map_pow, hβ3, map_one]
  have hβ'out : MulAut.congr E β ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner
      ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
    rintro ⟨c, hc⟩
    apply hβout
    refine ⟨E.symm c, ?_⟩
    ext x
    have h2 : (MulAut.conj c) (E x) = (MulAut.congr E β) (E x) := by rw [hc]
    have h3 : c * E x * c⁻¹ = E (β x) := by
      have h4 : (MulAut.congr E β) (E x) = E (β (E.symm (E x))) := rfl
      rw [h4, MulEquiv.symm_apply_apply] at h2
      exact h2
    rw [MulAut.conj_apply]
    apply E.injective
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, h3]
  obtain ⟨t', n', hsh, hadm', hM'⟩ := exists_lieOrder_of_subnQuot q.prime_p hq q.exponent_pos hK σ hσ
    _ hβ'3 hβ'out hT h1
  exact false_of_lieOrder hadm hM hsh hadm' hq hM'

theorem td4OddNoG2Layer_holds : CFSG.LocalAnalysis.GLTheoremA.CatB.KMultA1.TD4OddNoG2Layer := by
  intro S _ hS β hβ3 hβout J hJ n T _ hT φ hφ
  obtain ⟨-, hTsimp, hTns, hadm, hM⟩ := data_g2n hT
  haveI := hTsimp
  have hJle : J ≤ CFSG.LocalAnalysis.GLTheoremA.FP.fixSub β := hJ.le
  have h0 : SubnQuot ↥(CFSG.LocalAnalysis.GLTheoremA.FP.fixSub β) T :=
    ⟨J.subgroupOf (CFSG.LocalAnalysis.GLTheoremA.FP.fixSub β), hJ.subgroupOf,
      φ.comp (Subgroup.subgroupOfEquivOfLe hJle).toMonoidHom,
      hφ.comp (Subgroup.subgroupOfEquivOfLe hJle).surjective⟩
  obtain ⟨i, hi, ⟨e₀⟩⟩ := hS
  cases i with
  | cyclic p hp => simp [onLie] at hi
  | alternating m hm => simp [onLie] at hi
  | sporadic s => simp [onLie] at hi
  | lie idx =>
    obtain ⟨d, hv⟩ := idx
    cases d with
    | trialityD4 q =>
      simp only [onLie] at hi
      exact not_subnQuot_fixSub_of_charTwo hv hi e₀ β hβ3 hβout hTns hadm hM h0
    | _ => simp [onLie] at hi

end Orders

end CFSG.LocalAnalysis.GLTheoremA.CatB.KMultA1TD4Odd
