module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2TwAModel
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTable
public import CFSG.Adapters.ClassicalCatalogLinearUnitary
public import CFSG.Adapters.ClassicalCatalogReverse
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Blueprint.SourceClassicalTransportOrthogonal
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.ClassicalArith
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.Shared
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Num
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20x
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankSmall
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankAlt
public import CFSG.Adapters.TauCetiExceptional.EvenBridgeG2
public import CFSG.Adapters.LinearFieldTransport
public import CFSG.Assembly.GL83StatedBridge
public import CFSG.LocalAnalysis.StandardType.MarkingClassical
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinBBridge
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinDOdd
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDOdd
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2Carrier
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
public import CFSG.Models
public import CFSG.Quasithin.Background.A3Structure36BPrime
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma32
public import CFSG.HardMathSupport.Solomon.LocalBalance.PartIInputs
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Interface
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011LabUniq
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs16
public import CFSG.LocalAnalysis.GLTheoremA.S11.InputsCE
public import CFSG.LocalAnalysis.GLTheoremA.S3.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4.Assembly
public import CFSG.LocalAnalysis.GLTheoremA.S4.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4S.Inputs
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasic
public import CFSG.Quasithin.EmptyFaithful.S146zYFacts
public import CFSG.Quasithin.EmptyFaithful.S146zYRes
public import CFSG.Quasithin.H13.NQCoreP134Main
public import CFSG.Quasithin.Vol2.Ch1Sec3E9Inputs

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG CFSG.Open CFSG.Assembly CFSG.LocalAnalysis.RankThreeUC.S15 CFSG.StandardType
open CFSG.Adapters.RankTwoModelTransports

@[expose] noncomputable def rk2Chev (lab : GLALabel) (r z : ℕ) : ℕ :=
  match lab.tag with
  | .A => rkLin (lab.rank + 1) true (2 ^ lab.n) r z
  | .twA => rkLin (lab.rank + 1) false (2 ^ lab.n) r z
  | .B | .C => rkSp lab.rank (2 ^ lab.n) r
  | .D => rkOmPlus lab.rank (2 ^ lab.n) r
  | .twD =>
    if lab.rank = 3 then rkLin 4 false (2 ^ lab.n) r z else rkOmMinus lab.rank (2 ^ lab.n) r
  | .G2 => rkG2 (2 ^ lab.n) r
  | _ => 0

theorem rk2_markedModel_of_isLabel {K : Type} [Group K] {lab : GLALabel}
    (hK : Rk2IsLabel K lab) :
    LargeEvenInLambda2 lab ∧ ∃ (R : Type) (_ : Group R),
      IsSimpleGroup R ∧ Nonempty (K ⧸ Subgroup.center K ≃* R) ∧ MarkedModel lab R := by
  change CFSG.Assembly.LargeEvenMarking K (fun lab' _ _ _ _ _ => lab' = lab) at hK
  unfold CFSG.Assembly.LargeEvenMarking at hK
  obtain ⟨-, lab', hlab', hraw⟩ := hK
  have hna : ∀ (R : Type) [Group R] (I F : Set (MulAut R)),
      IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
        (∃ θ : K ⧸ Subgroup.center K ≃* R, lab' = lab) →
      ∃ a b : R, a * b ≠ b * a := by
    intro R _ I F h
    exact h.2.1
  have hraw' := CFSG.StandardType.Canonical.largeEvenRawDatum_markedModel hlab' hna hraw
  obtain ⟨R, hgroup, I, F, hQ⟩ := CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw'
  letI : Group R := hgroup
  obtain ⟨⟨hsimple, -, θ, hlab'⟩, hM⟩ := hQ
  subst lab'
  exact ⟨hlab', R, hgroup, hsimple, ⟨θ⟩, hM⟩


private theorem prime_not_dvd_four {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) : ¬ r ∣ 4 := by
  intro h
  have h2 : r ∣ 2 := by
    have h' : r ∣ 2 ^ 2 := by simpa using h
    exact hr.dvd_of_dvd_pow h'
  exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h2)

theorem rkLin_four_true_eq_rkOmPlus_three (n r z : ℕ) (hr : r.Prime) (hr2 : r ≠ 2) :
    rkLin 4 true (2 ^ n) r z = rkOmPlus 3 (2 ^ n) r := by
  unfold rkLin rkOmPlus eP eS
  haveI : Fact r.Prime := ⟨hr⟩
  have h2 : (2 : ZMod r) ≠ 0 := by
    intro hc
    have h' : ((2 : ℕ) : ZMod r) = 0 := by exact_mod_cast hc
    rw [ZMod.natCast_eq_zero_iff] at h'
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 h')
  have heP : 0 < orderOf ((2 : ZMod r) ^ n) := by
    rw [orderOf_pos_iff, isOfFinOrder_iff_pow_eq_one]
    exact ⟨r - 1, by have := hr.two_le; omega, ZMod.pow_card_sub_one_eq_one (pow_ne_zero n h2)⟩
  rw [show (((2 ^ n : ℕ) : ZMod r)) = (2 : ZMod r) ^ n by push_cast; rfl] at *
  set ep := orderOf ((2 : ZMod r) ^ n) with hep
  have hes : orderOf (((2 : ZMod r) ^ n) ^ 2) = ep / ep.gcd 2 := by
    rw [hep, orderOf_pow' _ (by norm_num : 2 ≠ 0)]
  rw [hes] at *
  have hr4 : ¬ r ∣ 4 := prime_not_dvd_four hr hr2
  by_cases h6 : ep ≤ 6
  · interval_cases ep <;> norm_num [hr4]
  · have hgt : 6 < ep := by omega
    have hnotdvd : ¬ ep ∣ 2 * 3 := by
      intro hd
      have := Nat.le_of_dvd (by norm_num) hd
      omega
    have hnotdvd3 : ¬ ep ∣ 3 := by
      intro hd
      have := Nat.le_of_dvd (by norm_num) hd
      omega
    have hE : 3 < ep / ep.gcd 2 := by
      rcases Nat.even_or_odd ep with hev | hodd
      · obtain ⟨k, hek⟩ := hev
        rw [hek]
        have hg : (k + k).gcd 2 = 2 := Nat.gcd_eq_right ⟨k, by omega⟩
        rw [hg]
        omega
      · rw [(Nat.coprime_two_right.mpr hodd).gcd_eq_one]
        omega
    have hne1 : ep ≠ 1 := by omega
    have hnotdvd' : ¬ (ep ∣ 2 * 3 ∧ ¬ ep ∣ 3) := by
      rintro ⟨hd, -⟩
      exact hnotdvd hd
    simp only [if_true]
    rw [if_neg hne1, if_neg hnotdvd',
      Nat.div_eq_of_lt (by omega : 4 < ep), Nat.div_eq_of_lt hE]

theorem rkLin_two_true_eq_rkOmMinus_two (n r z : ℕ) (hr : r.Prime) (hr2 : r ≠ 2) :
    rkLin 2 true (2 ^ (2 * n)) r z = rkOmMinus 2 (2 ^ n) r := by
  unfold rkLin rkOmMinus eP eS
  haveI : Fact r.Prime := ⟨hr⟩
  have h2 : (2 : ZMod r) ≠ 0 := by
    intro hc
    have h' : ((2 : ℕ) : ZMod r) = 0 := by exact_mod_cast hc
    rw [ZMod.natCast_eq_zero_iff] at h'
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 h')
  have hep : 0 < orderOf ((2 : ZMod r) ^ n) := by
    rw [orderOf_pos_iff, isOfFinOrder_iff_pow_eq_one]
    exact ⟨r - 1, by have := hr.two_le; omega, ZMod.pow_card_sub_one_eq_one (pow_ne_zero n h2)⟩
  have hpow : (((2 ^ (2 * n) : ℕ) : ZMod r)) = (((2 ^ n : ℕ) : ZMod r)) ^ 2 := by
    push_cast
    rw [← pow_mul]
    congr 1
    omega
  rw [hpow] at *
  rw [show (((2 ^ n : ℕ) : ZMod r)) = (2 : ZMod r) ^ n by push_cast; rfl] at *
  set ep := orderOf ((2 : ZMod r) ^ n) with hepdef
  have hes : orderOf (((2 : ZMod r) ^ n) ^ 2) = ep / ep.gcd 2 := by
    rw [hepdef, orderOf_pow' _ (by norm_num : 2 ≠ 0)]
  rw [hes] at *
  by_cases h : ep / ep.gcd 2 = 1
  · have hep_dvd_two : ep ∣ 2 := by
      have hgpos : 0 < ep.gcd 2 := Nat.gcd_pos_of_pos_left 2 hep
      have heq : ep = 1 * (ep.gcd 2) :=
        (Nat.div_eq_iff_eq_mul_left hgpos (Nat.gcd_dvd_left ep 2)).mp h
      rw [heq]
      simpa using Nat.gcd_dvd_right ep 2
    simp only [if_true]
    rw [if_pos h, if_pos hep_dvd_two, h]
    norm_num
  · have hnot : ¬ ep ∣ 2 := by
      intro hd
      have hcases : ep = 1 ∨ ep = 2 := by
        rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h2
        · exact Or.inl h1
        · exact Or.inr h2
      rcases hcases with h1 | h1
      · rw [h1] at h
        norm_num at h
      · rw [h1] at h
        norm_num at h
    simp only [if_true]
    rw [if_neg h, if_neg hnot, Nat.sub_zero]


private theorem two_pow_eq_two_iff {n : ℕ} : 2 ^ n = 2 ↔ n = 1 := by
  constructor
  · intro h
    exact Nat.pow_right_injective (by norm_num : 1 < 2) (h.trans (pow_one 2).symm)
  · rintro rfl; norm_num

private theorem two_pow_eq_four_iff {n : ℕ} : 2 ^ n = 4 ↔ n = 2 := by
  constructor
  · intro h
    exact Nat.pow_right_injective (by norm_num : 1 < 2) (h.trans (by norm_num : 4 = 2 ^ 2).symm)
  · rintro rfl; norm_num

private theorem two_pow_ne_five {n : ℕ} (hn : 1 ≤ n) : 2 ^ n ≠ 5 := by
  intro h
  have he : Even (2 ^ n) := Even.pow_of_ne_zero even_two (by omega : n ≠ 0)
  obtain ⟨k, hk⟩ := he
  omega

private theorem two_pow_ne_nine {n : ℕ} (hn : 1 ≤ n) : 2 ^ n ≠ 9 := by
  intro h
  have he : Even (2 ^ n) := Even.pow_of_ne_zero even_two (by omega : n ≠ 0)
  obtain ⟨k, hk⟩ := he
  omega

private theorem nonempty_lie_equiv_of_fixedField_model
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {H : (K : Type) → [Field K] → Subgroup (GL ι K)}
    (hH : ∀ {K L : Type} [Field K] [Field L] (φ : K ≃+* L),
      (H K).map (glCongr φ).toMonoidHom = H L)
    {G : Type} [Group G] (d : TauCeti.ValidLieTypeIndex)
    (eT : d.Group ≃* StatedProj (H ↥d.fixedField))
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = d.fieldOrder)
    (θ : G ≃* StatedProj (H K)) :
    Nonempty (G ≃* d.Group) := by
  obtain ⟨φ⟩ := CFSG.ClassicalModels.nonempty_ringEquiv_validIndex_fixedField d K hK
  exact ⟨(θ.trans (statedProjCongr (glCongr φ) (hH φ) (glCongr_statedScalars φ))).trans eT.symm⟩

theorem rk2_index_A {K : Type} [Group K] [Finite K] {lab : GLALabel}
    (hK : Rk2IsLabel K lab) (htag : lab.tag = .A)
    (hA1 : lab.rank = 1 → 3 ≤ lab.n) (hA2 : lab.rank = 2 → 2 ≤ lab.n)
    (hA3 : lab.rank = 3 → 2 ≤ lab.n) :
    ∃ d : TauCeti.ValidLieTypeIndex, CFSG.AGLEmbedding.IsClassicalOrG2Index d.1 ∧
      Nonempty ((K ⧸ Subgroup.center K) ≃* (TauCeti.CFSGIndex.lie d).Group) ∧
      ∀ r z, r.Prime → r ≠ 2 → mRankChev d.1 r z = rk2Chev lab r z := by
  obtain ⟨hlab, R, hgroup, -, ⟨θ⟩, hM⟩ := rk2_markedModel_of_isLabel hK
  letI : Group R := hgroup
  simp only [CFSG.Assembly.LargeEvenInLambda2, htag] at hlab
  obtain ⟨hn1, hr1, hr1n⟩ := hlab
  have ht : CFSG.StandardType.markTag lab = .PSL := by
    simp [CFSG.StandardType.markTag, htag]
  have hr : CFSG.StandardType.markRank lab = lab.rank + 1 := by
    simp [CFSG.StandardType.markRank, htag]
  have hc : CFSG.StandardType.markChar lab = 2 := by
    simp [CFSG.StandardType.markChar, htag]
  have hd : CFSG.StandardType.markDeg lab = lab.n := by
    simp [CFSG.StandardType.markDeg, htag]
  have hM' := hM
  unfold CFSG.StandardType.MarkedModel at hM'
  rw [ht, hr, hc, hd] at hM'
  obtain ⟨-, F, hfield, hfinite, hcard, ⟨e⟩⟩ := hM'.statedClassicalModel (by decide)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let q : TauCeti.PrimePower := ⟨2, lab.n, Nat.prime_two, by omega⟩
  have hv : (TauCeti.LieTypeIndex.A lab.rank q).Valid := by
    rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
      TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
    simp only [q, TauCeti.PrimePower.card_def]
    refine ⟨⟨hr1, ?_⟩, ?_⟩
    · intro hrk
      have := hA1 hrk
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ lab.n := Nat.pow_le_pow_right (by norm_num) (by omega)
    rintro (⟨hrk, h4 | h5 | h9⟩ | ⟨hrk, h2⟩ | ⟨hrk, h2'⟩)
    · have hn2 : lab.n = 2 := by
        by_contra hn
        rw [two_pow_eq_four_iff] at h4
        omega
      exact absurd hn2 (by omega)
    · exact (two_pow_ne_five (by omega)) h5
    · exact (two_pow_ne_nine (by omega)) h9
    · have hn1' : lab.n = 1 := two_pow_eq_two_iff.mp h2
      omega
    · have hn1' : lab.n = 1 := two_pow_eq_two_iff.mp h2'
      omega
  have e1 := CFSG.ClassicalModels.statedLinearModelEquivGaloisPSL F (lab.rank + 1) 2 lab.n
    (by omega) hcard
  have e2 := (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL lab.rank q hv).symm
  refine ⟨⟨.A lab.rank q, hv⟩, ?_, ⟨(θ.trans e).trans (e1.trans e2)⟩, ?_⟩
  · simp [CFSG.AGLEmbedding.IsClassicalOrG2Index, q]
  · intro r z hr hr2
    simp [mRankChev, rk2Chev, htag, q, TauCeti.PrimePower.card_def]


theorem rk2_index_BC {K : Type} [Group K] [Finite K] {lab : GLALabel}
    (hK : Rk2IsLabel K lab) (htag : lab.tag = .B ∨ lab.tag = .C) :
    ∃ d : TauCeti.ValidLieTypeIndex, CFSG.AGLEmbedding.IsClassicalOrG2Index d.1 ∧
      Nonempty ((K ⧸ Subgroup.center K) ≃* (TauCeti.CFSGIndex.lie d).Group) ∧
      ∀ r z, r.Prime → r ≠ 2 → mRankChev d.1 r z = rk2Chev lab r z := by
  obtain ⟨hlab, R, hgroup, -, ⟨θ⟩, hM⟩ := rk2_markedModel_of_isLabel hK
  letI : Group R := hgroup
  have ht : CFSG.StandardType.markTag lab = .PSp := by
    rcases htag with hB | hC
    · simp [CFSG.StandardType.markTag, hB]
    · simp [CFSG.StandardType.markTag, hC]
  have hr : CFSG.StandardType.markRank lab = lab.rank := by
    rcases htag with hB | hC
    · simp [CFSG.StandardType.markRank, hB]
    · simp [CFSG.StandardType.markRank, hC]
  have hc : CFSG.StandardType.markChar lab = 2 := by
    rcases htag with hB | hC
    · simp [CFSG.StandardType.markChar, hB]
    · simp [CFSG.StandardType.markChar, hC]
  have hd : CFSG.StandardType.markDeg lab = lab.n := by
    rcases htag with hB | hC
    · simp [CFSG.StandardType.markDeg, hB]
    · simp [CFSG.StandardType.markDeg, hC]
  have hM' := hM
  unfold CFSG.StandardType.MarkedModel at hM'
  rw [ht, hr, hc, hd] at hM'
  obtain ⟨hadm, F, hfield, hfinite, hcard, ⟨e⟩⟩ := hM'.statedClassicalModel (by decide)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let q : TauCeti.PrimePower := ⟨2, lab.n, Nat.prime_two, by have := hadm.2.1; omega⟩
  have hv : (TauCeti.LieTypeIndex.B lab.rank q).Valid := by
    rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
      TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
    simp only [q, TauCeti.PrimePower.card_def]
    refine ⟨⟨hadm.2.2.1, ?_⟩, ?_⟩
    · rintro ⟨hrk, hq⟩
      exact hadm.2.2.2 (Prod.ext hrk (by simpa [q, TauCeti.PrimePower.card_def] using hq))
    · rintro ⟨-, hq⟩
      exact CFSG.StandardType.two_pow_ne_three lab.n hq
  let d : TauCeti.ValidLieTypeIndex := ⟨.B lab.rank q, hv⟩
  have hcardd : Nat.card F = d.fieldOrder := by
    rw [show d.fieldOrder = 2 ^ lab.n by
      simp [d, q, TauCeti.ValidLieTypeIndex.fieldOrder, TauCeti.LieTypeIndex.fieldOrder_B]]
    exact hcard
  have θ' : K ⧸ Subgroup.center K ≃* StatedProj (StatedSp lab.rank F) := θ.trans e
  have hmain : Nonempty (K ⧸ Subgroup.center K ≃* d.Group) := by
    rcases Nat.lt_or_ge 2 lab.rank with hlt | hle
    · have hr3 : 3 ≤ lab.rank := hlt
      exact nonempty_lie_equiv_of_fixedField_model
        (H := fun L _ => StatedSp lab.rank L)
        (hH := fun φ => glCongr_statedSp (φ := φ) lab.rank)
        d (CFSG.RankThree.PartTwo.Census.Carrier.SpinB.typeBGroupEquivStatedProj
          lab.rank q hv rfl hr3) hcardd θ'
    · have hr2 : lab.rank = 2 := le_antisymm hle hadm.2.2.1
      rw [hr2] at hv θ'
      have hd : d = ⟨.B 2 q, hv⟩ := by
        ext
        simp [d, hr2]
      have hcardd' : Nat.card F = TauCeti.ValidLieTypeIndex.fieldOrder ⟨.B 2 q, hv⟩ := by
        rw [← hd]
        exact hcardd
      have hres := nonempty_lie_equiv_of_fixedField_model
        (H := fun L _ => StatedSp 2 L) (hH := fun φ => glCongr_statedSp (φ := φ) 2)
        ⟨.B 2 q, hv⟩ (CFSG.QuasithinUnique.SQTK.typeB2GroupEquivStatedProj q hv)
        hcardd' θ'
      rw [hd]
      exact hres
  refine ⟨d, ?_, hmain, ?_⟩
  · rcases htag with hB | hC
    · simp [CFSG.AGLEmbedding.IsClassicalOrG2Index, d, q, hB]
    · simp [CFSG.AGLEmbedding.IsClassicalOrG2Index, d, q, hC]
  · intro r z hr hr2
    rcases htag with hB | hC
    · simp [mRankChev, rk2Chev, d, q, hB, TauCeti.PrimePower.card_def]
    · simp [mRankChev, rk2Chev, d, q, hC, TauCeti.PrimePower.card_def]


theorem rk2_index_twA {K : Type} [Group K] [Finite K] {lab : GLALabel}
    (hK : Rk2IsLabel K lab) (htag : lab.tag = .twA) :
    ∃ d : TauCeti.ValidLieTypeIndex, CFSG.AGLEmbedding.IsClassicalOrG2Index d.1 ∧
      Nonempty ((K ⧸ Subgroup.center K) ≃* (TauCeti.CFSGIndex.lie d).Group) ∧
      ∀ r z, r.Prime → r ≠ 2 → mRankChev d.1 r z = rk2Chev lab r z := by
  obtain ⟨hlab, R, hgroup, -, ⟨θ⟩, hM⟩ := rk2_markedModel_of_isLabel hK
  letI : Group R := hgroup
  have ht : CFSG.StandardType.markTag lab = .PSU := by
    simp [CFSG.StandardType.markTag, htag]
  have hr : CFSG.StandardType.markRank lab = lab.rank + 1 := by
    simp [CFSG.StandardType.markRank, htag]
  have hc : CFSG.StandardType.markChar lab = 2 := by
    simp [CFSG.StandardType.markChar, htag]
  have hd : CFSG.StandardType.markDeg lab = lab.n := by
    simp [CFSG.StandardType.markDeg, htag]
  have hM' := hM
  unfold CFSG.StandardType.MarkedModel at hM'
  rw [ht, hr, hc, hd] at hM'
  obtain ⟨hadm, F, hfield, hfinite, hcard, ⟨e⟩⟩ := hM'.statedClassicalModel (by decide)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let q : TauCeti.PrimePower := ⟨2, lab.n, hadm.1, by have := hadm.2.1; omega⟩
  have hv : (TauCeti.LieTypeIndex.twistedA lab.rank q).Valid := by
    have h := CFSG.ClassicalModels.unitaryCatalog_index_valid (lab.rank + 1) 2 lab.n hadm
    simpa [q, Nat.add_sub_cancel] using h
  let d : TauCeti.ValidLieTypeIndex := ⟨.twistedA lab.rank q, hv⟩
  have hc2 : TauCeti.ValidLieTypeIndex.characteristic d = 2 := by
    change (TauCeti.LieTypeIndex.twistedA lab.rank q).characteristic = 2
    simp [q]
  have hf2 : TauCeti.ValidLieTypeIndex.fieldExponent d = lab.n := by
    change (TauCeti.LieTypeIndex.twistedA lab.rank q).fieldExponent = lab.n
    simp [q]
  let L := GaloisField d.characteristic (2 * d.fieldExponent)
  let _ : Fintype F := Fintype.ofFinite F
  let _ : Fintype L := Fintype.ofFinite L
  have hcardNat : Nat.card F = Nat.card L := by
    rw [hcard]
    rw [show L = GaloisField 2 (2 * lab.n) by simp [L, hc2, hf2]]
    rw [GaloisField.card 2 (2 * lab.n) (by have := hadm.2.1; omega)]
    rw [← pow_mul]
    congr 1
    omega
  have hcardL : Fintype.card F = Fintype.card L := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    exact hcardNat
  let φ : F ≃+* L := FiniteField.ringEquivOfCardEq hcardL
  have hS : 2 ^ lab.n = d.characteristic ^ d.fieldExponent := by rw [hc2, hf2]
  have e' : R ≃* StatedProj
      (StatedSU (lab.rank + 1) (d.characteristic ^ d.fieldExponent) F) := by
    rw [← hS]
    exact e
  let e1 := statedProjCongr (glCongr (ι := Fin (lab.rank + 1)) φ)
    (glCongr_statedSU φ (lab.rank + 1) (d.characteristic ^ d.fieldExponent))
    (glCongr_statedScalars φ)
  let eT := CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj lab.rank q hv
  refine ⟨d, ?_, ⟨(θ.trans e').trans (e1.trans eT.symm)⟩, ?_⟩
  · have hd1 : (d : TauCeti.ValidLieTypeIndex).1 = .twistedA lab.rank q := rfl
    rw [hd1]
    simp [CFSG.AGLEmbedding.IsClassicalOrG2Index, q]
  · intro r z hr hr2
    have hd1 : (d : TauCeti.ValidLieTypeIndex).1 = .twistedA lab.rank q := rfl
    rw [hd1]
    simp [mRankChev, rk2Chev, htag, q, TauCeti.PrimePower.card_def]





theorem rk2_index_D {K : Type} [Group K] [Finite K] {lab : GLALabel}
    (hK : Rk2IsLabel K lab) (htag : lab.tag = .D) (hD3 : lab.rank = 3 → 2 ≤ lab.n) :
    ∃ d : TauCeti.ValidLieTypeIndex, CFSG.AGLEmbedding.IsClassicalOrG2Index d.1 ∧
      Nonempty ((K ⧸ Subgroup.center K) ≃* (TauCeti.CFSGIndex.lie d).Group) ∧
      ∀ r z, r.Prime → r ≠ 2 → mRankChev d.1 r z = rk2Chev lab r z := by
  obtain ⟨hlab, R, hgroup, -, ⟨θ⟩, hM⟩ := rk2_markedModel_of_isLabel hK
  letI : Group R := hgroup
  simp only [CFSG.Assembly.LargeEvenInLambda2, htag] at hlab
  by_cases hr3 : lab.rank = 3
  · have ht : CFSG.StandardType.markTag lab = .PSL := by
      simp [CFSG.StandardType.markTag, htag, hr3]
    have hr : CFSG.StandardType.markRank lab = 4 := by
      simp [CFSG.StandardType.markRank, htag, hr3]
    have hc : CFSG.StandardType.markChar lab = 2 := by
      simp [CFSG.StandardType.markChar, htag]
    have hd : CFSG.StandardType.markDeg lab = lab.n := by
      simp [CFSG.StandardType.markDeg, htag]
    have hM' := hM
    unfold CFSG.StandardType.MarkedModel at hM'
    rw [ht, hr, hc, hd] at hM'
    obtain ⟨-, F, hfield, hfinite, hcard, ⟨e⟩⟩ := hM'.statedClassicalModel (by decide)
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    let q : TauCeti.PrimePower := ⟨2, lab.n, Nat.prime_two, by omega⟩
    have hv : (TauCeti.LieTypeIndex.A 3 q).Valid := by
      rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
        TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
      simp only [q, TauCeti.PrimePower.card_def]
      refine ⟨⟨by norm_num, by norm_num⟩, ?_⟩
      rintro (⟨h1, -⟩ | ⟨h2, -⟩ | ⟨h3, hq⟩)
      · omega
      · omega
      · have hn1 : lab.n = 1 := two_pow_eq_two_iff.mp hq
        omega
    have e1 := CFSG.ClassicalModels.statedLinearModelEquivGaloisPSL F 4 2 lab.n
      (by omega) hcard
    have e2 := (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 3 q hv).symm
    refine ⟨⟨.A 3 q, hv⟩, ?_, ⟨(θ.trans e).trans (e1.trans e2)⟩, ?_⟩
    · simp [CFSG.AGLEmbedding.IsClassicalOrG2Index, q]
    · intro r z hrp hr2
      rw [show rk2Chev lab r z = rkOmPlus 3 (2 ^ lab.n) r by
        simp [rk2Chev, htag, hr3]]
      rw [show mRankChev (TauCeti.LieTypeIndex.A 3 q) r z = rkLin 4 true (2 ^ lab.n) r z by
        simp [mRankChev, q, TauCeti.PrimePower.card_def]]
      exact rkLin_four_true_eq_rkOmPlus_three lab.n r z hrp hr2
  · have hr4 : 4 ≤ lab.rank := by
      have := hlab
      omega
    have ht : CFSG.StandardType.markTag lab = .POmegaPlus := by
      simp [CFSG.StandardType.markTag, htag, if_neg hr3]
    have hr : CFSG.StandardType.markRank lab = lab.rank := by
      simp [CFSG.StandardType.markRank, htag, if_neg hr3]
    have hc : CFSG.StandardType.markChar lab = 2 := by
      simp [CFSG.StandardType.markChar, htag]
    have hd : CFSG.StandardType.markDeg lab = lab.n := by
      simp [CFSG.StandardType.markDeg, htag]
    have hM' := hM
    unfold CFSG.StandardType.MarkedModel at hM'
    rw [ht, hr, hc, hd] at hM'
    obtain ⟨hadm, F, hfield, hfinite, hcard, ⟨e⟩⟩ := hM'.statedClassicalModel (by decide)
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    let q : TauCeti.PrimePower := ⟨2, lab.n, Nat.prime_two, by omega⟩
    have hv : (TauCeti.LieTypeIndex.D lab.rank q).Valid := by
      rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
        TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
      exact ⟨hr4, not_false⟩
    let d : TauCeti.ValidLieTypeIndex := ⟨.D lab.rank q, hv⟩
    have hcardd : Nat.card F = d.fieldOrder := by
      rw [show d.fieldOrder = 2 ^ lab.n by
        simp [d, q, TauCeti.ValidLieTypeIndex.fieldOrder, TauCeti.LieTypeIndex.fieldOrder_D]]
      exact hcard
    have θ' : K ⧸ Subgroup.center K ≃*
        StatedProj (StatedOmega (StatedQuadPlus lab.rank F)) := θ.trans e
    have hmain : Nonempty (K ⧸ Subgroup.center K ≃* d.Group) :=
      nonempty_lie_equiv_of_fixedField_model
        (H := fun L _ => StatedOmega (StatedQuadPlus lab.rank L))
        (hH := fun φ => CFSG.ClassicalInvolution.Upgrade.map_statedOmega φ
          (CFSG.ClassicalInvolution.Upgrade.statedQuadPlus_comp φ))
        d (CFSG.RankThree.PartTwo.Census.Carrier.SpinD.typeDGroupEquivStatedProj_of_valid
          lab.rank q hv) hcardd θ'
    refine ⟨d, ?_, hmain, ?_⟩
    · have hd1 : (d : TauCeti.ValidLieTypeIndex).1 = .D lab.rank q := rfl
      rw [hd1]
      simp [CFSG.AGLEmbedding.IsClassicalOrG2Index, q]
    · intro r z hrp hr2
      have hd1 : (d : TauCeti.ValidLieTypeIndex).1 = .D lab.rank q := rfl
      rw [hd1]
      simp [mRankChev, rk2Chev, htag, hr3, q, TauCeti.PrimePower.card_def]


theorem rk2_index_twD {K : Type} [Group K] [Finite K] {lab : GLALabel}
    (hK : Rk2IsLabel K lab) (htag : lab.tag = .twD) (hTD2 : lab.rank = 2 → 2 ≤ lab.n) :
    ∃ d : TauCeti.ValidLieTypeIndex, CFSG.AGLEmbedding.IsClassicalOrG2Index d.1 ∧
      Nonempty ((K ⧸ Subgroup.center K) ≃* (TauCeti.CFSGIndex.lie d).Group) ∧
      ∀ r z, r.Prime → r ≠ 2 → mRankChev d.1 r z = rk2Chev lab r z := by
  obtain ⟨hlab, R, hgroup, -, ⟨θ⟩, hM⟩ := rk2_markedModel_of_isLabel hK
  letI : Group R := hgroup
  simp only [CFSG.Assembly.LargeEvenInLambda2, htag] at hlab
  by_cases hr2 : lab.rank = 2
  · have ht : CFSG.StandardType.markTag lab = .PSL := by
      simp [CFSG.StandardType.markTag, htag, hr2]
    have hr : CFSG.StandardType.markRank lab = 2 := by
      simp [CFSG.StandardType.markRank, htag, hr2]
    have hc : CFSG.StandardType.markChar lab = 2 := by
      simp [CFSG.StandardType.markChar, htag]
    have hd : CFSG.StandardType.markDeg lab = 2 * lab.n := by
      simp [CFSG.StandardType.markDeg, htag, hr2]
    have hM' := hM
    unfold CFSG.StandardType.MarkedModel at hM'
    rw [ht, hr, hc, hd] at hM'
    obtain ⟨-, F, hfield, hfinite, hcard, ⟨e⟩⟩ := hM'.statedClassicalModel (by decide)
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    let q : TauCeti.PrimePower := ⟨2, 2 * lab.n, Nat.prime_two, by omega⟩
    have hv : (TauCeti.LieTypeIndex.A 1 q).Valid := by
      rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
        TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
      simp only [q, TauCeti.PrimePower.card_def]
      refine ⟨⟨by norm_num, ?_⟩, ?_⟩
      · intro _
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (2 * lab.n) := Nat.pow_le_pow_right (by norm_num) (by omega)
      rintro (⟨h1, h4 | h5 | h9⟩ | ⟨h2, -⟩ | ⟨h3, -⟩)
      · have h2n : 2 * lab.n = 2 := two_pow_eq_four_iff.mp h4
        omega
      · exact (two_pow_ne_five (by omega)) h5
      · exact (two_pow_ne_nine (by omega)) h9
      · omega
      · omega
    have e1 := CFSG.ClassicalModels.statedLinearModelEquivGaloisPSL F 2 2 (2 * lab.n)
      (by omega) hcard
    have e2 := (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 q hv).symm
    refine ⟨⟨.A 1 q, hv⟩, ?_, ⟨(θ.trans e).trans (e1.trans e2)⟩, ?_⟩
    · simp [CFSG.AGLEmbedding.IsClassicalOrG2Index, q]
    · intro r z hrp hr2'
      rw [show rk2Chev lab r z = rkOmMinus 2 (2 ^ lab.n) r by
        simp [rk2Chev, htag, hr2]]
      rw [show mRankChev (TauCeti.LieTypeIndex.A 1 q) r z = rkLin 2 true (2 ^ (2 * lab.n)) r z by
        simp [mRankChev, q, TauCeti.PrimePower.card_def]]
      exact rkLin_two_true_eq_rkOmMinus_two lab.n r z hrp hr2'
  · by_cases hr3 : lab.rank = 3
    · have ht : CFSG.StandardType.markTag lab = .PSU := by
        simp [CFSG.StandardType.markTag, htag, if_neg hr2, hr3]
      have hr : CFSG.StandardType.markRank lab = 4 := by
        simp [CFSG.StandardType.markRank, htag, if_neg hr2, hr3]
      have hc : CFSG.StandardType.markChar lab = 2 := by
        simp [CFSG.StandardType.markChar, htag]
      have hd : CFSG.StandardType.markDeg lab = lab.n := by
        simp [CFSG.StandardType.markDeg, htag, if_neg hr2]
      have hM' := hM
      unfold CFSG.StandardType.MarkedModel at hM'
      rw [ht, hr, hc, hd] at hM'
      obtain ⟨hadm, F, hfield, hfinite, hcard, ⟨e⟩⟩ := hM'.statedClassicalModel (by decide)
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      let q : TauCeti.PrimePower := ⟨2, lab.n, hadm.1, by have := hadm.2.1; omega⟩
      have hv : (TauCeti.LieTypeIndex.twistedA 3 q).Valid := by
        have h := CFSG.ClassicalModels.unitaryCatalog_index_valid 4 2 lab.n hadm
        simpa [q] using h
      let d : TauCeti.ValidLieTypeIndex := ⟨.twistedA 3 q, hv⟩
      have hc2 : TauCeti.ValidLieTypeIndex.characteristic d = 2 := by
        change (TauCeti.LieTypeIndex.twistedA 3 q).characteristic = 2
        simp [q]
      have hf2 : TauCeti.ValidLieTypeIndex.fieldExponent d = lab.n := by
        change (TauCeti.LieTypeIndex.twistedA 3 q).fieldExponent = lab.n
        simp [q]
      let L := GaloisField d.characteristic (2 * d.fieldExponent)
      let _ : Fintype F := Fintype.ofFinite F
      let _ : Fintype L := Fintype.ofFinite L
      have hcardNat : Nat.card F = Nat.card L := by
        rw [hcard]
        rw [show L = GaloisField 2 (2 * lab.n) by simp [L, hc2, hf2]]
        rw [GaloisField.card 2 (2 * lab.n) (by have := hadm.2.1; omega)]
        rw [← pow_mul]
        congr 1
        omega
      have hcardL : Fintype.card F = Fintype.card L := by
        rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
        exact hcardNat
      let φ : F ≃+* L := FiniteField.ringEquivOfCardEq hcardL
      have hS : 2 ^ lab.n = d.characteristic ^ d.fieldExponent := by rw [hc2, hf2]
      have e' : R ≃* StatedProj
          (StatedSU 4 (d.characteristic ^ d.fieldExponent) F) := by
        rw [← hS]
        exact e
      let e1 := statedProjCongr (glCongr (ι := Fin 4) φ)
        (glCongr_statedSU φ 4 (d.characteristic ^ d.fieldExponent))
        (glCongr_statedScalars φ)
      let eT := CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj 3 q hv
      refine ⟨d, ?_, ⟨(θ.trans e').trans (e1.trans eT.symm)⟩, ?_⟩
      · have hd1 : (d : TauCeti.ValidLieTypeIndex).1 = .twistedA 3 q := rfl
        rw [hd1]
        simp [CFSG.AGLEmbedding.IsClassicalOrG2Index, q]
      · intro r z hrp hr2'
        have hd1 : (d : TauCeti.ValidLieTypeIndex).1 = .twistedA 3 q := rfl
        rw [hd1]
        simp [mRankChev, rk2Chev, htag, hr2, hr3, q, TauCeti.PrimePower.card_def]
    · have hr4 : 4 ≤ lab.rank := by omega
      have ht : CFSG.StandardType.markTag lab = .POmegaMinus := by
        simp [CFSG.StandardType.markTag, htag, if_neg hr2, if_neg hr3]
      have hr : CFSG.StandardType.markRank lab = lab.rank := by
        simp [CFSG.StandardType.markRank, htag, if_neg hr2, if_neg hr3]
      have hc : CFSG.StandardType.markChar lab = 2 := by
        simp [CFSG.StandardType.markChar, htag]
      have hd : CFSG.StandardType.markDeg lab = lab.n := by
        simp [CFSG.StandardType.markDeg, htag, if_neg hr2]
      have hM' := hM
      unfold CFSG.StandardType.MarkedModel at hM'
      rw [ht, hr, hc, hd] at hM'
      obtain ⟨hadm, F, hfield, hfinite, hcard, b, c, hirr, ⟨e⟩⟩ :=
        hM'.statedClassicalModel (by decide)
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      let q : TauCeti.PrimePower := ⟨2, lab.n, Nat.prime_two, by omega⟩
      have hv : (TauCeti.LieTypeIndex.twistedD lab.rank q).Valid := by
        rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
          TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
        exact ⟨hr4, not_false⟩
      let d : TauCeti.ValidLieTypeIndex := ⟨.twistedD lab.rank q, hv⟩
      have hcardd : Nat.card F = d.fieldOrder := by
        rw [show d.fieldOrder = 2 ^ lab.n by
          simp [d, q, TauCeti.ValidLieTypeIndex.fieldOrder,
            TauCeti.LieTypeIndex.fieldOrder_twistedD]]
        exact hcard
      obtain ⟨b₀, c₀, hirr₀, ⟨eT⟩⟩ :=
        CFSG.RankThree.PartTwo.Census.Carrier.SpinD.exists_typeTwistedDGroupEquivStatedProj_of_valid
          lab.rank q hv
      obtain ⟨φ⟩ := CFSG.ClassicalModels.nonempty_ringEquiv_validIndex_fixedField d F hcardd
      have _ : Finite ↥d.fixedField := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField d
      obtain ⟨e2⟩ := CFSG.Blueprint.EvenSource.nonempty_statedOmegaMinus_equiv
        (n := lab.rank) (by omega) (CFSG.ClassicalInvolution.Upgrade.irreducible_map φ hirr) hirr₀
      let e1 := statedProjCongr (glCongr φ)
        (CFSG.ClassicalInvolution.Upgrade.map_statedOmega φ
          (CFSG.ClassicalInvolution.Upgrade.statedQuadMinus_comp (n := lab.rank)
            (b := b) (c := c) φ rfl rfl))
        (glCongr_statedScalars φ)
      refine ⟨d, ?_, ⟨(θ.trans e).trans ((e1.trans e2).trans eT.symm)⟩, ?_⟩
      · have hd1 : (d : TauCeti.ValidLieTypeIndex).1 = .twistedD lab.rank q := rfl
        rw [hd1]
        simp [CFSG.AGLEmbedding.IsClassicalOrG2Index, q]
      · intro r z hrp hr2'
        have hd1 : (d : TauCeti.ValidLieTypeIndex).1 = .twistedD lab.rank q := rfl
        rw [hd1]
        simp [mRankChev, rk2Chev, htag, hr2, hr3, q, TauCeti.PrimePower.card_def]



theorem rkLin_four_false_le_rk2Mult_twD_three {r n z : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) :
    rkLin 4 false (2 ^ n) r z ≤
      rk2Mult (⟨.twD, 3, n⟩ : GLALabel) (rk2Ord r n) := by
  haveI : Fact r.Prime := ⟨hr⟩
  have hmpos : 0 < rk2Ord r n := rk2Ord_pos hr hr2 n
  have hRHS : rk2Mult (⟨.twD, 3, n⟩ : GLALabel) (rk2Ord r n) =
      (if rk2Ord r n % 2 = 0 then 2 * 3 / rk2Ord r n else 3 / rk2Ord r n) -
        (if rk2Ord r n ∣ 3 then 1 else 0) := by
    simp [rk2Mult]
  have hLHS : rkLin 4 false (2 ^ n) r z =
      if eM (2 ^ n) r = 1 then 3 else 4 / eM (2 ^ n) r := by
    rw [show rkLin 4 false (2 ^ n) r z = (if eM (2 ^ n) r = 1 then
        4 - 1 - (if ¬ r ∣ z ∧ r ∣ 4 ∧ 4 ≤ 4 ∧
          padicValNat r (2 ^ n + 1) ≤ padicValNat r 4 then 1 else 0)
        else 4 / eM (2 ^ n) r) by simp [rkLin]]
    have hr4 : ¬ r ∣ 4 := prime_not_dvd_four hr hr2
    simp [hr4]
  rw [hRHS, hLHS]
  by_cases hm1 : rk2Ord r n = 1
  · have hx : orderOf ((2 : ZMod r) ^ n) = 1 := hm1
    have heM : eM (2 ^ n) r = 2 := by
      rw [eM_two_pow_eq_orderOf]
      simpa using CFSG.LieType.SeitzGeneration.orderOf_neg_of_odd
        (CFSG.LieType.SeitzGeneration.neg_one_ne_one_zmod hr hr2) hx (by norm_num) (by norm_num)
    rw [hm1, heM]; norm_num
  by_cases hm2 : rk2Ord r n = 2
  · have hx : orderOf ((2 : ZMod r) ^ n) = 2 := hm2
    have heM : eM (2 ^ n) r = 1 := by
      rw [eM_two_pow_eq_orderOf]
      simpa using CFSG.LieType.SeitzGeneration.orderOf_neg_of_two_mod_four
        (x := (2 : ZMod r) ^ n) hx (by norm_num)
    rw [hm2, heM]; norm_num
  by_cases hm3 : rk2Ord r n = 3
  · have hx : orderOf ((2 : ZMod r) ^ n) = 3 := hm3
    have heM : eM (2 ^ n) r = 6 := by
      rw [eM_two_pow_eq_orderOf]
      simpa using CFSG.LieType.SeitzGeneration.orderOf_neg_of_odd
        (CFSG.LieType.SeitzGeneration.neg_one_ne_one_zmod hr hr2) hx (by norm_num) (by norm_num)
    rw [hm3, heM]; norm_num
  by_cases hm4 : rk2Ord r n = 4
  · have hx : orderOf ((2 : ZMod r) ^ n) = 4 := hm4
    have heM : eM (2 ^ n) r = 4 := by
      rw [eM_two_pow_eq_orderOf]
      simpa using CFSG.LieType.SeitzGeneration.orderOf_neg_of_four_dvd
        (x := (2 : ZMod r) ^ n) hx (by norm_num) (by norm_num)
    rw [hm4, heM]; norm_num
  by_cases hm6 : rk2Ord r n = 6
  · have hx : orderOf ((2 : ZMod r) ^ n) = 6 := hm6
    have heM : eM (2 ^ n) r = 3 := by
      rw [eM_two_pow_eq_orderOf]
      simpa using CFSG.LieType.SeitzGeneration.orderOf_neg_of_two_mod_four
        (x := (2 : ZMod r) ^ n) hx (by norm_num)
    rw [hm6, heM]; norm_num
  · have hnotdiv3 : ¬ rk2Ord r n ∣ 3 := by
      rintro hd
      have hle : rk2Ord r n ≤ 3 := Nat.le_of_dvd (by norm_num) hd
      interval_cases rk2Ord r n <;> simp_all
    by_cases hodd : rk2Ord r n % 2 = 1
    · have hodd' : Odd (rk2Ord r n) := Nat.odd_iff.mpr hodd
      have heM : eM (2 ^ n) r = 2 * rk2Ord r n := by
        rw [eM_two_pow_eq_orderOf]
        exact CFSG.LieType.SeitzGeneration.orderOf_neg_of_odd
          (CFSG.LieType.SeitzGeneration.neg_one_ne_one_zmod hr hr2) rfl hodd' hmpos.ne'
      have hgt : 4 < eM (2 ^ n) r := by rw [heM]; omega
      rw [if_neg (by omega : ¬ eM (2 ^ n) r = 1),
        Nat.div_eq_of_lt hgt, if_neg (by omega : ¬ rk2Ord r n % 2 = 0), if_neg hnotdiv3]
      omega
    · have h2dvd : 2 ∣ rk2Ord r n := by
        rw [Nat.dvd_iff_mod_eq_zero]
        omega
      by_cases h4mod : rk2Ord r n % 4 = 2
      · have heM : eM (2 ^ n) r = rk2Ord r n / 2 := by
          rw [eM_two_pow_eq_orderOf]
          exact CFSG.LieType.SeitzGeneration.orderOf_neg_of_two_mod_four
            (x := (2 : ZMod r) ^ n) rfl h4mod
        have hgt : 4 < eM (2 ^ n) r := by
          rw [heM]
          omega
        rw [if_neg (by omega : ¬ eM (2 ^ n) r = 1),
          Nat.div_eq_of_lt hgt, if_pos (by omega : rk2Ord r n % 2 = 0), if_neg hnotdiv3]
        omega
      · have h4dvd : 4 ∣ rk2Ord r n := by
          rw [Nat.dvd_iff_mod_eq_zero]
          omega
        have heM : eM (2 ^ n) r = rk2Ord r n := by
          rw [eM_two_pow_eq_orderOf]
          exact CFSG.LieType.SeitzGeneration.orderOf_neg_of_four_dvd
            (x := (2 : ZMod r) ^ n) rfl h4dvd hmpos.ne'
        have hgt : 4 < eM (2 ^ n) r := by rw [heM]; omega
        rw [if_neg (by omega : ¬ eM (2 ^ n) r = 1),
          Nat.div_eq_of_lt hgt, if_pos (by omega : rk2Ord r n % 2 = 0), if_neg hnotdiv3]
        omega


theorem rk2_isQuasisimple_of_isLabel {K : Type} [Group K] {lab : GLALabel}
    (hK : Rk2IsLabel K lab) :
    CFSG.Open.IsQuasisimple K := by
  obtain ⟨-, R, hgroup, hsimple, ⟨θ⟩, -⟩ := rk2_markedModel_of_isLabel hK
  letI : Group R := hgroup
  have hcomm : commutator K = ⊤ := by
    have h := hK
    change CFSG.Assembly.LargeEvenMarking K (fun lab' _ _ _ _ _ => lab' = lab) at h
    exact h.1
  exact ⟨hcomm, (MulEquiv.isSimpleGroup_congr θ).mpr hsimple⟩

private lemma rk2Ord_three_two : rk2Ord 3 2 = 1 :=
  rk2Ord_eq_one_iff.mpr (by norm_num)

private lemma rk2Ord_five_two : rk2Ord 5 2 = 2 :=
  (rk2Ord_eq_two_iff (by norm_num) (by norm_num)).mpr (by norm_num)

private theorem rk2KRank_A_one_two {K : Type} [Group K] [Finite K]
    (hK : Rk2IsLabel K ⟨.A, 1, 2⟩) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    CFSG.Open.pRank p (⊤ : Subgroup K) ≤
      rk2Mult (⟨.A, 1, 2⟩ : GLALabel) (rk2Ord p 2) := by
  obtain ⟨-, R, hgroup, -, ⟨θ⟩, hM⟩ := rk2_markedModel_of_isLabel hK
  letI : Group R := hgroup
  have hM' : CFSG.Blueprint.LieModel R .PSL 2 2 2 := by
    have h := hM
    unfold CFSG.StandardType.MarkedModel at h
    simpa [CFSG.StandardType.markTag, CFSG.StandardType.markRank,
      CFSG.StandardType.markChar, CFSG.StandardType.markDeg] using h
  obtain ⟨e5⟩ := CFSG.LocalAnalysis.ComponentInitial.PSL2_four_alternating_five_model R hM'
  have hQ := rk2_isQuasisimple_of_isLabel hK
  have hpr := CFSG.LocalAnalysis.RankThreeUC.S15.lieOddRankAlt_holds (K := K) hQ 5 (by norm_num)
    ⟨θ.trans e5⟩ p hp hp2
  rw [hpr]
  by_cases hp5 : p ≤ 5
  · have hp35 : p = 3 ∨ p = 5 := by
      interval_cases p <;> (try norm_num at hp; try norm_num at hp2; try norm_num)
    rcases hp35 with rfl | rfl
    · rw [rk2Ord_three_two]; norm_num [rk2Mult]
    · rw [rk2Ord_five_two]; norm_num [rk2Mult]
  · rw [Nat.div_eq_of_lt (by omega : 5 < p)]
    exact Nat.zero_le _


private theorem pRank_le_rk2Mult_of_alt {K : Type} [Group K] [Finite K] {lab : GLALabel}
    (hQ : CFSG.Open.IsQuasisimple K) (m : ℕ) (hm : 5 ≤ m)
    (e : Nonempty (K ⧸ Subgroup.center K ≃* alternatingGroup (Fin m)))
    (hbound : ∀ p, p.Prime → p ≠ 2 → m / p ≤ rk2Mult lab (rk2Ord p lab.n))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    CFSG.Open.pRank p (⊤ : Subgroup K) ≤ rk2Mult lab (rk2Ord p lab.n) := by
  have hpr := CFSG.LocalAnalysis.RankThreeUC.S15.lieOddRankAlt_holds (K := K) hQ m hm e p hp hp2
  rw [hpr]
  exact hbound p hp hp2

private theorem rk2KRank_A_three_one {K : Type} [Group K] [Finite K]
    (hK : Rk2IsLabel K ⟨.A, 3, 1⟩) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    CFSG.Open.pRank p (⊤ : Subgroup K) ≤
      rk2Mult (⟨.A, 3, 1⟩ : GLALabel) (rk2Ord p 1) := by
  obtain ⟨-, R, hgroup, -, ⟨θ⟩, hM⟩ := rk2_markedModel_of_isLabel hK
  letI : Group R := hgroup
  have hM' : CFSG.Blueprint.LieModel R .PSL 4 2 1 := by
    have h := hM
    unfold CFSG.StandardType.MarkedModel at h
    simpa [CFSG.StandardType.markTag, CFSG.StandardType.markRank,
      CFSG.StandardType.markChar, CFSG.StandardType.markDeg] using h
  obtain ⟨e8⟩ := CFSG.GH74.Exceptional.nonempty_mulEquiv_alternating_eight_of_lieModel hM'
  have hQ := rk2_isQuasisimple_of_isLabel hK
  refine pRank_le_rk2Mult_of_alt (lab := ⟨.A, 3, 1⟩) hQ 8 (by norm_num) ⟨θ.trans e8⟩ ?_ hp hp2
  intro p hp hp2
  by_cases hp8 : p ≤ 8
  · have hp357 : p = 3 ∨ p = 5 ∨ p = 7 := by
      interval_cases p <;> (try norm_num at hp; try norm_num at hp2; try norm_num)
    rcases hp357 with rfl | rfl | rfl
    · rw [rk2Ord_three_one_eq_two]; norm_num [rk2Mult]
    · rw [rk2Ord_five_one_eq_four]; norm_num [rk2Mult]
    · rw [rk2Ord_seven_one_eq_three]; norm_num [rk2Mult]
  · rw [Nat.div_eq_of_lt (by omega : 8 < p)]
    exact Nat.zero_le _

private theorem rk2KRank_D_three_one {K : Type} [Group K] [Finite K]
    (hK : Rk2IsLabel K ⟨.D, 3, 1⟩) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    CFSG.Open.pRank p (⊤ : Subgroup K) ≤
      rk2Mult (⟨.D, 3, 1⟩ : GLALabel) (rk2Ord p 1) := by
  obtain ⟨-, R, hgroup, -, ⟨θ⟩, hM⟩ := rk2_markedModel_of_isLabel hK
  letI : Group R := hgroup
  have hM' : CFSG.Blueprint.LieModel R .PSL 4 2 1 := by
    have h := hM
    unfold CFSG.StandardType.MarkedModel at h
    simpa [CFSG.StandardType.markTag, CFSG.StandardType.markRank,
      CFSG.StandardType.markChar, CFSG.StandardType.markDeg] using h
  obtain ⟨e8⟩ := CFSG.GH74.Exceptional.nonempty_mulEquiv_alternating_eight_of_lieModel hM'
  have hQ := rk2_isQuasisimple_of_isLabel hK
  refine pRank_le_rk2Mult_of_alt (lab := ⟨.D, 3, 1⟩) hQ 8 (by norm_num) ⟨θ.trans e8⟩ ?_ hp hp2
  intro p hp hp2
  by_cases hp8 : p ≤ 8
  · have hp357 : p = 3 ∨ p = 5 ∨ p = 7 := by
      interval_cases p <;> (try norm_num at hp; try norm_num at hp2; try norm_num)
    rcases hp357 with rfl | rfl | rfl
    · rw [rk2Ord_three_one_eq_two]; norm_num [rk2Mult]
    · rw [rk2Ord_five_one_eq_four]; norm_num [rk2Mult]
    · rw [rk2Ord_seven_one_eq_three]; norm_num [rk2Mult]
  · rw [Nat.div_eq_of_lt (by omega : 8 < p)]
    exact Nat.zero_le _

private theorem rk2KRank_twD_two_one {K : Type} [Group K] [Finite K]
    (hK : Rk2IsLabel K ⟨.twD, 2, 1⟩) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    CFSG.Open.pRank p (⊤ : Subgroup K) ≤
      rk2Mult (⟨.twD, 2, 1⟩ : GLALabel) (rk2Ord p 1) := by
  obtain ⟨-, R, hgroup, -, ⟨θ⟩, hM⟩ := rk2_markedModel_of_isLabel hK
  letI : Group R := hgroup
  have hM' : CFSG.Blueprint.LieModel R .PSL 2 2 2 := by
    have h := hM
    unfold CFSG.StandardType.MarkedModel at h
    simpa [CFSG.StandardType.markTag, CFSG.StandardType.markRank,
      CFSG.StandardType.markChar, CFSG.StandardType.markDeg] using h
  obtain ⟨e5⟩ := CFSG.LocalAnalysis.ComponentInitial.PSL2_four_alternating_five_model R hM'
  have hQ := rk2_isQuasisimple_of_isLabel hK
  refine pRank_le_rk2Mult_of_alt (lab := ⟨.twD, 2, 1⟩) hQ 5 (by norm_num) ⟨θ.trans e5⟩ ?_ hp hp2
  intro p hp hp2
  by_cases hp5 : p ≤ 5
  · have hp35 : p = 3 ∨ p = 5 := by
      interval_cases p <;> (try norm_num at hp; try norm_num at hp2; try norm_num)
    rcases hp35 with rfl | rfl
    · rw [rk2Ord_three_one_eq_two]; norm_num [rk2Mult]
    · rw [rk2Ord_five_one_eq_four]; norm_num [rk2Mult]
  · rw [Nat.div_eq_of_lt (by omega : 5 < p)]
    exact Nat.zero_le _


private theorem rk2KRank_A_two_one (hG : CFSG.Open.GriessAllModelsStatement) {K : Type}
    [Group K] [Finite K] (hK : Rk2IsLabel K ⟨.A, 2, 1⟩) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    CFSG.Open.pRank p (⊤ : Subgroup K) ≤
      rk2Mult (⟨.A, 2, 1⟩ : GLALabel) (rk2Ord p 1) := by
  have hS : CFSG.LocalAnalysis.RankThreeUC.S15.LieOddRankSmall :=
    CFSG.LocalAnalysis.RankThreeUC.S15.lieOddRankSmall_of_griess hG
  obtain ⟨-, R, hgroup, -, ⟨θ⟩, hM⟩ := rk2_markedModel_of_isLabel hK
  letI : Group R := hgroup
  have hM3 : CFSG.Blueprint.LieModel R .PSL 3 2 1 := by
    have h := hM
    unfold CFSG.StandardType.MarkedModel at h
    simpa [CFSG.StandardType.markTag, CFSG.StandardType.markRank,
      CFSG.StandardType.markChar, CFSG.StandardType.markDeg] using h
  have hM7 : CFSG.Blueprint.LieModel R .PSL 2 7 1 :=
    CFSG.LocalAnalysis.ComponentInitial.PSL3_two_PSL2_seven_paired_isomorphism R hM3
  obtain ⟨-, F, hfield, hfinite, hcard, ⟨e7⟩⟩ := hM7.statedClassicalModel (by decide)
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  let q : TauCeti.PrimePower := ⟨7, 1, by norm_num, by norm_num⟩
  have hv : (TauCeti.LieTypeIndex.A 1 q).Valid := by
    rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
      TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
    simp only [q, TauCeti.PrimePower.card_def, pow_one]
    refine ⟨⟨by norm_num, by norm_num⟩, ?_⟩
    rintro (⟨-, h4 | h5 | h9⟩ | ⟨h2, -⟩ | ⟨h3, -⟩) <;> omega
  have e1 := CFSG.ClassicalModels.statedLinearModelEquivGaloisPSL F 2 7 1
    (by norm_num) (by simpa [q, pow_one] using hcard)
  have e2 := (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 q hv).symm
  have hQ := rk2_isQuasisimple_of_isLabel hK
  have hpr : CFSG.Open.pRank p (⊤ : Subgroup K) = if p = 3 ∨ p = 7 then 1 else 0 :=
    (hS K hQ p hp hp2).1
      ⟨q, ⟨.A 1 q, hv⟩, by norm_num, rfl, ⟨(θ.trans e7).trans (e1.trans e2)⟩⟩
  rw [hpr]
  by_cases hp37 : p = 3 ∨ p = 7
  · rw [if_pos hp37]
    rcases hp37 with rfl | rfl
    · rw [rk2Ord_three_one_eq_two]; norm_num [rk2Mult]
    · rw [rk2Ord_seven_one_eq_three]; norm_num [rk2Mult]
  · rw [if_neg hp37]
    exact Nat.zero_le _

theorem rk2_tauCeti_index_of_isLabel {K : Type} [Group K] [Finite K] {lab : GLALabel}
    (hK : Rk2IsLabel K lab)
    (htag : lab.tag = .A ∨ lab.tag = .twA ∨ lab.tag = .B ∨ lab.tag = .C ∨
      lab.tag = .D ∨ lab.tag = .twD)
    (hA1 : lab.tag = .A → lab.rank = 1 → 3 ≤ lab.n)
    (hA2 : lab.tag = .A → lab.rank = 2 → 2 ≤ lab.n)
    (hA3 : lab.tag = .A → lab.rank = 3 → 2 ≤ lab.n)
    (hD3 : lab.tag = .D → lab.rank = 3 → 2 ≤ lab.n)
    (hTD2 : lab.tag = .twD → lab.rank = 2 → 2 ≤ lab.n) :
    ∃ d : TauCeti.ValidLieTypeIndex, CFSG.AGLEmbedding.IsClassicalOrG2Index d.1 ∧
      Nonempty ((K ⧸ Subgroup.center K) ≃* (TauCeti.CFSGIndex.lie d).Group) ∧
      ∀ r z, r.Prime → r ≠ 2 → mRankChev d.1 r z = rk2Chev lab r z := by
  rcases htag with hA | htwA | hB | hC | hD | htwD
  · exact rk2_index_A hK hA (hA1 hA) (hA2 hA) (hA3 hA)
  · exact rk2_index_twA hK htwA
  · exact rk2_index_BC hK (Or.inl hB)
  · exact rk2_index_BC hK (Or.inr hC)
  · exact rk2_index_D hK hD (hD3 hD)
  · exact rk2_index_twD hK htwD (hTD2 htwD)

theorem rk2_pRank_eq_of_isLabel_classical (hC : LieOddRankChev) {K : Type} [Group K]
    [Finite K] {lab : GLALabel} {p : ℕ} (hK : Rk2IsLabel K lab) (hp : p.Prime) (hp2 : p ≠ 2)
    (htag : lab.tag = .A ∨ lab.tag = .twA ∨ lab.tag = .B ∨ lab.tag = .C ∨
      lab.tag = .D ∨ lab.tag = .twD)
    (hA1 : lab.tag = .A → lab.rank = 1 → 3 ≤ lab.n)
    (hA2 : lab.tag = .A → lab.rank = 2 → 2 ≤ lab.n)
    (hA3 : lab.tag = .A → lab.rank = 3 → 2 ≤ lab.n)
    (hD3 : lab.tag = .D → lab.rank = 3 → 2 ≤ lab.n)
    (hTD2 : lab.tag = .twD → lab.rank = 2 → 2 ≤ lab.n) :
    CFSG.Open.pRank p (⊤ : Subgroup K) =
      rk2Chev lab p (Nat.card (Subgroup.center K)) := by
  obtain ⟨d, hclass, ⟨e⟩, hformula⟩ :=
    rk2_tauCeti_index_of_isLabel hK htag hA1 hA2 hA3 hD3 hTD2
  have hQ := rk2_isQuasisimple_of_isLabel hK
  rw [hC K hQ d hclass ⟨e⟩ p hp hp2]
  exact hformula p _ hp hp2

theorem rk2KRank_classical_generic (hC : LieOddRankChev) {K : Type} [Group K] [Finite K]
    {lab : GLALabel} {p : ℕ} (hK : Rk2IsLabel K lab) (hp : p.Prime) (hp2 : p ≠ 2)
    (htag : lab.tag = .A ∨ lab.tag = .twA ∨ lab.tag = .B ∨ lab.tag = .C ∨
      lab.tag = .D ∨ lab.tag = .twD)
    (hA1 : lab.tag = .A → lab.rank = 1 → 3 ≤ lab.n)
    (hA2 : lab.tag = .A → lab.rank = 2 → 2 ≤ lab.n)
    (hA3 : lab.tag = .A → lab.rank = 3 → 2 ≤ lab.n)
    (hD3 : lab.tag = .D → lab.rank = 3 → 2 ≤ lab.n)
    (hTD2 : lab.tag = .twD → lab.rank = 2 → 2 ≤ lab.n) :
    CFSG.Open.pRank p (⊤ : Subgroup K) ≤ rk2Mult lab (rk2Ord p lab.n) := by
  rw [rk2_pRank_eq_of_isLabel_classical hC hK hp hp2 htag hA1 hA2 hA3 hD3 hTD2]
  rcases htag with hA | htwA | hB | hC' | hD | htwD
  · rw [show rk2Chev lab p (Nat.card (Subgroup.center K)) =
        rkLin (lab.rank + 1) true (2 ^ lab.n) p (Nat.card (Subgroup.center K)) by
      simp [rk2Chev, hA]]
    exact rkLin_true_le_rk2Mult hp hp2 lab hA _
  · rw [show rk2Chev lab p (Nat.card (Subgroup.center K)) =
        rkLin (lab.rank + 1) false (2 ^ lab.n) p (Nat.card (Subgroup.center K)) by
      simp [rk2Chev, htwA]]
    exact rkLin_false_le_rk2Mult hp hp2 lab htwA _
  · rw [show rk2Chev lab p (Nat.card (Subgroup.center K)) =
        rkSp lab.rank (2 ^ lab.n) p by simp [rk2Chev, hB]]
    exact le_of_eq (rkSp_eq_rk2Mult hp hp2 lab (Or.inl hB))
  · rw [show rk2Chev lab p (Nat.card (Subgroup.center K)) =
        rkSp lab.rank (2 ^ lab.n) p by simp [rk2Chev, hC']]
    exact le_of_eq (rkSp_eq_rk2Mult hp hp2 lab (Or.inr hC'))
  · rw [show rk2Chev lab p (Nat.card (Subgroup.center K)) =
        rkOmPlus lab.rank (2 ^ lab.n) p by simp [rk2Chev, hD]]
    exact le_of_eq (rkOmPlus_eq_rk2Mult hp hp2 lab hD)
  · by_cases hr3 : lab.rank = 3
    · have hlab : lab = (⟨.twD, 3, lab.n⟩ : GLALabel) := by
        cases lab
        simp_all
      rw [hlab]
      rw [show rk2Chev (⟨.twD, 3, lab.n⟩ : GLALabel) p (Nat.card (Subgroup.center K)) =
          rkLin 4 false (2 ^ lab.n) p (Nat.card (Subgroup.center K)) by
        simp [rk2Chev]]
      exact rkLin_four_false_le_rk2Mult_twD_three hp hp2
    · rw [show rk2Chev lab p (Nat.card (Subgroup.center K)) =
          rkOmMinus lab.rank (2 ^ lab.n) p by
        simp [rk2Chev, htwD, hr3]]
      exact le_of_eq (rkOmMinus_eq_rk2Mult hp hp2 lab htwD)


theorem rk2KRank_classical (hG : CFSG.Open.GriessAllModelsStatement) {K : Type} [Group K]
    [Finite K] {lab : GLALabel} {p : ℕ} (hK : Rk2IsLabel K lab) (hp : p.Prime) (hp2 : p ≠ 2)
    (htag : lab.tag = .A ∨ lab.tag = .twA ∨ lab.tag = .B ∨ lab.tag = .C ∨
      lab.tag = .D ∨ lab.tag = .twD) :
    CFSG.Open.pRank p (⊤ : Subgroup K) ≤ rk2Mult lab (rk2Ord p lab.n) := by
  have hC : LieOddRankChev := CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20x_lieOddRankChev hG
  obtain ⟨t, l, n⟩ := lab
  by_cases hsmall : (t = .A ∧ l = 1 ∧ n = 2) ∨ (t = .A ∧ l = 2 ∧ n = 1) ∨
      (t = .A ∧ l = 3 ∧ n = 1) ∨ (t = .D ∧ l = 3 ∧ n = 1) ∨
      (t = .twD ∧ l = 2 ∧ n = 1)
  · rcases hsmall with ⟨hA, h1, h2⟩ | ⟨hA, h1, h2⟩ | ⟨hA, h1, h2⟩ |
      ⟨hA, h1, h2⟩ | ⟨hA, h1, h2⟩
    · subst t; subst l; subst n
      exact rk2KRank_A_one_two hK hp hp2
    · subst t; subst l; subst n
      exact rk2KRank_A_two_one hG hK hp hp2
    · subst t; subst l; subst n
      exact rk2KRank_A_three_one hK hp hp2
    · subst t; subst l; subst n
      exact rk2KRank_D_three_one hK hp hp2
    · subst t; subst l; subst n
      exact rk2KRank_twD_two_one hK hp hp2
  · have hlab : LargeEvenInLambda2 (⟨t, l, n⟩ : GLALabel) :=
      (rk2_markedModel_of_isLabel hK).1
    have hA1 : (⟨t, l, n⟩ : GLALabel).tag = .A → l = 1 → 3 ≤ n := by
      intro hA h1
      by_contra h
      have ht : t = .A := hA
      subst t
      simp only [CFSG.Assembly.LargeEvenInLambda2] at hlab
      have hn : n = 2 := by omega
      exact hsmall (Or.inl ⟨rfl, h1, hn⟩)
    have hA2 : (⟨t, l, n⟩ : GLALabel).tag = .A → l = 2 → 2 ≤ n := by
      intro hA h1
      by_contra h
      have ht : t = .A := hA
      subst t
      simp only [CFSG.Assembly.LargeEvenInLambda2] at hlab
      have hn : n = 1 := by omega
      exact hsmall (Or.inr (Or.inl ⟨rfl, h1, hn⟩))
    have hA3 : (⟨t, l, n⟩ : GLALabel).tag = .A → l = 3 → 2 ≤ n := by
      intro hA h1
      by_contra h
      have ht : t = .A := hA
      subst t
      simp only [CFSG.Assembly.LargeEvenInLambda2] at hlab
      have hn : n = 1 := by omega
      exact hsmall (Or.inr (Or.inr (Or.inl ⟨rfl, h1, hn⟩)))
    have hD3 : (⟨t, l, n⟩ : GLALabel).tag = .D → l = 3 → 2 ≤ n := by
      intro hD h1
      by_contra h
      have ht : t = .D := hD
      subst t
      simp only [CFSG.Assembly.LargeEvenInLambda2] at hlab
      have hn : n = 1 := by omega
      exact hsmall (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, h1, hn⟩))))
    have hTD2 : (⟨t, l, n⟩ : GLALabel).tag = .twD → l = 2 → 2 ≤ n := by
      intro hD h1
      by_contra h
      have ht : t = .twD := hD
      subst t
      simp only [CFSG.Assembly.LargeEvenInLambda2] at hlab
      have hn : n = 1 := by omega
      exact hsmall (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, h1, hn⟩))))
    exact rk2KRank_classical_generic hC hK hp hp2 htag hA1 hA2 hA3 hD3 hTD2


private theorem rk2_index_G2 {K : Type} [Group K] [Finite K] {lab : GLALabel}
    (hK : Rk2IsLabel K lab) (htag : lab.tag = .G2) :
    ∃ d : TauCeti.ValidLieTypeIndex, CFSG.AGLEmbedding.IsClassicalOrG2Index d.1 ∧
      Nonempty ((K ⧸ Subgroup.center K) ≃* (TauCeti.CFSGIndex.lie d).Group) ∧
      ∀ r z, r.Prime → r ≠ 2 → mRankChev d.1 r z = rk2Chev lab r z := by
  obtain ⟨hlab, R, hgroup, -, ⟨θ⟩, hM⟩ := rk2_markedModel_of_isLabel hK
  letI : Group R := hgroup
  have ht : CFSG.StandardType.markTag lab = .G2 := by
    simp [CFSG.StandardType.markTag, htag]
  have hr : CFSG.StandardType.markRank lab = 0 := by
    simp [CFSG.StandardType.markRank, htag]
  have hc : CFSG.StandardType.markChar lab = 2 := by
    simp [CFSG.StandardType.markChar, htag]
  have hd : CFSG.StandardType.markDeg lab = lab.n := by
    simp [CFSG.StandardType.markDeg, htag]
  have hM' := hM
  unfold CFSG.StandardType.MarkedModel at hM'
  rw [ht, hr, hc, hd] at hM'
  rcases hM' with ⟨hclass, -⟩ | ⟨-, -, hCE⟩ | ⟨-, hree, -⟩ | ⟨-, hsuz, -⟩
  · exact absurd hclass (by decide)
  · obtain ⟨hadm, F, hfield, hfinite, hcard, ⟨eA⟩⟩ := hCE
    letI : Field F := hfield
    letI : Finite F := hfinite
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    let q : TauCeti.PrimePower := ⟨2, lab.n, Nat.prime_two, by have := hadm.2.1; omega⟩
    have hv : (TauCeti.LieTypeIndex.G2 q).Valid := by
      rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
        TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
      simp only [q, TauCeti.PrimePower.card_def]
      exact ⟨hadm.2.2.2, not_false⟩
    let d : TauCeti.ValidLieTypeIndex := ⟨.G2 q, hv⟩
    have hcardd : Nat.card F = d.fieldOrder := by
      rw [show d.fieldOrder = 2 ^ lab.n by
        simp [d, q, TauCeti.ValidLieTypeIndex.fieldOrder, TauCeti.LieTypeIndex.fieldOrder_G2]]
      exact hcard
    obtain ⟨eB⟩ := CFSG.TauCetiBridge.Even.untwistedBridgeEven_G2 q hv rfl F
      (by simpa [q] using hcard)
    refine ⟨d, ?_, ⟨(θ.trans eA).trans eB⟩, ?_⟩
    · have hd1 : (d : TauCeti.ValidLieTypeIndex).1 = .G2 q := rfl
      rw [hd1]
      simp [CFSG.AGLEmbedding.IsClassicalOrG2Index, q]
    · intro r z hrp hr2
      have hd1 : (d : TauCeti.ValidLieTypeIndex).1 = .G2 q := rfl
      rw [hd1]
      simp [mRankChev, rk2Chev, htag, q, TauCeti.PrimePower.card_def]
  · exact absurd hree (by decide)
  · exact absurd hsuz (by decide)

theorem rk2KRank_G2 (hG : CFSG.Open.GriessAllModelsStatement) {K : Type} [Group K] [Finite K]
    {lab : GLALabel} {p : ℕ} (hK : Rk2IsLabel K lab) (hp : p.Prime) (hp2 : p ≠ 2)
    (htag : lab.tag = .G2) :
    CFSG.Open.pRank p (⊤ : Subgroup K) ≤ rk2Mult lab (rk2Ord p lab.n) := by
  have hC : LieOddRankChev :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20x_lieOddRankChev hG
  obtain ⟨d, hclass, ⟨e⟩, hformula⟩ := rk2_index_G2 hK htag
  have hQ := rk2_isQuasisimple_of_isLabel hK
  rw [hC K hQ d hclass ⟨e⟩ p hp hp2, hformula p _ hp hp2]
  rw [show rk2Chev lab p (Nat.card (Subgroup.center K)) = rkG2 (2 ^ lab.n) p by
    simp [rk2Chev, htag]]
  exact le_of_eq (rkG2_eq_rk2Mult hp hp2 lab (Or.inl htag))

end CFSG.LocalAnalysis.GLTheoremA
