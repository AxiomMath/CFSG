module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T123CBlockAbs
import CFSG.LocalAnalysis.GLTheoremA.CatA.T123CBlockTrans
import CFSG.LocalAnalysis.GLTheoremA.CatA.T123CBlockLinC
import CFSG.LocalAnalysis.GLTheoremA.CatA.T123CBlockFieldL
import CFSG.LocalAnalysis.GLTheoremA.CatA.T123CBlockFieldO
import CFSG.LocalAnalysis.GLTheoremA.CatA.T123CBlockOrthE
import CFSG.Adapters.LinearCatalogStated
import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
import CFSG.RankThree.PartTwo.Census.Carrier.SpinDOdd
import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDOdd
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
import CFSG.RankThree.PartOne.KC.OrthogonalAutSemilinearBridge
import CFSG.RankThree.PartOne.KFR4.Row4
public import CFSG.CharacterTheory.Wreathed.BrauerWongTypes
public import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Interface
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.GL83PartI.I_22_5.Setup
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBaseIso
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FFix
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FSeitzB1
public import CFSG.LocalAnalysis.GLTheoremA.P51.Quaternion
public import CFSG.LocalAnalysis.GLTheoremA.P55.Dihedral
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs105
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsBeta
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsSetup
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs119
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs16
public import CFSG.LocalAnalysis.GLTheoremA.S11.InputsCE
public import CFSG.LocalAnalysis.GLTheoremA.S11.InputsElim
public import CFSG.LocalAnalysis.GLTheoremA.S3.Lemma35
public import CFSG.LocalAnalysis.GLTheoremA.S9.Inputs95
public import CFSG.LocalAnalysis.GLTheoremA.S9.Lemma94
public import CFSG.LocalAnalysis.GLTheoremA.S9.Lemma95A
public import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Proof
public import CFSG.LocalAnalysis.SignalizerFunctor
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
import CFSG.RankThree.PartOne.S11d.LieGoodConclusion
import CFSG.RankThree.PartOne.S12.Sec1322Fin
import CFSG.RankThree.PartOne.S12.Sec136Inputs
import CFSG.RankThree.PartOne.S12.Sec136Pair
import CFSG.RankThree.PartOne.S12.Sec136Setup
import CFSG.RankThree.PartOne.S12.Sec138Loc
import CFSG.RankThree.PartOne.S12.Sec141Row
import CFSG.RankThree.PartOne.S12.Sec1511Y3

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T123CB

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData

section Models

theorem blockAt_of_projectiveSL {p m : ℕ} {T : Type} [Group T] {K : Type} [Field K] [Finite K]
    (e : T ≃* projectiveSL m K) (hm : 3 ≤ m) (hp : p.Prime) (hp2 : p ≠ 2)
    (hdvd : p ∣ Nat.card K + 1) : InnerBlockAt p T ∧ FieldBlockAt p T :=
  ⟨innerBlockAt_of_mulEquiv e (innerBlockAt_projectiveSL_of_dvd_succ hp hp2 (by omega) hdvd),
    fieldBlockAt_of_mulEquiv e (fieldBlockAt_projectiveSL_of_dvd_succ hm hp hp2 hdvd)⟩

theorem blockAt_of_typeA {p r : ℕ} {T : Type} [Group T] {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.A r q).Valid)
    (e : T ≃* TauCeti.ValidLieTypeIndex.Group ⟨.A r q, hv⟩) (hr : 2 ≤ r) (hp : p.Prime)
    (hp2 : p ≠ 2) (hdvd : p ∣ q.card + 1) : InnerBlockAt p T ∧ FieldBlockAt p T := by
  obtain ⟨-, K, _, _, hK, ⟨e'⟩⟩ :=
    CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv_typeA hv e
  refine blockAt_of_projectiveSL (e'.trans
    ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj _ K).symm.trans
      (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL
        _ K))) (by omega) hp hp2 ?_
  rwa [hK, ← TauCeti.PrimePower.card_def]

theorem blockAt_of_omegaPlus_model {p m f : ℕ} {T : Type} [Group T]
    (hM : StatedClassicalModel T .POmegaPlus m 2 f) (hm : 5 ≤ m) (hp : p.Prime) (hp2 : p ≠ 2)
    (hdvd : p ∣ 2 ^ f + 1) : InnerBlockAt p T ∧ FieldBlockAt p T := by
  refine ⟨?_, fieldBlockAt_of_omegaPlus_model hM hm hp hp2 hdvd⟩
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := id hM
  obtain ⟨hchar, hnd, -⟩ := coordinate_model_witness_plus hM K hK e
  haveI : CharP K 2 := ringChar.of_eq hchar
  haveI : Nonempty (Fin (2 * m)) := ⟨⟨0, by omega⟩⟩
  exact innerBlockAt_of_mulEquiv (((coordinatePlusWitnessEquiv K e).trans
    (CFSG.RankThree.PartOne.KCOrthogonalAut.coordBridge _ (by omega))).trans
      (CFSG.RankThree.PartOne.KFR4.orthDerivedEquivProj hnd).symm)
    (innerBlockAt_orthDerived _ hnd hp hp2 (by rwa [hK]))

theorem blockAt_of_omegaMinus_model {p m f : ℕ} {T : Type} [Group T]
    (hM : StatedClassicalModel T .POmegaMinus m 2 f) (hp : p.Prime) (hp2 : p ≠ 2)
    (hdvd : p ∣ 2 ^ f + 1) : InnerBlockAt p T ∧ FieldBlockAt p T := by
  refine ⟨?_, fieldBlockAt_of_omegaMinus_model hM hp hp2 hdvd⟩
  obtain ⟨-, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := id hM
  have hm : 4 ≤ m := hM.1.2.2
  have hn1 : 1 ≤ m := by omega
  obtain ⟨hchar, hnd, -⟩ := coordinate_model_witness_minus hM K hK b c hirr e
  haveI : CharP K 2 := ringChar.of_eq hchar
  haveI : Nonempty (Fin (2 * m)) := ⟨⟨0, by omega⟩⟩
  exact innerBlockAt_of_mulEquiv (((coordinateMinusWitnessEquiv K hn1 b c e).trans
    (CFSG.RankThree.PartOne.KCOrthogonalAut.coordBridge _ (by omega))).trans
      (CFSG.RankThree.PartOne.KFR4.orthDerivedEquivProj hnd).symm)
    (innerBlockAt_orthDerived _ hnd hp hp2 (by rwa [hK]))

private theorem primePower_p_eq_two {q : TauCeti.PrimePower} {j : ℕ} (hq : q.card = 2 ^ j) :
    q.p = 2 := by
  have h1 : q.p ∣ 2 ^ j := by
    rw [← hq, TauCeti.PrimePower.card_def]
    exact dvd_pow_self _ q.exponent_pos.ne'
  exact (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).mp (q.prime_p.dvd_of_dvd_pow h1)

theorem blockAt_of_typeD {p r j : ℕ} {T : Type} [Group T] {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.D r q).Valid)
    (e : T ≃* TauCeti.ValidLieTypeIndex.Group ⟨.D r q, hv⟩) (hr : 5 ≤ r) (hq : q.card = 2 ^ j)
    (hp : p.Prime) (hp2 : p ≠ 2) (hdvd : p ∣ q.card + 1) : InnerBlockAt p T ∧ FieldBlockAt p T := by
  have hq2 := primePower_p_eq_two hq
  have hM := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD r q hv e
  rw [hq2] at hM
  refine blockAt_of_omegaPlus_model hM hr hp hp2 ?_
  rwa [← hq2, ← TauCeti.PrimePower.card_def]

theorem blockAt_of_typeTwistedD {p r j : ℕ} {T : Type} [Group T] {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedD r q).Valid)
    (e : T ≃* TauCeti.ValidLieTypeIndex.Group ⟨.twistedD r q, hv⟩) (hq : q.card = 2 ^ j)
    (hp : p.Prime) (hp2 : p ≠ 2) (hdvd : p ∣ q.card + 1) : InnerBlockAt p T ∧ FieldBlockAt p T := by
  have hq2 := primePower_p_eq_two hq
  have hM := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD r q hv e
  rw [hq2] at hM
  refine blockAt_of_omegaMinus_model hM hp hp2 ?_
  rwa [← hq2, ← TauCeti.PrimePower.card_def]

end Models

section Index

private theorem exists_typeA_of_isLnEps {i : TauCeti.CFSGIndex} {m q : ℕ}
    (h : onLie (isLnEps m q true) i) :
    ∃ (r : ℕ) (qq : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.A r qq).Valid),
      r + 1 = m ∧ qq.card = q ∧ i = TauCeti.CFSGIndex.lie ⟨.A r qq, hv⟩ := by
  cases i with
  | cyclic l hl => simp [onLie] at h
  | alternating a ha => simp [onLie] at h
  | sporadic s => simp [onLie] at h
  | lie idx =>
    obtain ⟨d, hv⟩ := idx
    cases d with
    | A r qq =>
      have h' : r + 1 = m ∧ qq.card = q := h
      exact ⟨r, qq, hv, h'.1, h'.2, rfl⟩
    | _ => simp [onLie, isLnEps] at h

private theorem exists_typeD_of_isOmP {i : TauCeti.CFSGIndex} {m q : ℕ} (h : isOmP m q i) :
    ∃ (qq : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.D m qq).Valid),
      qq.card = q ∧ i = TauCeti.CFSGIndex.lie ⟨.D m qq, hv⟩ := by
  cases i with
  | cyclic l hl => simp [onLie, isOmP] at h
  | alternating a ha => simp [onLie, isOmP] at h
  | sporadic s => simp [onLie, isOmP] at h
  | lie idx =>
    obtain ⟨d, hv⟩ := idx
    cases d with
    | D r qq =>
      obtain ⟨rfl, hq⟩ : r = m ∧ qq.card = q := h
      exact ⟨qq, hv, hq, rfl⟩
    | _ => simp [onLie, isOmP] at h

private theorem exists_typeTwistedD_of_isOmM {i : TauCeti.CFSGIndex} {m q : ℕ}
    (h : isOmM m q i) :
    ∃ (qq : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.twistedD m qq).Valid),
      qq.card = q ∧ i = TauCeti.CFSGIndex.lie ⟨.twistedD m qq, hv⟩ := by
  cases i with
  | cyclic l hl => simp [onLie, isOmM] at h
  | alternating a ha => simp [onLie, isOmM] at h
  | sporadic s => simp [onLie, isOmM] at h
  | lie idx =>
    obtain ⟨d, hv⟩ := idx
    cases d with
    | twistedD r qq =>
      obtain ⟨rfl, hq⟩ : r = m ∧ qq.card = q := h
      exact ⟨qq, hv, hq, rfl⟩
    | _ => simp [onLie, isOmM] at h

private theorem one_le_of_valid_A {r : ℕ} {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.A r q).Valid) : 1 ≤ r :=
  ((TauCeti.LieTypeIndex.inStandardRange_iff _).mp ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1).1

private theorem four_le_of_valid_D {r : ℕ} {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.D r q).Valid) : 4 ≤ r :=
  (TauCeti.LieTypeIndex.inStandardRange_iff _).mp ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1

private theorem four_le_of_valid_twistedD {r : ℕ} {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedD r q).Valid) : 4 ≤ r :=
  (TauCeti.LieTypeIndex.inStandardRange_iff _).mp ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1

private theorem blockAt_of_isLnA {p m q : ℕ} {T : Type} [Group T] (h : catalogIs T (isLnA m q))
    (hm : 3 ≤ m) (hsmall : m ≤ 4 → q ≠ 2) (hp : p.Prime) (hp2 : p ≠ 2) (hdvd : p ∣ q + 1) :
    InnerBlockAt p T ∧ FieldBlockAt p T := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  rcases hi with h1 | ⟨h2, -⟩ | ⟨h2, -⟩ | ⟨h3, hq3, -⟩ | ⟨h4, hq4, -⟩
  · obtain ⟨r, qq, hv, hr, hq, rfl⟩ := exists_typeA_of_isLnEps h1
    exact blockAt_of_typeA hv e (by omega) hp hp2 (by rwa [hq])
  · omega
  · omega
  · exact absurd hq3 (hsmall (by omega))
  · exact absurd hq4 (hsmall (by omega))

private theorem blockAt_of_isOmP {p m j : ℕ} {T : Type} [Group T]
    (h : catalogIs T (isOmPA m (2 ^ j))) (hm : 5 ≤ m) (hp : p.Prime) (hp2 : p ≠ 2)
    (hdvd : p ∣ 2 ^ j + 1) : InnerBlockAt p T ∧ FieldBlockAt p T := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  rcases hi with h1 | ⟨h3, -⟩
  · obtain ⟨qq, hv, hq, rfl⟩ := exists_typeD_of_isOmP h1
    exact blockAt_of_typeD hv e hm hq hp hp2 (by rwa [hq])
  · omega

private theorem blockAt_of_isOmM {p m j : ℕ} {T : Type} [Group T]
    (h : catalogIs T (isOmMA m (2 ^ j))) (hm : m ≠ 3) (hp : p.Prime) (hp2 : p ≠ 2)
    (hdvd : p ∣ 2 ^ j + 1) : InnerBlockAt p T ∧ FieldBlockAt p T := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  rcases hi with h1 | ⟨h3, -⟩
  · obtain ⟨qq, hv, hq, rfl⟩ := exists_typeTwistedD_of_isOmM h1
    exact blockAt_of_typeTwistedD hv e hq hp hp2 (by rwa [hq])
  · exact absurd h3 hm

private theorem two_le_of_isLnA {n q : ℕ} {J : Type} [Group J] (h : catalogIs J (isLnA n q)) :
    2 ≤ n := by
  obtain ⟨i, hi, -⟩ := h
  rcases hi with h1 | ⟨h2, -⟩ | ⟨h2, -⟩ | ⟨h3, -⟩ | ⟨h4, -⟩
  · obtain ⟨r, qq, hv, hr, -, rfl⟩ := exists_typeA_of_isLnEps h1
    have := one_le_of_valid_A hv
    omega
  all_goals omega

private theorem three_le_of_isOmMA {n q : ℕ} {J : Type} [Group J] (h : catalogIs J (isOmMA n q)) :
    3 ≤ n := by
  obtain ⟨i, hi, -⟩ := h
  rcases hi with h1 | ⟨h3, -⟩
  · obtain ⟨qq, hv, -, rfl⟩ := exists_typeTwistedD_of_isOmM h1
    have := four_le_of_valid_twistedD hv
    omega
  · omega

private theorem three_le_of_isOmPA {n q : ℕ} {J : Type} [Group J] (h : catalogIs J (isOmPA n q)) :
    3 ≤ n := by
  obtain ⟨i, hi, -⟩ := h
  rcases hi with h1 | ⟨h3, -⟩
  · obtain ⟨qq, hv, -, rfl⟩ := exists_typeD_of_isOmP h1
    have := four_le_of_valid_D hv
    omega
  · omega

end Index

private theorem dvd_two_pow_mul_add_one {p k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hdvd : p ∣ 2 ^ k + 1) : p ∣ 2 ^ (p * k) + 1 := by
  have h1 : 2 ^ k + 1 ∣ (2 ^ k) ^ p + 1 ^ p :=
    Odd.nat_add_dvd_pow_add_pow (2 ^ k) 1 (hp.odd_of_ne_two hp2)
  rw [one_pow, ← pow_mul, mul_comm] at h1
  exact hdvd.trans h1

theorem blockAt_of_type167At {p : ℕ} {T J : Type} [Group T] [Group J] (hp : p.Prime)
    (hp2 : p ≠ 2) (h : Type167At p T J) : InnerBlockAt p T ∧ FieldBlockAt p T := by
  rcases h with ⟨rfl, n, hn, hJ, hT | hT⟩ | ⟨rfl, n, hn, hJ, hT | hT⟩ |
      ⟨n, k, hn, hk, hdvd, hJ, hT | hT | ⟨rfl, rfl, rfl, hT⟩⟩
  ·
    have h2 := two_le_of_isLnA hJ
    obtain ⟨j, rfl⟩ := hn
    exact blockAt_of_isLnA hT (by omega) (fun h => by omega) hp hp2 (by norm_num)
  ·
    have h2 := two_le_of_isLnA hJ
    obtain ⟨j, rfl⟩ := hn
    exact blockAt_of_isLnA hT (by omega) (fun _ => by norm_num) hp hp2 (by norm_num)
  ·
    have h3 := three_le_of_isOmMA hJ
    obtain ⟨j, rfl⟩ := hn
    exact blockAt_of_isOmP (j := 1) (by rwa [pow_one]) (by omega) hp hp2 (by norm_num)
  ·
    obtain ⟨j, rfl⟩ := hn
    exact blockAt_of_isOmM (j := 3) (by rw [show (2 : ℕ) ^ 3 = 8 by norm_num]; exact hT)
      (by omega) hp hp2 (by norm_num)
  ·
    obtain ⟨j, rfl⟩ := hn
    exact blockAt_of_isOmM hT (by omega) hp hp2 hdvd
  ·
    have h3 := three_le_of_isOmPA hJ
    have hdvd' := dvd_two_pow_mul_add_one hp hp2 hdvd
    obtain ⟨i, hi, he⟩ := hT
    rcases hi with h1 | ⟨hn3, h4⟩
    · obtain ⟨j, rfl⟩ := hn
      obtain ⟨qq, hv, -, rfl⟩ := exists_typeD_of_isOmP h1
      have := four_le_of_valid_D hv
      exact blockAt_of_isOmP ⟨_, Or.inl h1, he⟩ (by omega) hp hp2 hdvd'
    · refine blockAt_of_isLnA ⟨i, h4, he⟩ (by norm_num) (fun _ h2 => ?_) hp hp2 hdvd'
      have hpk : p * k = 1 := Nat.pow_right_injective le_rfl (h2.trans (pow_one 2).symm)
      exact hp.one_lt.ne' (Nat.eq_one_of_mul_eq_one_right hpk)
  ·
    exact blockAt_of_isLnA hT (by norm_num) (fun h => by omega) hp hp2 (by norm_num)

theorem blockFact_holds : T123C.BlockFact :=
  blockFact_of_models fun _ _ _ _ _ _ hp hp2 h => blockAt_of_type167At hp hp2 h

end CFSG.LocalAnalysis.GLTheoremA.T123CB

end
