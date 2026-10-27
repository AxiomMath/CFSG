module

public import CFSG.RankThree.PartOne.N143.Inspect613Even
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinBBridge
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDBridge
public import CFSG.Adapters.TauCetiExceptional.EvenBridgeG2
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeG2
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeIndex
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.LocalAnalysis.AGL81I.Section4

open CFSG.AGLEmbedding CFSG.AGLEmbedding.ParabPrime

theorem exists_sylow_eq_of_isSylowTwoOf {X : Type} [Group X] [Finite X] {T : Subgroup X}
    (hT : CFSG.QuasithinUnique.IsSylowTwoOf T ⊤) :
    ∃ S : Sylow 2 X, (S : Subgroup X) = T := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hidx : ¬ 2 ∣ T.index := by
    have := hT.2.2
    rwa [← Subgroup.relIndex, Subgroup.relIndex_top_right] at this
  exact ⟨hT.2.1.toSylow hidx, rfl⟩

private theorem parabCore_of_index_A (I : ParabInputs) {X : Type} [Group X] [Finite X]
    {r : ℕ} {q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.A r q).Valid) (hq : q.p = 2)
    (e : X ≃* (TauCeti.CFSGIndex.lie ⟨.A r q, hv⟩).Group) :
    ParabCore X (TauCeti.LieTypeIndex.A r q).fieldOrder := by
  have h := CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv e
  rw [hq] at h
  have hcore := parabCore_of_classicalModel I (Or.inl rfl)
    (by have := q.exponent_pos; omega) h
  simpa [TauCeti.LieTypeIndex.fieldOrder_A, TauCeti.PrimePower.card_def, hq] using hcore

private theorem parabCore_of_index_tA (I : ParabInputs) {X : Type} [Group X] [Finite X]
    {r : ℕ} {q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.twistedA r q).Valid)
    (hq : q.p = 2) (e : X ≃* (TauCeti.CFSGIndex.lie ⟨.twistedA r q, hv⟩).Group) :
    ParabCore X (TauCeti.LieTypeIndex.twistedA r q).fieldOrder := by
  have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e
  rw [hq] at h
  have hcore := parabCore_of_classicalModel I (Or.inr (Or.inl rfl))
    (by have := q.exponent_pos; omega) h
  simpa [TauCeti.LieTypeIndex.fieldOrder_twistedA, TauCeti.PrimePower.card_def, hq] using hcore

private theorem parabCore_of_index_B (I : ParabInputs) {X : Type} [Group X] [Finite X]
    {r : ℕ} {q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.B r q).Valid) (hq : q.p = 2)
    (e : X ≃* (TauCeti.CFSGIndex.lie ⟨.B r q, hv⟩).Group) :
    ParabCore X (TauCeti.LieTypeIndex.B r q).fieldOrder := by
  rcases Nat.lt_or_ge r 3 with h2 | h3
  · obtain rfl : r = 2 := by
      have hr := (TauCeti.LieTypeIndex.inStandardRange_iff (.B r q)).1
        ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
      omega
    have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e
    rw [hq] at h
    have hcore := parabCore_of_classicalModel I (Or.inr (Or.inr (Or.inl rfl)))
      (by have := q.exponent_pos; omega) h
    simpa [TauCeti.LieTypeIndex.fieldOrder_B, TauCeti.PrimePower.card_def, hq] using hcore
  · have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even r q hv hq
      (by omega) e
    rw [hq] at h
    have hcore := parabCore_of_classicalModel I (Or.inr (Or.inr (Or.inl rfl)))
      (by have := q.exponent_pos; omega) h
    simpa [TauCeti.LieTypeIndex.fieldOrder_B, TauCeti.PrimePower.card_def, hq] using hcore

private theorem parabCore_of_index_D (I : ParabInputs) {X : Type} [Group X] [Finite X]
    {r : ℕ} {q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.D r q).Valid) (hq : q.p = 2)
    (e : X ≃* (TauCeti.CFSGIndex.lie ⟨.D r q, hv⟩).Group) :
    ParabCore X (TauCeti.LieTypeIndex.D r q).fieldOrder := by
  have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD_even r q hv hq e
  rw [hq] at h
  have hcore := parabCore_of_classicalModel I (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    (by have := q.exponent_pos; omega) h
  simpa [TauCeti.LieTypeIndex.fieldOrder_D, TauCeti.PrimePower.card_def, hq] using hcore

private theorem parabCore_of_index_tD (I : ParabInputs) {X : Type} [Group X] [Finite X]
    {r : ℕ} {q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.twistedD r q).Valid)
    (hq : q.p = 2) (e : X ≃* (TauCeti.CFSGIndex.lie ⟨.twistedD r q, hv⟩).Group) :
    ParabCore X (TauCeti.LieTypeIndex.twistedD r q).fieldOrder := by
  have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD_even r q hv hq e
  rw [hq] at h
  have hcore := parabCore_of_classicalModel I (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
    (by have := q.exponent_pos; omega) h
  simpa [TauCeti.LieTypeIndex.fieldOrder_twistedD, TauCeti.PrimePower.card_def, hq] using hcore


private theorem parabCore_of_g2_index {X : Type} [Group X] [Finite X] {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.G2 q).Valid) (hq : q.p = 2)
    (e : X ≃* (TauCeti.CFSGIndex.lie ⟨.G2 q, hv⟩).Group) :
    ParabCore X (TauCeti.LieTypeIndex.G2 q).fieldOrder := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have : CharP (GaloisField q.p q.exponent) 2 := CharP.congr q.p hq
  have hK : Nat.card (GaloisField q.p q.exponent) = q.card := by
    rw [TauCeti.PrimePower.card_def, GaloisField.card q.p q.exponent q.exponent_pos.ne']
  obtain ⟨b⟩ := CFSG.TauCetiBridge.Even.untwistedBridgeEven_G2 q hv hq
    (GaloisField q.p q.exponent) hK
  have hq3 : 3 ≤ q.card := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have hcard : q.card = 2 ^ q.exponent := by rw [TauCeti.PrimePower.card_def, hq]
  have hm : 2 ≤ q.exponent := by
    by_contra hm
    have h1 : 2 ^ q.exponent ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hq4 : 4 ≤ q.card := by
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ q.exponent := Nat.pow_le_pow_right (by norm_num) hm
  have hcore := parabCore_g2 (e.trans b.symm) (hK ▸ hq4)
  simpa [hK, TauCeti.LieTypeIndex.fieldOrder_G2] using hcore

theorem parabCore_of_index (I : ParabInputs) {Y : Type} [Group Y] [Finite Y]
    (d : TauCeti.ValidLieTypeIndex) (hd : IsClassicalOrG2Index d.1)
    (e : Y ⧸ Subgroup.center Y ≃* (TauCeti.CFSGIndex.lie d).Group) :
    ParabCore (Y ⧸ Subgroup.center Y) d.1.fieldOrder := by
  obtain ⟨dd, hv⟩ := d
  cases dd with
  | A r q =>
    change q.p = 2 at hd
    exact parabCore_of_index_A I hv hd e
  | twistedA r q =>
    change q.p = 2 at hd
    exact parabCore_of_index_tA I hv hd e
  | B r q =>
    change q.p = 2 at hd
    exact parabCore_of_index_B I hv hd e
  | D r q =>
    change q.p = 2 at hd
    exact parabCore_of_index_D I hv hd e
  | twistedD r q =>
    change q.p = 2 at hd
    exact parabCore_of_index_tD I hv hd e
  | G2 q =>
    change q.p = 2 at hd
    exact parabCore_of_g2_index hv hd e
  | C r q => exact hd.elim
  | suzuki m => exact hd.elim
  | reeG2 m => exact hd.elim
  | reeF4 m => exact hd.elim
  | E6 q => exact hd.elim
  | E7 q => exact hd.elim
  | E8 q => exact hd.elim
  | F4 q => exact hd.elim
  | twistedE6 q => exact hd.elim
  | trialityD4 q => exact hd.elim
  | tits => exact hd.elim

theorem not_dvd_sq_sub_one_of_isClassicalTwoOrG2 (I : ParabInputs) {Y : Type} [Group Y]
    [Finite Y] (d : TauCeti.ValidLieTypeIndex) (hd : IsClassicalOrG2Index d.1)
    (e : Y ⧸ Subgroup.center Y ≃* (TauCeti.CFSGIndex.lie d).Group)
    {T J : Subgroup (Y ⧸ Subgroup.center Y)} (hT : CFSG.QuasithinUnique.IsSylowTwoOf T ⊤)
    (hNJ : Subgroup.normalizer (T : Set (Y ⧸ Subgroup.center Y)) ≤ J)
    (hJ : J ≠ Subgroup.normalizer (T : Set (Y ⧸ Subgroup.center Y)))
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpJ : ¬ p ∣ Nat.card J) :
    ¬ p ∣ d.1.fieldOrder ^ 2 - 1 := by
  obtain ⟨S, hS⟩ := exists_sylow_eq_of_isSylowTwoOf hT
  have hset : (S : Set (Y ⧸ Subgroup.center Y)) = (T : Set (Y ⧸ Subgroup.center Y)) :=
    congrArg (fun H : Subgroup (Y ⧸ Subgroup.center Y) =>
      (H : Set (Y ⧸ Subgroup.center Y))) hS
  have hNJ' : Subgroup.normalizer (S : Set (Y ⧸ Subgroup.center Y)) ≤ J := by
    rwa [hset]
  have hJ' : J ≠ Subgroup.normalizer (S : Set (Y ⧸ Subgroup.center Y)) := by
    rwa [hset]
  intro hpq
  have hcore := parabCore_of_index I d hd e
  obtain ⟨V, hVJ, -, hpV⟩ := (hcore S J hNJ' hJ' p hp hp5).1 hpq
  exact hpJ (hpV.trans (Subgroup.card_dvd_of_le hVJ))

end CFSG.LocalAnalysis.AGL81I.Section4

end
