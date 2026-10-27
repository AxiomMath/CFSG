module

public import CFSG.LocalAnalysis.GLTheoremA.S3.KData
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofA6Core
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanCoverThreeRank
public import CFSG.Adapters.TauCetiExceptional.ReeCatalog
public import CFSG.HardMathSupport.Foote.Coordinator.CoverThree.Order

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)


private theorem ex3_dvd27_of_model {X : Type} [Group X] {t : CFSG.Open.StatedLieTag} {n f : ℕ}
    (hadm : CFSG.Open.StatedLieAdmissible t n 3 f) (hL : CFSG.Blueprint.LieModel X t n 3 f)
    (hN : 3 ≤ CFSG.ComponentClassification.CatLeaf.lieSylowExponent t n * f) :
    27 ∣ Nat.card X := by
  obtain ⟨hfin, -, hfac⟩ :=
    CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput X t n 3 f hadm hL
  haveI := hfin
  have hne : Nat.card X ≠ 0 := Nat.card_pos.ne'
  have h : 3 ^ 3 ∣ Nat.card X :=
    (Nat.Prime.pow_dvd_iff_le_factorization (k := 3) Nat.prime_three hne).2
      (by rw [hfac]; exact hN)
  simpa using h

private theorem ex3_dvd27_of_classical {X : Type} [Group X] {t : CFSG.Open.StatedLieTag}
    {n f : ℕ} (ht : t ∈ CFSG.Blueprint.classicalTags)
    (hC : CFSG.Open.StatedClassicalModel X t n 3 f) (hPSL : ¬ (t = .PSL ∧ n = 2)) :
    27 ∣ Nat.card X := by
  have hadm := hC.1
  refine ex3_dvd27_of_model hadm (Or.inl ⟨ht, hC⟩) ?_
  have hf : 1 ≤ f := hadm.2.1
  rcases CFSG.ComponentClassification.CatLeafProof.lieSylowExponent_ge_three hadm (by norm_num)
    with h | h
  · exact absurd h hPSL
  · exact le_trans h (Nat.le_mul_of_pos_right _ hf)

private theorem ex3_dvd27_A {r : ℕ} (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.A r q).Valid) (hp : q.p = 3) (hr : 2 ≤ r) :
    27 ∣ Nat.card (TauCeti.CFSGIndex.lie ⟨.A r q, hv⟩).Group := by
  have hC := CFSG.AGLEmbedding.KFactProofs.CoverFive.statedClassicalModel_psl_of_typeA r q hv
    (MulEquiv.refl _)
  rw [hp] at hC
  exact ex3_dvd27_of_classical (by decide) hC (by omega)

private theorem ex3_dvd27_twistedA {r : ℕ} (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedA r q).Valid) (hp : q.p = 3) :
    27 ∣ Nat.card (TauCeti.CFSGIndex.lie ⟨.twistedA r q, hv⟩).Group := by
  have hC := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv (MulEquiv.refl _)
  rw [hp] at hC
  exact ex3_dvd27_of_classical (by decide) hC (by simp)

private theorem ex3_dvd27_B2 (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.B 2 q).Valid)
    (hp : q.p = 3) : 27 ∣ Nat.card (TauCeti.CFSGIndex.lie ⟨.B 2 q, hv⟩).Group := by
  have hC := CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv (MulEquiv.refl _)
  rw [hp] at hC
  exact ex3_dvd27_of_classical (by decide) hC (by simp)

private theorem ex3_dvd27_B {r : ℕ} (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.B r q).Valid) (hp : q.p = 3) (hr : 3 ≤ r) :
    27 ∣ Nat.card (TauCeti.CFSGIndex.lie ⟨.B r q, hv⟩).Group := by
  have hC := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_odd r q hv
    (by rw [hp]; norm_num) hr (MulEquiv.refl _)
  rw [hp] at hC
  exact ex3_dvd27_of_classical (by decide) hC (by simp)

private theorem ex3_dvd27_C {r : ℕ} (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.C r q).Valid) (hp : q.p = 3) :
    27 ∣ Nat.card (TauCeti.CFSGIndex.lie ⟨.C r q, hv⟩).Group := by
  have hC := CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeC r q hv (MulEquiv.refl _)
  rw [hp] at hC
  exact ex3_dvd27_of_classical (by decide) hC (by simp)

private theorem ex3_dvd27_D {r : ℕ} (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.D r q).Valid) (hp : q.p = 3) :
    27 ∣ Nat.card (TauCeti.CFSGIndex.lie ⟨.D r q, hv⟩).Group := by
  have hC := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD r q hv (MulEquiv.refl _)
  rw [hp] at hC
  exact ex3_dvd27_of_classical (by decide) hC (by simp)

private theorem ex3_dvd27_twistedD {r : ℕ} (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedD r q).Valid) (hp : q.p = 3) :
    27 ∣ Nat.card (TauCeti.CFSGIndex.lie ⟨.twistedD r q, hv⟩).Group := by
  have hC := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD r q hv
    (MulEquiv.refl _)
  rw [hp] at hC
  exact ex3_dvd27_of_classical (by decide) hC (by simp)

private theorem ex3_dvd27_of_chevalley {X : Type} [Group X] {t : CFSG.Open.StatedLieTag}
    {p f : ℕ} (ht : t ∈ CFSG.Blueprint.chevalleyExceptionalTags)
    (hm : CFSG.Blueprint.ChevalleyExceptionalModel X t p f) (hp : p = 3)
    (hN : 3 ≤ CFSG.ComponentClassification.CatLeaf.lieSylowExponent t 0) :
    27 ∣ Nat.card X := by
  subst hp
  have hf : 1 ≤ f := hm.1.2.1
  exact ex3_dvd27_of_model hm.1 (Or.inr (Or.inl ⟨rfl, ht, hm⟩))
    (le_trans hN (Nat.le_mul_of_pos_right _ hf))

private theorem ex3_dvd27_of_ree {X : Type} [Group X] {t : CFSG.Open.StatedLieTag}
    {p f : ℕ} (ht : t ∈ CFSG.Blueprint.reeTitsTags)
    (hm : CFSG.Blueprint.ReeTitsModel X t p f) (hp : p = 3)
    (hN : 3 ≤ CFSG.ComponentClassification.CatLeaf.lieSylowExponent t 0) :
    27 ∣ Nat.card X := by
  subst hp
  have hf : 1 ≤ f := hm.1.2.1
  exact ex3_dvd27_of_model hm.1 (Or.inr (Or.inr (Or.inl ⟨rfl, ht, hm⟩)))
    (le_trans hN (Nat.le_mul_of_pos_right _ hf))

private theorem ex3_dvd27_G2 (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.G2 q).Valid)
    (hp : q.p = 3) : 27 ∣ Nat.card (TauCeti.CFSGIndex.lie ⟨.G2 q, hv⟩).Group := by
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hK : Nat.card (GaloisField q.p q.exponent) = q.card := by
    rw [GaloisField.card _ _ q.exponent_pos.ne', TauCeti.PrimePower.card_def]
  obtain ⟨b⟩ := CFSG.TauCetiBridge.typewiseBridges.g2 q hv (by rw [hp]; norm_num)
    (GaloisField q.p q.exponent) hK
  have hq3 : 3 ≤ q.p ^ q.exponent := by
    rw [← TauCeti.PrimePower.card_def]
    exact (TauCeti.LieTypeIndex.inStandardRange_iff _).1 ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have hK' : Nat.card (GaloisField q.p q.exponent) = q.p ^ q.exponent :=
    GaloisField.card _ _ q.exponent_pos.ne'
  refine ex3_dvd27_of_chevalley (t := .G2) (p := q.p) (f := q.exponent) (by decide) ?_ hp
    (by decide)
  exact ⟨⟨q.prime_p, q.exponent_pos, rfl, hq3⟩, GaloisField q.p q.exponent, inferInstance,
    inferInstance, hK', ⟨b.symm⟩⟩

private theorem ex3_dvd27_F4 (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.F4 q).Valid)
    (hp : q.p = 3) : 27 ∣ Nat.card (TauCeti.CFSGIndex.lie ⟨.F4 q, hv⟩).Group := by
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hK : Nat.card (GaloisField q.p q.exponent) = q.card := by
    rw [GaloisField.card _ _ q.exponent_pos.ne', TauCeti.PrimePower.card_def]
  obtain ⟨b⟩ := CFSG.TauCetiBridge.typewiseBridges.f4 q hv (by rw [hp]; norm_num)
    (GaloisField q.p q.exponent) hK
  have hK' : Nat.card (GaloisField q.p q.exponent) = q.p ^ q.exponent :=
    GaloisField.card _ _ q.exponent_pos.ne'
  refine ex3_dvd27_of_chevalley (t := .F4) (p := q.p) (f := q.exponent) (by decide) ?_ hp
    (by decide)
  exact ⟨⟨q.prime_p, q.exponent_pos, rfl⟩, GaloisField q.p q.exponent, inferInstance,
    inferInstance, hK', ⟨b.symm⟩⟩

private theorem ex3_dvd27_E6 (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.E6 q).Valid)
    (hp : q.p = 3) : 27 ∣ Nat.card (TauCeti.CFSGIndex.lie ⟨.E6 q, hv⟩).Group := by
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hK : Nat.card (GaloisField q.p q.exponent) = q.card := by
    rw [GaloisField.card _ _ q.exponent_pos.ne', TauCeti.PrimePower.card_def]
  obtain ⟨b⟩ := CFSG.TauCetiBridge.typewiseBridges.e6 q hv (by rw [hp]; norm_num)
    (GaloisField q.p q.exponent) hK
  have hK' : Nat.card (GaloisField q.p q.exponent) = q.p ^ q.exponent :=
    GaloisField.card _ _ q.exponent_pos.ne'
  refine ex3_dvd27_of_chevalley (t := .E6) (p := q.p) (f := q.exponent) (by decide) ?_ hp
    (by decide)
  exact ⟨⟨q.prime_p, q.exponent_pos, rfl⟩, GaloisField q.p q.exponent, inferInstance,
    inferInstance, hK', ⟨b.symm⟩⟩

private theorem ex3_dvd27_E7 (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.E7 q).Valid)
    (hp : q.p = 3) : 27 ∣ Nat.card (TauCeti.CFSGIndex.lie ⟨.E7 q, hv⟩).Group := by
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hK : Nat.card (GaloisField q.p q.exponent) = q.card := by
    rw [GaloisField.card _ _ q.exponent_pos.ne', TauCeti.PrimePower.card_def]
  obtain ⟨b⟩ := CFSG.TauCetiBridge.typewiseBridges.e7 q hv (by rw [hp]; norm_num)
    (GaloisField q.p q.exponent) hK
  have hK' : Nat.card (GaloisField q.p q.exponent) = q.p ^ q.exponent :=
    GaloisField.card _ _ q.exponent_pos.ne'
  refine ex3_dvd27_of_chevalley (t := .E7) (p := q.p) (f := q.exponent) (by decide) ?_ hp
    (by decide)
  exact ⟨⟨q.prime_p, q.exponent_pos, rfl⟩, GaloisField q.p q.exponent, inferInstance,
    inferInstance, hK', ⟨b.symm⟩⟩

private theorem ex3_dvd27_E8 (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.E8 q).Valid)
    (hp : q.p = 3) : 27 ∣ Nat.card (TauCeti.CFSGIndex.lie ⟨.E8 q, hv⟩).Group := by
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hK : Nat.card (GaloisField q.p q.exponent) = q.card := by
    rw [GaloisField.card _ _ q.exponent_pos.ne', TauCeti.PrimePower.card_def]
  obtain ⟨b⟩ := CFSG.TauCetiBridge.typewiseBridges.e8 q hv (by rw [hp]; norm_num)
    (GaloisField q.p q.exponent) hK
  have hK' : Nat.card (GaloisField q.p q.exponent) = q.p ^ q.exponent :=
    GaloisField.card _ _ q.exponent_pos.ne'
  refine ex3_dvd27_of_chevalley (t := .E8) (p := q.p) (f := q.exponent) (by decide) ?_ hp
    (by decide)
  exact ⟨⟨q.prime_p, q.exponent_pos, rfl⟩, GaloisField q.p q.exponent, inferInstance,
    inferInstance, hK', ⟨b.symm⟩⟩

private theorem ex3_dvd27_twistedE6 (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedE6 q).Valid) (hp : q.p = 3) :
    27 ∣ Nat.card (TauCeti.CFSGIndex.lie ⟨.twistedE6 q, hv⟩).Group := by
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hK : Nat.card (GaloisField q.p (q.exponent * CFSG.Blueprint.Chevalley.TwistTag.E6.order))
      = q.card ^ CFSG.Blueprint.Chevalley.TwistTag.E6.order := by
    rw [GaloisField.card _ _ (Nat.mul_ne_zero q.exponent_pos.ne' (by decide)), pow_mul,
      TauCeti.PrimePower.card_def]
  have hK' : Nat.card (GaloisField q.p (q.exponent * CFSG.Blueprint.Chevalley.TwistTag.E6.order))
      = (q.p ^ q.exponent) ^ CFSG.Blueprint.Chevalley.TwistTag.E6.order := by
    rw [GaloisField.card _ _ (Nat.mul_ne_zero q.exponent_pos.ne' (by decide)), pow_mul]
  let σ : GaloisField q.p (q.exponent * CFSG.Blueprint.Chevalley.TwistTag.E6.order) →+*
      GaloisField q.p (q.exponent * CFSG.Blueprint.Chevalley.TwistTag.E6.order) :=
    iterateFrobenius _ q.p q.exponent
  have hσ : ∀ x, σ x = x ^ q.card := fun x => by
    rw [TauCeti.PrimePower.card_def]
    rfl
  have hσ' : ∀ x, σ x = x ^ (q.p ^ q.exponent) := fun _ => rfl
  obtain ⟨b⟩ := CFSG.TauCetiBridge.typewiseBridges.twistedE6 q hv (by rw [hp]; norm_num)
    (GaloisField q.p (q.exponent * CFSG.Blueprint.Chevalley.TwistTag.E6.order)) hK σ hσ
  refine ex3_dvd27_of_chevalley (t := .twistedE6) (p := q.p) (f := q.exponent) (by decide) ?_ hp
    (by decide)
  exact ⟨⟨q.prime_p, q.exponent_pos, rfl⟩, GaloisField q.p (q.exponent *
    CFSG.Blueprint.Chevalley.TwistTag.E6.order), inferInstance, inferInstance, hK', σ, hσ',
    ⟨b.symm⟩⟩

private theorem ex3_dvd27_trialityD4 (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid) (hp : q.p = 3) :
    27 ∣ Nat.card (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hv⟩).Group := by
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hK : Nat.card (GaloisField q.p (q.exponent * CFSG.Blueprint.Chevalley.TwistTag.D4.order))
      = q.card ^ CFSG.Blueprint.Chevalley.TwistTag.D4.order := by
    rw [GaloisField.card _ _ (Nat.mul_ne_zero q.exponent_pos.ne' (by decide)), pow_mul,
      TauCeti.PrimePower.card_def]
  have hK' : Nat.card (GaloisField q.p (q.exponent * CFSG.Blueprint.Chevalley.TwistTag.D4.order))
      = (q.p ^ q.exponent) ^ CFSG.Blueprint.Chevalley.TwistTag.D4.order := by
    rw [GaloisField.card _ _ (Nat.mul_ne_zero q.exponent_pos.ne' (by decide)), pow_mul]
  let σ : GaloisField q.p (q.exponent * CFSG.Blueprint.Chevalley.TwistTag.D4.order) →+*
      GaloisField q.p (q.exponent * CFSG.Blueprint.Chevalley.TwistTag.D4.order) :=
    iterateFrobenius _ q.p q.exponent
  have hσ : ∀ x, σ x = x ^ q.card := fun x => by
    rw [TauCeti.PrimePower.card_def]
    rfl
  have hσ' : ∀ x, σ x = x ^ (q.p ^ q.exponent) := fun _ => rfl
  obtain ⟨b⟩ := CFSG.TauCetiBridge.typewiseBridges.trialityD4 q hv (by rw [hp]; norm_num)
    (GaloisField q.p (q.exponent * CFSG.Blueprint.Chevalley.TwistTag.D4.order)) hK σ hσ
  refine ex3_dvd27_of_chevalley (t := .trialityD4) (p := q.p) (f := q.exponent) (by decide) ?_ hp
    (by decide)
  exact ⟨⟨q.prime_p, q.exponent_pos, rfl⟩, GaloisField q.p (q.exponent *
    CFSG.Blueprint.Chevalley.TwistTag.D4.order), inferInstance, inferInstance, hK', σ, hσ',
    ⟨b.symm⟩⟩

private theorem ex3_dvd27_reeG2 (m : ℕ) (hv : (TauCeti.LieTypeIndex.reeG2 m).Valid) :
    27 ∣ Nat.card (TauCeti.CFSGIndex.lie ⟨.reeG2 m, hv⟩).Group := by
  have hm1 : 1 ≤ m :=
    ((TauCeti.LieTypeIndex.inStandardRange_iff _).1 ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1)
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK : Nat.card (GaloisField 3 (2 * m + 1)) = 3 ^ (2 * m + 1) :=
    GaloisField.card _ _ (by omega)
  obtain ⟨b⟩ := CFSG.TauCetiBridge.typewiseBridges.reeG2 m hv (GaloisField 3 (2 * m + 1)) hK
  refine ex3_dvd27_of_ree (t := .twistedG2) (p := 3) (f := 2 * m + 1) (by decide) ?_ rfl
    (by decide)
  exact ⟨⟨Nat.prime_three, by omega, rfl, rfl, ⟨m, rfl⟩, by omega⟩, m, rfl,
    GaloisField 3 (2 * m + 1), inferInstance, inferInstance, hK, ⟨b.symm⟩⟩

private theorem ex3_dvd27_A1 (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.A 1 q).Valid)
    (hp : q.p = 3) : 27 ∣ Nat.card (TauCeti.CFSGIndex.lie ⟨.A 1 q, hv⟩).Group := by
  have hvv := (TauCeti.LieTypeIndex.valid_iff _).1 hv
  have hr : 4 ≤ q.card := ((TauCeti.LieTypeIndex.inStandardRange_iff _).1 hvv.1).2 rfl
  have hnd : q.card ≠ 9 := fun h9 => hvv.2 ((TauCeti.LieTypeIndex.isDuplicateRepresentative_iff
    _).2 (Or.inl ⟨rfl, Or.inr (Or.inr h9)⟩))
  have hf : 3 ≤ q.exponent := by
    by_contra hf
    have h1 : q.exponent = 1 ∨ q.exponent = 2 := by have := q.exponent_pos; omega
    rw [TauCeti.PrimePower.card_def, hp] at hr hnd
    rcases h1 with h1 | h1
    · rw [h1] at hr
      norm_num at hr
    · rw [h1] at hnd
      norm_num at hnd
  have hC := CFSG.AGLEmbedding.KFactProofs.CoverFive.statedClassicalModel_psl_of_typeA 1 q hv
    (MulEquiv.refl _)
  rw [hp] at hC
  refine ex3_dvd27_of_model hC.1 (Or.inl ⟨by decide, hC⟩) ?_
  simpa [CFSG.ComponentClassification.CatLeaf.lieSylowExponent] using hf

private theorem ex3_dvd27_char3 (d : TauCeti.ValidLieTypeIndex) (h : d.1.characteristic = 3) :
    27 ∣ Nat.card d.Group := by
  obtain ⟨d, hv⟩ := d
  have hstd := (TauCeti.LieTypeIndex.inStandardRange_iff _).1 ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  cases d with
  | A r q =>
    rw [TauCeti.LieTypeIndex.characteristic_A] at h
    rcases r with _ | _ | r
    · exact absurd hstd.1 (by norm_num)
    · exact ex3_dvd27_A1 q hv h
    · exact ex3_dvd27_A q hv h (by omega)
  | twistedA r q =>
    rw [TauCeti.LieTypeIndex.characteristic_twistedA] at h
    exact ex3_dvd27_twistedA q hv h
  | B r q =>
    rw [TauCeti.LieTypeIndex.characteristic_B] at h
    rcases (show r = 2 ∨ 3 ≤ r by have := hstd.1; omega) with rfl | hr3
    · exact ex3_dvd27_B2 q hv h
    · exact ex3_dvd27_B q hv h hr3
  | C r q =>
    rw [TauCeti.LieTypeIndex.characteristic_C] at h
    exact ex3_dvd27_C q hv h
  | D r q =>
    rw [TauCeti.LieTypeIndex.characteristic_D] at h
    exact ex3_dvd27_D q hv h
  | twistedD r q =>
    rw [TauCeti.LieTypeIndex.characteristic_twistedD] at h
    exact ex3_dvd27_twistedD q hv h
  | E6 q =>
    rw [TauCeti.LieTypeIndex.characteristic_E6] at h
    exact ex3_dvd27_E6 q hv h
  | E7 q =>
    rw [TauCeti.LieTypeIndex.characteristic_E7] at h
    exact ex3_dvd27_E7 q hv h
  | E8 q =>
    rw [TauCeti.LieTypeIndex.characteristic_E8] at h
    exact ex3_dvd27_E8 q hv h
  | F4 q =>
    rw [TauCeti.LieTypeIndex.characteristic_F4] at h
    exact ex3_dvd27_F4 q hv h
  | G2 q =>
    rw [TauCeti.LieTypeIndex.characteristic_G2] at h
    exact ex3_dvd27_G2 q hv h
  | twistedE6 q =>
    rw [TauCeti.LieTypeIndex.characteristic_twistedE6] at h
    exact ex3_dvd27_twistedE6 q hv h
  | trialityD4 q =>
    rw [TauCeti.LieTypeIndex.characteristic_trialityD4] at h
    exact ex3_dvd27_trialityD4 q hv h
  | reeG2 m => exact ex3_dvd27_reeG2 m hv
  | suzuki m => simp [TauCeti.LieTypeIndex.characteristic_suzuki] at h
  | reeF4 m => simp [TauCeti.LieTypeIndex.characteristic_reeF4] at h
  | tits => simp [TauCeti.LieTypeIndex.characteristic_tits] at h

private theorem ex3_card_alt7 (h : 5 ≤ 7) :
    Nat.card (TauCeti.CFSGIndex.alternating 7 h).Group = 2520 := by
  show Nat.card (alternatingGroup (Fin 7)) = 2520
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  simp [Nat.factorial]

private theorem ex3_card_M22 :
    Nat.card (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.M22).Group = 443520 := by
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.M22.nonempty_mulEquiv
  have h1 := CFSG.Sporadic.Bridge.M22.tauCeti_finite_card_le.2
  have h2 := CFSG.Sporadic.Bridge.M22.le_card_native
  rw [Nat.card_congr e.toEquiv] at h2
  show Nat.card TauCeti.SporadicName.M22.Group = 443520
  omega

private theorem ex3_card_A2_mul (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.A 2 q).Valid)
    (hq : q.card % 9 = 4 ∨ q.card % 9 = 7) :
    Nat.card (TauCeti.CFSGIndex.lie ⟨.A 2 q, hv⟩).Group * 3 =
      q.card ^ 3 * ((q.card ^ 2 - 1) * (q.card ^ 3 - 1)) := by
  have hC := CFSG.AGLEmbedding.KFactProofs.CoverFive.statedClassicalModel_psl_of_typeA 2 q hv
    (MulEquiv.refl _)
  have hL : CFSG.Blueprint.LieModel (TauCeti.CFSGIndex.lie ⟨.A 2 q, hv⟩).Group .PSL 3 q.p
      q.exponent := Or.inl ⟨by decide, hC⟩
  obtain ⟨-, hmul, -⟩ := CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput _ .PSL 3
    q.p q.exponent hC.1 hL
  have hg : Nat.gcd 3 (q.card - 1) = 3 := Nat.gcd_eq_left (by omega)
  have hprod : ∏ i ∈ Finset.Icc 2 3, (q.card ^ i - 1) = (q.card ^ 2 - 1) * (q.card ^ 3 - 1) := by
    rw [show Finset.Icc 2 3 = {2, 3} from rfl, Finset.prod_pair (by norm_num)]
  have hnum : CFSG.ComponentClassification.CatLeaf.lieOrderNumerator .PSL 3 q.card =
      q.card ^ 3 * ∏ i ∈ Finset.Icc 2 3, (q.card ^ i - 1) := rfl
  have hden : CFSG.ComponentClassification.CatLeaf.lieOrderDivisor .PSL 3 q.card =
      Nat.gcd 3 (q.card - 1) := rfl
  rw [← TauCeti.PrimePower.card_def] at hmul
  rw [hden, hg, hnum, hprod] at hmul
  exact hmul

private theorem ex3_card_twistedA2_mul (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedA 2 q).Valid) (hq : q.card % 9 = 2 ∨ q.card % 9 = 5) :
    Nat.card (TauCeti.CFSGIndex.lie ⟨.twistedA 2 q, hv⟩).Group * 3 =
      q.card ^ 3 * ((q.card ^ 2 - 1) * (q.card ^ 3 + 1)) := by
  have hC := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv (MulEquiv.refl _)
  have hL : CFSG.Blueprint.LieModel (TauCeti.CFSGIndex.lie ⟨.twistedA 2 q, hv⟩).Group .PSU 3
      q.p q.exponent := Or.inl ⟨by decide, hC⟩
  obtain ⟨-, hmul, -⟩ := CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput _ .PSU 3
    q.p q.exponent hC.1 hL
  have hg : Nat.gcd 3 (q.card + 1) = 3 := Nat.gcd_eq_left (by omega)
  have hprod : ∏ i ∈ Finset.Icc 2 3, (if Even i then q.card ^ i - 1 else q.card ^ i + 1) =
      (q.card ^ 2 - 1) * (q.card ^ 3 + 1) := by
    rw [show Finset.Icc 2 3 = {2, 3} from rfl, Finset.prod_pair (by norm_num)]
    simp [Nat.even_iff]
  have hnum : CFSG.ComponentClassification.CatLeaf.lieOrderNumerator .PSU 3 q.card =
      q.card ^ 3 * ∏ i ∈ Finset.Icc 2 3, (if Even i then q.card ^ i - 1 else q.card ^ i + 1) :=
    rfl
  have hden : CFSG.ComponentClassification.CatLeaf.lieOrderDivisor .PSU 3 q.card =
      Nat.gcd 3 (q.card + 1) := rfl
  rw [← TauCeti.PrimePower.card_def] at hmul
  rw [hden, hg, hnum, hprod] at hmul
  exact hmul

private theorem ex3_A2_facts (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.A 2 q).Valid)
    (hq : q.card % 9 = 4 ∨ q.card % 9 = 7) :
    20160 ≤ Nat.card (TauCeti.CFSGIndex.lie ⟨.A 2 q, hv⟩).Group ∧
      ¬ 27 ∣ Nat.card (TauCeti.CFSGIndex.lie ⟨.A 2 q, hv⟩).Group := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hm := ex3_card_A2_mul q hv hq
  have hq4 : 4 ≤ q.card := by omega
  have h1 : 64 ≤ q.card ^ 3 := by
    calc 64 = 4 ^ 3 := by norm_num
      _ ≤ q.card ^ 3 := Nat.pow_le_pow_left hq4 3
  have h2 : 16 ≤ q.card ^ 2 := by
    calc 16 = 4 ^ 2 := by norm_num
      _ ≤ q.card ^ 2 := Nat.pow_le_pow_left hq4 2
  have hA : 15 ≤ q.card ^ 2 - 1 := by omega
  have hB : 63 ≤ q.card ^ 3 - 1 := by omega
  have hC : 64 * (15 * 63) ≤ q.card ^ 3 * ((q.card ^ 2 - 1) * (q.card ^ 3 - 1)) :=
    Nat.mul_le_mul h1 (Nat.mul_le_mul hA hB)
  have hlow : 20160 ≤ Nat.card (TauCeti.CFSGIndex.lie ⟨.A 2 q, hv⟩).Group := by omega
  refine ⟨hlow, ?_⟩
  have hpv := CFSG.HardMathSupport.Foote.Coordinator.padicValNat_card_typeA_two q hv
    (by omega) (by omega)
  have hne : Nat.card (TauCeti.CFSGIndex.lie ⟨.A 2 q, hv⟩).Group ≠ 0 := by omega
  intro h27
  have h33 : 3 ^ 3 ∣ Nat.card (TauCeti.CFSGIndex.lie ⟨.A 2 q, hv⟩).Group := by
    norm_num
    exact h27
  have := (padicValNat_dvd_iff_le hne).1 h33
  omega

private theorem ex3_U2_facts (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedA 2 q).Valid) (hq : q.card % 9 = 2 ∨ q.card % 9 = 5) :
    126000 ≤ Nat.card (TauCeti.CFSGIndex.lie ⟨.twistedA 2 q, hv⟩).Group ∧
      ¬ 27 ∣ Nat.card (TauCeti.CFSGIndex.lie ⟨.twistedA 2 q, hv⟩).Group := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hm := ex3_card_twistedA2_mul q hv hq
  have hstd := ((TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1)
  have hq5 : 5 ≤ q.card := by have := hstd.2 rfl; omega
  have h1 : 125 ≤ q.card ^ 3 := by
    calc 125 = 5 ^ 3 := by norm_num
      _ ≤ q.card ^ 3 := Nat.pow_le_pow_left hq5 3
  have h2 : 25 ≤ q.card ^ 2 := by
    calc 25 = 5 ^ 2 := by norm_num
      _ ≤ q.card ^ 2 := Nat.pow_le_pow_left hq5 2
  have hA : 24 ≤ q.card ^ 2 - 1 := by omega
  have hB : 126 ≤ q.card ^ 3 + 1 := by omega
  have hC : 125 * (24 * 126) ≤ q.card ^ 3 * ((q.card ^ 2 - 1) * (q.card ^ 3 + 1)) :=
    Nat.mul_le_mul h1 (Nat.mul_le_mul hA hB)
  have hlow : 126000 ≤ Nat.card (TauCeti.CFSGIndex.lie ⟨.twistedA 2 q, hv⟩).Group := by omega
  refine ⟨hlow, ?_⟩
  have hpv := CFSG.HardMathSupport.Foote.Coordinator.padicValNat_card_twistedA_two q hv
    (by omega) (by omega)
  have hne : Nat.card (TauCeti.CFSGIndex.lie ⟨.twistedA 2 q, hv⟩).Group ≠ 0 := by omega
  intro h27
  have h33 : 3 ^ 3 ∣ Nat.card (TauCeti.CFSGIndex.lie ⟨.twistedA 2 q, hv⟩).Group := by
    norm_num
    exact h27
  have := (padicValNat_dvd_iff_le hne).1 h33
  omega


private theorem ex3_card_A18 (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.A 1 q).Valid)
    (hq : q.card = 8) : Nat.card (TauCeti.CFSGIndex.lie ⟨.A 1 q, hv⟩).Group = 504 := by
  have hC := CFSG.AGLEmbedding.KFactProofs.CoverFive.statedClassicalModel_psl_of_typeA 1 q hv
    (MulEquiv.refl _)
  have hL : CFSG.Blueprint.LieModel (TauCeti.CFSGIndex.lie ⟨.A 1 q, hv⟩).Group .PSL (1 + 1)
      q.p q.exponent := Or.inl ⟨by decide, hC⟩
  obtain ⟨-, hmul, -⟩ := CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput _ .PSL
    (1 + 1) q.p q.exponent hC.1 hL
  rw [← TauCeti.PrimePower.card_def, hq] at hmul
  have hden : CFSG.ComponentClassification.CatLeaf.lieOrderDivisor .PSL (1 + 1) 8 = 1 := rfl
  have hnum : CFSG.ComponentClassification.CatLeaf.lieOrderNumerator .PSL (1 + 1) 8 = 504 := rfl
  rw [hden, hnum] at hmul
  omega

private theorem ex3_card_U42 (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedA 3 q).Valid) (hq : q.card = 2) :
    Nat.card (TauCeti.CFSGIndex.lie ⟨.twistedA 3 q, hv⟩).Group = 25920 := by
  have hC := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 3 q hv (MulEquiv.refl _)
  have hL : CFSG.Blueprint.LieModel (TauCeti.CFSGIndex.lie ⟨.twistedA 3 q, hv⟩).Group .PSU
      (3 + 1) q.p q.exponent := Or.inl ⟨by decide, hC⟩
  obtain ⟨-, hmul, -⟩ := CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput _ .PSU
    (3 + 1) q.p q.exponent hC.1 hL
  rw [← TauCeti.PrimePower.card_def, hq] at hmul
  have hden : CFSG.ComponentClassification.CatLeaf.lieOrderDivisor .PSU (3 + 1) 2 = 1 := rfl
  have hnum : CFSG.ComponentClassification.CatLeaf.lieOrderNumerator .PSU (3 + 1) 2 = 25920 :=
    rfl
  rw [hden, hnum] at hmul
  omega

private theorem ex3_exc_lie_facts (d : TauCeti.ValidLieTypeIndex)
    (h : excIndex (TauCeti.CFSGIndex.lie d)) :
    20160 ≤ Nat.card d.Group ∧ ¬ 27 ∣ Nat.card d.Group := by
  obtain ⟨d, hv⟩ := d
  cases d with
  | A r q =>
    rcases r with _ | _ | _ | r
    · exact False.elim h
    · exact False.elim h
    · exact ex3_A2_facts q hv h
    · exact False.elim h
  | twistedA r q =>
    rcases r with _ | _ | _ | r
    · exact False.elim h
    · exact False.elim h
    · have := ex3_U2_facts q hv h
      exact ⟨le_trans (by norm_num) this.1, this.2⟩
    · exact False.elim h
  | _ => exact False.elim h

private theorem ex3_chev3_facts (S : Type) [Group S] (hch : CFSG.Yardstones.Md0ec50421ce4.IsChevSimple 3 S) :
    catalogIs S (fun k => ∃ h, k = TauCeti.CFSGIndex.alternating 6 h) ∨ 27 ∣ Nat.card S ∨
      Nat.card S = 504 ∨ Nat.card S = 25920 := by
  rcases hch with ⟨j, hj, ⟨eJ⟩⟩ | ⟨j, hj, ⟨eJ⟩⟩
  · rcases j with ⟨p, hp⟩ | ⟨n, hn⟩ | ⟨d⟩ | s
    · exact False.elim hj
    · exact False.elim hj
    · right; left
      have hS : Nat.card S = Nat.card d.Group := Nat.card_congr eJ.toEquiv
      rw [hS]
      exact ex3_dvd27_char3 d hj
    · exact False.elim hj
  · rcases j with ⟨p, hp⟩ | ⟨n, hn⟩ | ⟨d⟩ | s
    · exact False.elim hj
    · rcases hj with ⟨-, h⟩ | ⟨h6, -⟩ | ⟨-, h⟩
      · exfalso
        omega
      · subst h6
        exact Or.inl ⟨TauCeti.CFSGIndex.alternating 6 hn, ⟨hn, rfl⟩, ⟨eJ⟩⟩
      · exfalso
        omega
    · obtain ⟨d, hv⟩ := d
      cases d with
      | A r q =>
        rcases r with _ | _ | r
        · exact False.elim hj
        · rcases hj with ⟨-, h⟩ | ⟨h8, -⟩
          · exfalso
            omega
          · right; right; left
            exact (Nat.card_congr eJ.toEquiv).trans (ex3_card_A18 q hv h8)
        · exact False.elim hj
      | twistedA r q =>
        rcases r with _ | _ | _ | _ | r
        · exact False.elim hj
        · exact False.elim hj
        · rcases hj with ⟨-, h⟩
          exfalso
          omega
        · rcases hj with ⟨h2, -⟩
          right; right; right
          exact (Nat.card_congr eJ.toEquiv).trans (ex3_card_U42 q hv h2)
        · exact False.elim hj
      | _ => exact False.elim hj
    · exact False.elim hj

theorem kdExcChev3_holds : KDExcChev3 := by
  intro S _ hex hch
  obtain ⟨i, hi, ⟨eI⟩⟩ := hex
  rcases i with ⟨p, hp⟩ | ⟨n, hn⟩ | ⟨d⟩ | s
  · exact False.elim hi
  · rcases hi with rfl | rfl
    · exact ⟨TauCeti.CFSGIndex.alternating 6 hn, ⟨hn, rfl⟩, ⟨eI⟩⟩
    · have hS : Nat.card S = 2520 := (Nat.card_congr eI.toEquiv).trans (ex3_card_alt7 hn)
      rcases ex3_chev3_facts S hch with hg | h | h | h
      · exact hg
      · omega
      · omega
      · omega
  · obtain ⟨h20160, hnd⟩ := ex3_exc_lie_facts d hi
    have hS : Nat.card S = Nat.card d.Group := Nat.card_congr eI.toEquiv
    rcases ex3_chev3_facts S hch with hg | h | h | h
    · exact hg
    · omega
    · omega
    · omega
  · have hs : s = TauCeti.SporadicName.M22 := hi
    subst hs
    have hS : Nat.card S = 443520 := (Nat.card_congr eI.toEquiv).trans ex3_card_M22
    rcases ex3_chev3_facts S hch with hg | h | h | h
    · exact hg
    · omega
    · omega
    · omega

end CFSG.LocalAnalysis.GLTheoremA
