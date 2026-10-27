module

public import CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.Arith
public import CFSG.Open.GriessAllModelsStatement
public import CFSG.RankThree.PerfectCover.HopfFormula
public import CFSG.RankThree.PerfectCover.HopfCentralCoversSetup
public import CFSG.GH74.Generic.GKFCover
public import CFSG.RankThree.PartTwo.Census.Classical.Bridges
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinBOdd
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDOdd
public import CFSG.LocalAnalysis.AGLEmbedding.CompCenterNineOrbit

public section

namespace CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Assembly.RankThreeEven CFSG.Models
  CFSG.Blueprint.Multiplier TauCeti
open CFSG.RankThree.PerfectCover (hopfMultiplier hopfMultiplierToKer hopfMultiplierToKer_surjective
  centralQuotientMap centralQuotientMap_surjective centralQuotientMap_ker hopfMultiplier_le_center
  hopfMultiplierEquivGriess)
open CFSG.Open (GriessAllModelsStatement)

theorem lieModel_of_classical {X : Type} [Group X] {t : StatedLieTag} {n p f : ℕ}
    (h : StatedClassicalModel X t n p f) : LieModel X t n p f :=
  ⟨h.1, Or.inl h⟩

theorem lieModel_lie {t : StatedLieTag} {p f : ℕ} (h : StatedLieAdmissible t 0 p f)
    (d : ValidLieTypeIndex) (hd : NamesTag d.1 t p f) :
    LieModel (CFSGIndex.lie d).Group t 0 p f :=
  ⟨h, Or.inr ⟨rfl, d, hd, ⟨MulEquiv.refl _⟩⟩⟩

theorem lieModel_typeA (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.A r q).Valid) :
    LieModel (CFSGIndex.lie ⟨.A r q, hv⟩).Group .PSL (r + 1) q.p q.exponent := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hrange := (LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1
  have hr : 1 ≤ r := hrange.1
  have h4 : r = 1 → 4 ≤ q.p ^ q.exponent := by
    simpa only [PrimePower.card_def] using hrange.2
  have hadm : StatedLieAdmissible .PSL (r + 1) q.p q.exponent := by
    refine ⟨q.prime_p, q.exponent_pos, by omega, ?_, ?_⟩
    · intro h
      simp only [Prod.mk.injEq] at h
      have := h4 (by omega)
      omega
    · intro h
      simp only [Prod.mk.injEq] at h
      have := h4 (by omega)
      omega
  refine ⟨hadm, Or.inl ⟨hadm, GaloisField q.p q.exponent, inferInstance, inferInstance,
    GaloisField.card _ _ q.exponent_pos.ne', ⟨?_⟩⟩⟩
  exact (((CFSG.RankThree.PartTwo.Census.typeAGroupEquivProjSL r q hv).trans
    (MulEquiv.subgroupCongr (CFSG.RankThree.PartTwo.Census.projImage_statedSL _ _).symm)).trans
    (CFSG.RankThree.PartTwo.Census.statedProjEquivProjImage _).symm)

theorem exists_lieModel (d : ValidLieTypeIndex) :
    ∃ (t : StatedLieTag) (n p f : ℕ), LieModel (CFSGIndex.lie d).Group t n p f := by
  obtain ⟨d, hv⟩ := d
  have hrange := (LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1
  cases d with
  | A r q => exact ⟨_, _, _, _, lieModel_typeA r q hv⟩
  | twistedA r q =>
    exact ⟨_, _, _, _, lieModel_of_classical
      (CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv (MulEquiv.refl _))⟩
  | B r q =>
    have hr : 2 ≤ r := hrange.1
    rcases (show r = 2 ∨ 3 ≤ r by omega) with rfl | hr3
    · exact ⟨_, _, _, _, lieModel_of_classical
        (CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv (MulEquiv.refl _))⟩
    · by_cases hp : q.p = 2
      · exact ⟨_, _, _, _, lieModel_of_classical
          (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even r q hv hp hr3
            (MulEquiv.refl _))⟩
      · exact ⟨_, _, _, _, lieModel_of_classical
          (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_odd r q hv hp hr3
            (MulEquiv.refl _))⟩
  | C r q =>
    exact ⟨_, _, _, _, lieModel_of_classical
      (CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeC r q hv (MulEquiv.refl _))⟩
  | D r q =>
    exact ⟨_, _, _, _, lieModel_of_classical
      (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD r q hv (MulEquiv.refl _))⟩
  | twistedD r q =>
    exact ⟨_, _, _, _, lieModel_of_classical
      (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD r q hv (MulEquiv.refl _))⟩
  | E6 q =>
    exact ⟨_, _, _, _, lieModel_lie (t := .E6) ⟨q.prime_p, q.exponent_pos, rfl⟩ ⟨.E6 q, hv⟩
      ⟨rfl, rfl⟩⟩
  | E7 q =>
    exact ⟨_, _, _, _, lieModel_lie (t := .E7) ⟨q.prime_p, q.exponent_pos, rfl⟩ ⟨.E7 q, hv⟩
      ⟨rfl, rfl⟩⟩
  | E8 q =>
    exact ⟨_, _, _, _, lieModel_lie (t := .E8) ⟨q.prime_p, q.exponent_pos, rfl⟩ ⟨.E8 q, hv⟩
      ⟨rfl, rfl⟩⟩
  | F4 q =>
    exact ⟨_, _, _, _, lieModel_lie (t := .F4) ⟨q.prime_p, q.exponent_pos, rfl⟩ ⟨.F4 q, hv⟩
      ⟨rfl, rfl⟩⟩
  | G2 q =>
    have h3q : 3 ≤ q.p ^ q.exponent := by simpa only [PrimePower.card_def] using hrange
    exact ⟨_, _, _, _, lieModel_lie (t := .G2) ⟨q.prime_p, q.exponent_pos, rfl, h3q⟩ ⟨.G2 q, hv⟩
      ⟨rfl, rfl⟩⟩
  | twistedE6 q =>
    exact ⟨_, _, _, _, lieModel_lie (t := .twistedE6) ⟨q.prime_p, q.exponent_pos, rfl⟩
      ⟨.twistedE6 q, hv⟩ ⟨rfl, rfl⟩⟩
  | trialityD4 q =>
    exact ⟨_, _, _, _, lieModel_lie (t := .trialityD4) ⟨q.prime_p, q.exponent_pos, rfl⟩
      ⟨.trialityD4 q, hv⟩ ⟨rfl, rfl⟩⟩
  | suzuki m =>
    have hm1 : 1 ≤ m := hrange
    exact ⟨_, _, _, _, lieModel_lie (t := .twistedB2) (p := 2) (f := 2 * m + 1)
      ⟨Nat.prime_two, by omega, rfl, rfl, ⟨m, rfl⟩, by omega⟩ ⟨.suzuki m, hv⟩ ⟨rfl, rfl⟩⟩
  | reeG2 m =>
    have hm1 : 1 ≤ m := hrange
    exact ⟨_, _, _, _, lieModel_lie (t := .twistedG2) (p := 3) (f := 2 * m + 1)
      ⟨Nat.prime_three, by omega, rfl, rfl, ⟨m, rfl⟩, by omega⟩ ⟨.reeG2 m, hv⟩ ⟨rfl, rfl⟩⟩
  | reeF4 m =>
    have hm1 : 1 ≤ m := hrange
    exact ⟨_, _, _, _, lieModel_lie (t := .twistedF4) (p := 2) (f := 2 * m + 1)
      ⟨Nat.prime_two, by omega, rfl, rfl, ⟨m, rfl⟩, by omega⟩ ⟨.reeF4 m, hv⟩ ⟨rfl, rfl⟩⟩
  | tits =>
    exact ⟨_, _, _, _, lieModel_lie (t := .Tits) (p := 2) (f := 1)
      ⟨Nat.prime_two, le_rfl, rfl, rfl, rfl⟩ ⟨.tits, hv⟩ ⟨rfl, rfl⟩⟩

theorem card_torsion_center_le {K S : Type} [Group K] [Finite K] [Group S]
    (hq : CFSG.Open.IsQuasisimple K) (e : K ⧸ Subgroup.center K ≃* S) [Finite (hopfMultiplier S)]
    (r : ℕ) :
    Nat.card {z : Subgroup.center K // z ^ r = 1} ≤
      Nat.card {m : hopfMultiplier S // m ^ r = 1} := by
  have : Group.IsPerfect K := ⟨hq.1⟩
  have hker := centralQuotientMap_ker e
  have hle := CFSG.AGLEmbedding.CompCenterNine.card_pow_eq_one_le_of_surjective
    (fun a b : hopfMultiplier S =>
      Subtype.ext (Subgroup.mem_center_iff.mp (hopfMultiplier_le_center b.2) a))
    (hopfMultiplierToKer (centralQuotientMap e) (centralQuotientMap_surjective e) hker.le)
    (hopfMultiplierToKer_surjective _ _ _) r
  refine le_trans (le_of_eq (Nat.card_congr ((MulEquiv.subgroupCongr hker.symm).toEquiv.subtypeEquiv
    fun z => ?_))) hle
  change z ^ r = 1 ↔ MulEquiv.subgroupCongr hker.symm z ^ r = 1
  rw [← map_pow, MulEquiv.map_eq_one_iff]

theorem finite_and_torsion_le (hGA : GriessAllModelsStatement) {X : Type} [Group X]
    {t : StatedLieTag} {n p f : ℕ} (hm : LieModel X t n p f) {r : ℕ} (hr : r.Prime) :
    Finite (hopfMultiplier X) ∧
      Nat.card {m : hopfMultiplier X // m ^ r = 1} ≤ torsBound r t n p f := by
  obtain ⟨-, ⟨eg⟩⟩ := hGA X t n p f hm
  have ha := genericOrders_fst_pos hm.1
  obtain ⟨hb, -⟩ := genericOrders_snd_le t n p f
  obtain ⟨⟨hc, -⟩, ⟨hd, -⟩⟩ := exceptionalOrders_le t n p f
  have : NeZero (genericOrders t n p f).1 := ⟨ha.ne'⟩
  have : NeZero (genericOrders t n p f).2 := ⟨hb.ne'⟩
  have : NeZero (exceptionalOrders t n p f).1 := ⟨hc.ne'⟩
  have : NeZero (exceptionalOrders t n p f).2 := ⟨hd.ne'⟩
  let e : hopfMultiplier X ≃* generic t n p f × exceptional t n p f :=
    (hopfMultiplierEquivGriess X).symm.trans eg
  refine ⟨Finite.of_equiv _ e.symm.toEquiv, ?_⟩
  refine le_trans (le_of_eq (Nat.card_congr (e.toEquiv.subtypeEquiv fun m => ?_)))
    (card_pow_four_le hr ha hb hc hd)
  change m ^ r = 1 ↔ e m ^ r = 1
  rw [← map_pow, MulEquiv.map_eq_one_iff]

theorem finite_and_card_hopf (hGA : GriessAllModelsStatement) {X : Type} [Group X]
    {t : StatedLieTag} {n p f : ℕ} (hm : LieModel X t n p f) :
    Finite (hopfMultiplier X) ∧ Nat.card (hopfMultiplier X) =
      (genericOrders t n p f).1 * (genericOrders t n p f).2 *
        ((exceptionalOrders t n p f).1 * (exceptionalOrders t n p f).2) := by
  obtain ⟨-, ⟨eg⟩⟩ := hGA X t n p f hm
  have ha := genericOrders_fst_pos hm.1
  obtain ⟨hb, -⟩ := genericOrders_snd_le t n p f
  obtain ⟨⟨hc, -⟩, ⟨hd, -⟩⟩ := exceptionalOrders_le t n p f
  have : NeZero (genericOrders t n p f).1 := ⟨ha.ne'⟩
  have : NeZero (genericOrders t n p f).2 := ⟨hb.ne'⟩
  have : NeZero (exceptionalOrders t n p f).1 := ⟨hc.ne'⟩
  have : NeZero (exceptionalOrders t n p f).2 := ⟨hd.ne'⟩
  let e : hopfMultiplier X ≃* generic t n p f × exceptional t n p f :=
    (hopfMultiplierEquivGriess X).symm.trans eg
  refine ⟨Finite.of_equiv _ e.symm.toEquiv, ?_⟩
  rw [Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_prod, Nat.card_prod]
  simp

theorem center_pow_lcm (hGA : GriessAllModelsStatement) {K X : Type} [Group K] [Finite K]
    [Group X] (hq : CFSG.Open.IsQuasisimple K) (e : K ⧸ Subgroup.center K ≃* X)
    {t : StatedLieTag} {n p f : ℕ} (hm : LieModel X t n p f) (z : Subgroup.center K) :
    z ^ Nat.lcm (genericOrders t n p f).1 12 = 1 := by
  obtain ⟨-, ⟨eg⟩⟩ := hGA X t n p f hm
  let e' : hopfMultiplier X ≃* generic t n p f × exceptional t n p f :=
    (hopfMultiplierEquivGriess X).symm.trans eg
  have : Group.IsPerfect K := ⟨hq.1⟩
  have hker := centralQuotientMap_ker e
  have hsurj := hopfMultiplierToKer_surjective (centralQuotientMap e)
    (centralQuotientMap_surjective e) hker.le
  have hzk : (z : K) ∈ (centralQuotientMap e).ker := by rw [hker]; exact z.2
  obtain ⟨m, hm'⟩ := hsurj ⟨z, hzk⟩
  have hdvd : ∀ {x : ℕ}, x ∣ 12 ∨ x ∣ (genericOrders t n p f).1 →
      x ∣ Nat.lcm (genericOrders t n p f).1 12 := by
    rintro x (h | h)
    · exact h.trans (Nat.dvd_lcm_right _ _)
    · exact h.trans (Nat.dvd_lcm_left _ _)
  have hmN : m ^ Nat.lcm (genericOrders t n p f).1 12 = 1 := by
    apply e'.injective
    rw [map_pow, map_one]
    obtain ⟨hb1, hb2⟩ := genericOrders_snd_le t n p f
    obtain ⟨⟨hc1, hc2⟩, ⟨hd1, hd2⟩⟩ := exceptionalOrders_le t n p f
    have h12 : ∀ x : ℕ, 0 < x → x ≤ 4 → x ∣ 12 := fun x h0 h4 => by
      interval_cases x <;> norm_num
    refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_)
    · exact pow_eq_one_of_dvd_zmod (hdvd (Or.inr dvd_rfl)) _
    · exact pow_eq_one_of_dvd_zmod (hdvd (Or.inl (h12 _ hb1 (by omega)))) _
    · exact pow_eq_one_of_dvd_zmod (hdvd (Or.inl (h12 _ hc1 hc2))) _
    · exact pow_eq_one_of_dvd_zmod (hdvd (Or.inl (h12 _ hd1 hd2))) _
  have := congrArg (fun w : (centralQuotientMap e).ker => (w : K)) (show
    (hopfMultiplierToKer (centralQuotientMap e) (centralQuotientMap_surjective e) hker.le m) ^
      Nat.lcm (genericOrders t n p f).1 12 = 1 by rw [← map_pow, hmN, map_one])
  rw [hm'] at this
  apply Subtype.ext
  simpa using this

theorem center_torsion_le (hGA : GriessAllModelsStatement) {K X : Type} [Group K] [Finite K]
    [Group X] (hq : CFSG.Open.IsQuasisimple K) (e : K ⧸ Subgroup.center K ≃* X) {t : StatedLieTag}
    {n p f : ℕ} (hm : LieModel X t n p f) {r : ℕ} (hr : r.Prime) :
    Nat.card {z : Subgroup.center K // z ^ r = 1} ≤ torsBound r t n p f := by
  obtain ⟨hfin, hM⟩ := finite_and_torsion_le hGA hm hr
  have := hfin
  exact (card_torsion_center_le hq e r).trans hM

theorem center_dvd_table (hGA : GriessAllModelsStatement) {K X : Type} [Group K] [Finite K]
    [Group X] (hq : CFSG.IsQuasisimple K) (e : K ⧸ Subgroup.center K ≃* X) {t : StatedLieTag}
    {n p f : ℕ} (hm : LieModel X t n p f) :
    Nat.card (Subgroup.center K) ∣ (genericOrders t n p f).1 * (genericOrders t n p f).2 *
      ((exceptionalOrders t n p f).1 * (exceptionalOrders t n p f).2) := by
  obtain ⟨-, ⟨eg⟩⟩ := hGA X t n p f hm
  let e' : hopfMultiplier X ≃* generic t n p f × exceptional t n p f :=
    (hopfMultiplierEquivGriess X).symm.trans eg
  have h1 := CFSG.GH74.Generic.card_center_dvd_hopfMultiplier hq e
  rw [Nat.card_congr e'.toEquiv, Nat.card_prod, Nat.card_prod, Nat.card_prod] at h1
  simpa [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod] using h1

end CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier
