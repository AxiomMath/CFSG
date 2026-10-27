module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1AlphaList3
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1AlphaListE1
public import CFSG.RankThree.PartOne.N143.HighEven
public import CFSG.RankThree.PartOne.N143.O7
import CFSG.RankThree.PartOne.N143.Inspect613Even
import CFSG.RankThree.PartOne.S11c.HigherLinearSmall
import CFSG.RankThree.PartOne.S11c.HigherUnitarySmall
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
import CFSG.RankThree.OddKernel.ThreeComplementQuotient

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven TauCeti Subgroup
open CFSG.Blueprint CFSG.RankThree.PartOne.N143
open CFSG.RankThree.PartOne (ActualCoverETypeRankThreeOnlyE6FieldTwo)
open CFSG.RankThree.PartTwo.Sec4.Census (IsThreeCenterCover TripleCoverLie)

theorem false_of_noOddCentralCoverFor {P : CFSGIndex → Prop} (h : NoOddCentralCoverFor P)
    {K : Type} [Group K] [Finite K] (hK : CFSG.IsKGroup K) (hq : CFSG.IsQuasisimple K)
    (he : CFSG.twoLocalOddRank K ≤ 3) (hZ : IsPGroup 3 (Subgroup.center K))
    (h3 : 3 ∣ Nat.card (Subgroup.center K)) {i : CFSGIndex} (hi : P i)
    (e : K ⧸ Subgroup.center K ≃* i.Group) : False := by
  have : IsSimpleGroup (K ⧸ Subgroup.center K) := hq.2.1
  have hker : (QuotientGroup.mk' (Subgroup.center K)).ker = Subgroup.center K :=
    QuotientGroup.ker_mk' _
  refine h K hK hq.1 ?_ (K ⧸ Subgroup.center K) hq.2.2 (QuotientGroup.mk' (Subgroup.center K))
    (QuotientGroup.mk'_surjective _) hker.le (by rw [hker]; exact hZ) (by rw [hker]; exact h3)
    ⟨i, hi, ⟨e⟩⟩
  rw [CFSG.RankThree.OddKernel.evenRank_eq_twoLocalOddRank]
  exact he

@[expose] def IsLieHighOddIndex : CFSGIndex → Prop
  | .lie ⟨.A r q, _⟩ => 5 ≤ r ∧ 3 ∣ r + 1 ∧ 3 ∣ q.card - 1 ∧ q.p ≠ 2
  | .lie ⟨.twistedA r q, _⟩ => 5 ≤ r ∧ 3 ∣ r + 1 ∧ 3 ∣ q.card + 1 ∧ q.p ≠ 2
  | _ => False

theorem noOddCentralCoverFor_lieHighOdd : NoOddCentralCoverFor IsLieHighOddIndex := by
  intro Y _ _ hK hperf he S _ _ _ hnonab φ hφ hcent h3 h3dvd ⟨i, hi, ⟨e⟩⟩
  obtain ⟨hker, hYq, ⟨hcongr⟩⟩ := central_cover_quasisimple hperf hnonab φ hφ hcent
  cases i with
  | cyclic p hp => exact hi.elim
  | alternating n hn => exact hi.elim
  | sporadic s => exact hi.elim
  | lie d =>
    obtain ⟨dd, hv⟩ := d
    cases dd with
    | A r q =>
      obtain ⟨h5, h3r, hq3, hq2⟩ : 5 ≤ r ∧ 3 ∣ r + 1 ∧ 3 ∣ q.card - 1 ∧ q.p ≠ 2 := hi
      have hp3 : q.p ≠ 3 := ne_three_of_dvd_pow_sub_one_or_add_one q.exponent_pos
        (Or.inl (by simpa [PrimePower.card_def] using hq3))
      have eM : (↥(⊤ : Subgroup Y) ⧸ center ↥(⊤ : Subgroup Y)) ≃*
          (CFSGIndex.lie ⟨.A r q, hv⟩).Group := ((topCenterEquiv Y).trans hcongr).trans e
      have hmod := statedClassicalModel_of_isoLie_A hv eM
      have hrank : localRank q.p Y ≤ 3 :=
        (CFSG.RankThree.OddKernel.localRank_le_evenRank q.prime_p hq2).trans he
      have := CFSG.RankThree.PartOne.linear_small_parameters (X := Y) (Y := ⊤) (n := r + 1)
        (ℓ := q.p) (f := q.exponent) (by omega) q.prime_p hq2 hmod hrank
      rcases this.1 with h | ⟨h, -⟩
      · omega
      · exact hp3 h
    | twistedA r q =>
      obtain ⟨h5, h3r, hq3, hq2⟩ : 5 ≤ r ∧ 3 ∣ r + 1 ∧ 3 ∣ q.card + 1 ∧ q.p ≠ 2 := hi
      have hp3 : q.p ≠ 3 := ne_three_of_dvd_pow_sub_one_or_add_one q.exponent_pos
        (Or.inr (by simpa [PrimePower.card_def] using hq3))
      have eM : (↥(⊤ : Subgroup Y) ⧸ center ↥(⊤ : Subgroup Y)) ≃*
          (CFSGIndex.lie ⟨.twistedA r q, hv⟩).Group := ((topCenterEquiv Y).trans hcongr).trans e
      have hmod := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv eM
      have hrank : localRank q.p Y ≤ 3 :=
        (CFSG.RankThree.OddKernel.localRank_le_evenRank q.prime_p hq2).trans he
      have := CFSG.RankThree.PartOne.unitary_small_parameters (X := Y) (Y := ⊤) (n := r + 1)
        (ℓ := q.p) (f := q.exponent) (by omega) q.prime_p hq2 hmod hrank
      rcases this.1 with h | ⟨h, -⟩
      · omega
      · exact hp3 h
    | _ => exact hi.elim

theorem noOddCentralCoverFor_lieE6 (hE : ActualCoverETypeRankThreeOnlyE6FieldTwo)
    (hB : CFSG.TauCetiBridge.Even.ChevalleyBridgesAll) : NoOddCentralCoverFor IsLieE6Index := by
  intro Y _ _ hK hperf he S _ _ _ hnonab φ hφ hcent h3 h3dvd ⟨i, hi, ⟨e⟩⟩
  obtain ⟨hker, hYq, ⟨hcongr⟩⟩ := central_cover_quasisimple hperf hnonab φ hφ hcent
  have he' : CFSG.twoLocalOddRank Y ≤ 3 := by
    rw [← CFSG.RankThree.OddKernel.evenRank_eq_twoLocalOddRank]
    exact he
  cases i with
  | cyclic p hp => exact hi.elim
  | alternating n hn => exact hi.elim
  | sporadic s => exact hi.elim
  | lie d =>
    obtain ⟨dd, hv⟩ := d
    cases dd with
    | E6 q =>
      have hq3 : 3 ∣ q.card - 1 := hi
      have : Fact q.p.Prime := ⟨q.prime_p⟩
      have hcard : Nat.card (GaloisField q.p q.exponent) = q.card := by
        rw [GaloisField.card q.p q.exponent q.exponent_pos.ne', PrimePower.card_def]
      obtain ⟨br⟩ := hB.e6 q hv (GaloisField q.p q.exponent) hcard
      have hmod : CFSG.Blueprint.ChevalleyExceptionalModel
          (↥(⊤ : Subgroup Y) ⧸ center ↥(⊤ : Subgroup Y)) .E6 q.p q.exponent :=
        ⟨⟨q.prime_p, q.exponent_pos, rfl⟩, GaloisField q.p q.exponent, inferInstance, inferInstance,
          by rw [hcard, PrimePower.card_def],
          ⟨(((topCenterEquiv Y).trans hcongr).trans e).trans br.symm⟩⟩
      obtain ⟨-, hp2, hf1⟩ := hE Y he' ⊤ q.p q.exponent q.prime_p q.exponent_pos .E6
        (Or.inl rfl) hmod
      have : q.card = 2 := by rw [PrimePower.card_def, hp2, hf1]; norm_num
      rw [this] at hq3
      omega
    | twistedE6 q =>
      have hq3 : 3 ∣ q.card + 1 := hi
      have : Fact q.p.Prime := ⟨q.prime_p⟩
      have hcard : Nat.card (GaloisField q.p (q.exponent * 2)) = q.card ^ 2 := by
        rw [GaloisField.card q.p (q.exponent * 2) (by have := q.exponent_pos; omega),
          PrimePower.card_def, pow_mul]
      obtain ⟨br⟩ := hB.twistedE6 q hv (GaloisField q.p (q.exponent * 2)) hcard
        (iterateFrobenius (GaloisField q.p (q.exponent * 2)) q.p q.exponent)
        (fun x => by rw [iterateFrobenius_def, PrimePower.card_def])
      have hmod : CFSG.Blueprint.ChevalleyExceptionalModel
          (↥(⊤ : Subgroup Y) ⧸ center ↥(⊤ : Subgroup Y)) .twistedE6 q.p q.exponent :=
        ⟨⟨q.prime_p, q.exponent_pos, rfl⟩, GaloisField q.p (q.exponent * 2), inferInstance,
          inferInstance, by rw [hcard, PrimePower.card_def]; rfl,
          iterateFrobenius (GaloisField q.p (q.exponent * 2)) q.p q.exponent,
          fun c => by rw [iterateFrobenius_def],
          ⟨(((topCenterEquiv Y).trans hcongr).trans e).trans br.symm⟩⟩
      obtain ⟨h, -, -⟩ := hE Y he' ⊤ q.p q.exponent q.prime_p q.exponent_pos .twistedE6
        (Or.inr (Or.inr (Or.inr rfl))) hmod
      exact absurd h (by decide)
    | _ => exact hi.elim

@[expose] def KFactLiftU43 : Prop :=
  ∀ (q : PrimePower) (hv : (LieTypeIndex.twistedA 3 q).Valid), q.card = 3 →
    HasLiftableTriple (CFSGIndex.lie ⟨.twistedA 3 q, hv⟩).Group

@[expose] def KFactLiftG23 : Prop :=
  ∀ (q : PrimePower) (hv : (LieTypeIndex.G2 q).Valid), q.card = 3 →
    HasLiftableTriple (CFSGIndex.lie ⟨.G2 q, hv⟩).Group

@[expose] def KFactLiftJ3 : Prop :=
  HasLiftableTriple (CFSGIndex.sporadic .J3).Group

@[expose] def KFactLiftMcL : Prop :=
  HasLiftableTriple (CFSGIndex.sporadic .McL).Group

structure KFactAlphaLifts : Prop where
  u43 : KFactLiftU43
  g23 : KFactLiftG23
  j3 : KFactLiftJ3
  mcl : KFactLiftMcL

theorem isLinThreeCover3_of_lieCover (hTC : TripleCoverLie)
    (hE : ActualCoverETypeRankThreeOnlyE6FieldTwo)
    (hB : CFSG.TauCetiBridge.Even.ChevalleyBridgesAll) (hL : KFactAlphaLifts)
    {K : Type} [Group K] [Finite K] (hK : CFSG.IsKGroup K) (hq : CFSG.IsQuasisimple K)
    (he : CFSG.twoLocalOddRank K ≤ 3) (hm : Open.pRank 3 (⊤ : Subgroup K) ≤ 3)
    (hZ : IsPGroup 3 (Subgroup.center K)) (h3 : 3 ∣ Nat.card (Subgroup.center K))
    (d : TauCeti.ValidLieTypeIndex) (e : K ⧸ Subgroup.center K ≃* (CFSGIndex.lie d).Group) :
    IsLinThreeCover3 d := by
  have hT := hTC d K ⟨hq, h3, ⟨e⟩⟩
  obtain ⟨d, hv⟩ := d
  cases d with
  | A r q =>
    have h31 : 3 ∣ r + 1 ∧ 3 ∣ q.card - 1 := hT
    have hr1 : 1 ≤ r :=
      ((LieTypeIndex.inStandardRange_iff _).mp ((LieTypeIndex.valid_iff _).mp hv).1).1
    rcases (show r = 2 ∨ 5 ≤ r by omega) with rfl | hr5
    · exact Or.inl ⟨q, rfl, h31.2⟩
    · exfalso
      by_cases hq2 : q.p = 2
      · exact false_of_noOddCentralCoverFor noOddCentralCoverFor_highEven hK hq he hZ h3
          (i := CFSGIndex.lie ⟨.A r q, hv⟩) ⟨hr5, h31.1, h31.2, hq2⟩ e
      · exact false_of_noOddCentralCoverFor noOddCentralCoverFor_lieHighOdd hK hq he hZ h3
          (i := CFSGIndex.lie ⟨.A r q, hv⟩) ⟨hr5, h31.1, h31.2, hq2⟩ e
  | twistedA r q =>
    have hr2 : 2 ≤ r :=
      LieTypeIndex.two_le_of_twistedA_inStandardRange ((LieTypeIndex.valid_iff _).mp hv).1
    have hT' : (3 ∣ r + 1 ∧ 3 ∣ q.card + 1) ∨ (r = 3 ∧ q.card = 3) := hT
    rcases hT' with ⟨h1, h2⟩ | ⟨rfl, hq3⟩
    · rcases (show r = 2 ∨ 5 ≤ r by omega) with rfl | hr5
      · exact Or.inr ⟨q, rfl, h2⟩
      · exfalso
        by_cases hq2 : q.p = 2
        · exact false_of_noOddCentralCoverFor noOddCentralCoverFor_highEven hK hq he hZ h3
            (i := CFSGIndex.lie ⟨.twistedA r q, hv⟩) ⟨hr5, h1, h2, hq2⟩ e
        · exact false_of_noOddCentralCoverFor noOddCentralCoverFor_lieHighOdd hK hq he hZ h3
            (i := CFSGIndex.lie ⟨.twistedA r q, hv⟩) ⟨hr5, h1, h2, hq2⟩ e
    · exfalso
      have h4 := HasLiftableTriple.four_le_pRank_of_cover (hL.u43 q hv hq3) e h3
      omega
  | B r q =>
    exfalso
    have hB3 : r = 3 ∧ q.card = 3 := hT
    exact false_of_noOddCentralCoverFor noOddCentralCoverFor_o7 hK hq he hZ h3
      (i := CFSGIndex.lie ⟨.B r q, hv⟩) hB3 e
  | G2 q =>
    exfalso
    have h4 := HasLiftableTriple.four_le_pRank_of_cover (hL.g23 q hv hT) e h3
    omega
  | E6 q =>
    exfalso
    exact false_of_noOddCentralCoverFor (noOddCentralCoverFor_lieE6 hE hB) hK hq he hZ h3
      (i := CFSGIndex.lie ⟨.E6 q, hv⟩) hT e
  | twistedE6 q =>
    exfalso
    exact false_of_noOddCentralCoverFor (noOddCentralCoverFor_lieE6 hE hB) hK hq he hZ h3
      (i := CFSGIndex.lie ⟨.twistedE6 q, hv⟩) hT e
  | _ => exact hT.elim

end CFSG.LocalAnalysis.RankThreeTheoremC
