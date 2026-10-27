module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.InputsSeitz3
public import CFSG.LieType.SeitzGeneration.QuasiHighClassical
import CFSG.RankThree.PartTwo.Sec4.Census.Item43Narrow
import CFSG.LocalAnalysis.AGLEmbeddingD2.FiveCover
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanCoverRankFiveCensus

public section

namespace CFSG.LieType.SeitzGeneration.QuasiHigh

open CFSG.Open CFSG.LieType.Seitz CFSG.LieType.SeitzGeneration CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsSeitz3 (SeitzQuasiHigh equivCenterQuot
  seitzHyperGamma_eq_top_of_plane not_d2Exc isLThreeFour_congr)
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ (ExcIndex IsSixIndex Seitz2310CubeSimple
  closure_eq_seitzHyperGamma)
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzBridgeAux (exists_noncomm_quot
  center_eq_bot_of_simple isQuasisimple_of_simple)
open CFSG.AGLEmbeddingD2 (KFactSeitzRankTwo)
open CFSG.ComponentClassification.TBLit (GriessMultipliersAllModels)

section Induced

variable {K : Type*} [Group K]

theorem quotAut_eq_quotientCenterAut' (f : MulAut K) : quotAut f = quotientCenterAut' K f := by
  ext s
  induction s using QuotientGroup.induction_on with
  | H x =>
    rw [quotAut_mk]
    simp [quotientCenterAut', QuotientGroup.congr_mk]

theorem quotientCenterAut'_conj (k : K) :
    quotientCenterAut' K (MulAut.conj k) = MulAut.conj (k : K ⧸ Subgroup.center K) := by
  ext s
  rw [← quotAut_eq_quotientCenterAut', quotAut_conj, MulAut.conj_apply]

theorem map_quotientCenterAut'_le_range_conj {E : Subgroup (MulAut K)}
    (hinn : E ≤ (MulAut.conj : K →* MulAut K).range) :
    E.map (quotientCenterAut' K) ≤
      (MulAut.conj : K ⧸ Subgroup.center K →* MulAut (K ⧸ Subgroup.center K)).range := by
  rintro _ ⟨f, hf, rfl⟩
  obtain ⟨k, rfl⟩ := hinn hf
  exact ⟨(k : K ⧸ Subgroup.center K), (quotientCenterAut'_conj k).symm⟩

theorem closure_fixed_quotAut_of_seitzHyperGamma (hperf : commutator K = ⊤) {p : ℕ}
    {E : Subgroup (MulAut K)} (h : seitzHyperGamma p (E.map (quotientCenterAut' K)) = ⊤) :
    (⊤ : Subgroup (K ⧸ Subgroup.center K)) ≤ Subgroup.closure
      {s : K ⧸ Subgroup.center K | ∃ F ≤ E, F.relIndex E = p ∧ ∀ f ∈ F, quotAut f s = s} := by
  have hinj := quotientCenterAut'_injective hperf
  rw [← h, ← closure_eq_seitzHyperGamma]
  refine Subgroup.closure_mono ?_
  rintro s ⟨F₀, hF₀, hrel, hs⟩
  refine ⟨F₀.comap (quotientCenterAut' K) ⊓ E, inf_le_right, ?_, ?_⟩
  · have hmap : (F₀.comap (quotientCenterAut' K) ⊓ E).map (quotientCenterAut' K) = F₀ := by
      apply le_antisymm
      · rintro _ ⟨x, ⟨hx, -⟩, rfl⟩
        exact hx
      · intro y hy
        obtain ⟨x, hx, rfl⟩ := hF₀ hy
        exact ⟨x, ⟨hy, hx⟩, rfl⟩
    rw [← Subgroup.relIndex_map_map_of_injective (F₀.comap (quotientCenterAut' K) ⊓ E) E hinj,
      hmap, hrel]
  · rintro f ⟨hf, -⟩
    rw [quotAut_eq_quotientCenterAut']
    exact hs _ hf

end Induced

@[expose] def SeitzSimpleAt (k : ℕ) : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S →
    (∃ a b : S, a * b ≠ b * a) → ∀ d : TauCeti.ValidLieTypeIndex,
    Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group) → p ≠ d.1.characteristic →
    ¬ (p = 3 ∧ IsLThreeFour S) →
    ∀ E : Subgroup (MulAut S), IsElemAbelian p E → Nat.card E = p ^ k →
      (¬ ExcIndex p d.1 ∨ (IsSixIndex d.1 ∧ E ≤ (MulAut.conj : S →* MulAut S).range)) →
        seitzHyperGamma p E = ⊤

@[expose] def SeitzCoverRest (k : ℕ) : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
    ∀ d : TauCeti.ValidLieTypeIndex,
    Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group) →
    p ≠ d.1.characteristic → ¬ (p = 3 ∧ IsLThreeFour (K ⧸ Subgroup.center K)) →
    p ∣ Nat.card (Subgroup.center K) →
    ∀ E : Subgroup (MulAut K), IsElemAbelian p E → Nat.card E = p ^ k →
      (¬ ExcIndex p d.1 ∨ (IsSixIndex d.1 ∧ E ≤ (MulAut.conj : K →* MulAut K).range)) →
      ¬ CoverScope d p E →
        seitzHyperGamma p E = ⊤

theorem ne_bot_of_card {G : Type*} [Group G] {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k)
    {E : Subgroup G} (hcard : Nat.card E = p ^ k) : E ≠ ⊥ := by
  rintro rfl
  rw [Subgroup.card_bot] at hcard
  have : 1 < p ^ k := Nat.one_lt_pow (by omega) hp.one_lt
  omega

theorem seitzSimpleAt_two (h2 : KFactSeitzRankTwo) : SeitzSimpleAt 2 := by
  intro p hp hp2 S _ _ hs hnab d hd hpd hL34 E hE hcard hex
  obtain ⟨e⟩ := hd
  have hZ := center_eq_bot_of_simple hs hnab
  exact seitzHyperGamma_eq_top_of_plane h2 hp hp2 hZ d ((equivCenterQuot hZ).symm.trans e) hpd
    (not_d2Exc d e (hex.imp_right And.left) hL34) hE hcard

theorem seitzSimpleAt_three (h3 : Seitz2310CubeSimple) : SeitzSimpleAt 3 :=
  fun p hp hp2 S _ _ hs hnab d hd hpd hL34 E hE hcard hex =>
    h3 p hp hp2 S hs hnab d hd hpd hL34 E hE hcard hex

theorem seitzHyperGamma_eq_top_of_simpleAt {k : ℕ} (hk : 1 ≤ k) (hS : SeitzSimpleAt k)
    (hC : SeitzCoverRest k) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {K : Type} [Group K]
    [Finite K] (hq : CFSG.Open.IsQuasisimple K) (d : TauCeti.ValidLieTypeIndex)
    (hd : Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group))
    (hpd : p ≠ d.1.characteristic) (hL34 : ¬ (p = 3 ∧ IsLThreeFour (K ⧸ Subgroup.center K)))
    {E : Subgroup (MulAut K)} (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ k)
    (hex : ¬ ExcIndex p d.1 ∨ (IsSixIndex d.1 ∧ E ≤ (MulAut.conj : K →* MulAut K).range)) :
    seitzHyperGamma p E = ⊤ := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hperf : commutator K = ⊤ := hq.1
  by_cases hz : p ∣ Nat.card (Subgroup.center K)
  · by_cases hIR : CoverScope d p E
    · exact seitzHyperGamma_eq_top_of_coverScope hperf hp hp2 hE (ne_bot_of_card hp hk hcard)
        hIR
    · exact hC p hp hp2 K hq d hd hpd hL34 hz E hE hcard hex hIR
  have hinj := quotientCenterAut'_injective hperf
  have hs : IsSimpleGroup (K ⧸ Subgroup.center K) := hq.2
  have hnab := exists_noncomm_quot hq
  have hĒ : IsElemAbelian p (E.map (quotientCenterAut' K)) :=
    CFSG.SectionRank.isElemAbelian_map hE _
  have hĒc : Nat.card (E.map (quotientCenterAut' K)) = p ^ k := by
    rw [Subgroup.card_map_of_injective hinj, hcard]
  have hex' : ¬ ExcIndex p d.1 ∨ (IsSixIndex d.1 ∧ E.map (quotientCenterAut' K) ≤
      (MulAut.conj : K ⧸ Subgroup.center K →* MulAut (K ⧸ Subgroup.center K)).range) :=
    hex.imp_right fun h => ⟨h.1, map_quotientCenterAut'_le_range_conj h.2⟩
  have hgen := hS p hp hp2 (K ⧸ Subgroup.center K) hs hnab d hd hpd hL34 _ hĒ hĒc hex'
  exact seitzHyperGamma_eq_top_of_coprime_center hperf hz (isPGroup_of_isElemAbelian hE)
    (closure_fixed_quotAut_of_seitzHyperGamma hperf hgen)

@[expose] def CoverIndex (p : ℕ) : TauCeti.LieTypeIndex → Prop
  | .A r q => p ∣ r + 1 ∧ p ∣ q.card - 1
  | .twistedA r q => p ∣ r + 1 ∧ p ∣ q.card + 1
  | .E6 q => p = 3 ∧ 3 ∣ q.card - 1
  | .twistedE6 q => p = 3 ∧ 3 ∣ q.card + 1
  | _ => False

theorem coverIndex_of_dvd_card_center (hGA : GriessMultipliersAllModels) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {K : Type} [Group K] [Finite K] (hq : CFSG.Open.IsQuasisimple K)
    (d : TauCeti.ValidLieTypeIndex) (e : K ⧸ Subgroup.center K ≃* Cat d)
    (hpd : p ≠ d.1.characteristic) (hz : p ∣ Nat.card (Subgroup.center K)) : CoverIndex p d.1 := by
  have hq' : CFSG.IsQuasisimple K :=
    CFSG.AGLEmbedding.KFactProofs.CoverFive.isQuasisimple_of_open hq
  have hchar3 : ∀ q : TauCeti.PrimePower, q.card = 3 → q.p = 3 := fun q hq3 =>
    (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_three).1 (by
      rw [← hq3, TauCeti.PrimePower.card_def]
      exact dvd_pow_self _ q.exponent_pos.ne')
  by_cases h3 : p = 3
  · subst h3
    have hidx := CFSG.RankThree.PartTwo.Sec4.Census.tripleCoverLie_of_griess hGA d K
      ⟨hq', hz, ⟨e⟩⟩
    obtain ⟨dd, hv⟩ := d
    cases dd with
    | A r q => exact hidx
    | twistedA r q =>
      rcases hidx with h | ⟨-, hq3⟩
      · exact h
      · exact (hpd (by rw [TauCeti.LieTypeIndex.characteristic_twistedA, hchar3 q hq3])).elim
    | B r q =>
      obtain ⟨-, hq3⟩ := hidx
      exact (hpd (by rw [TauCeti.LieTypeIndex.characteristic_B, hchar3 q hq3])).elim
    | G2 q => exact (hpd (by rw [TauCeti.LieTypeIndex.characteristic_G2, hchar3 q hidx])).elim
    | E6 q => exact ⟨rfl, hidx⟩
    | twistedE6 q => exact ⟨rfl, hidx⟩
    | _ => exact hidx.elim
  · have h5 : 5 ≤ p := by
      have h2 := hp.two_le
      have h4 : p ≠ 4 := by
        rintro rfl
        exact absurd hp (by norm_num)
      omega
    have hidx := CFSG.AGLEmbeddingD2.FiveCover.primeCoverLie_of_griess_of_five_le hGA hp h5 d hq'
      e hz
    obtain ⟨dd, hv⟩ := d
    cases dd with
    | A r q => exact hidx
    | twistedA r q => exact hidx
    | _ => exact hidx.elim

@[expose] def SeitzCoverFamRest (k : ℕ) : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
    ∀ d : TauCeti.ValidLieTypeIndex,
    Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group) →
    p ≠ d.1.characteristic → ¬ (p = 3 ∧ IsLThreeFour (K ⧸ Subgroup.center K)) →
    p ∣ Nat.card (Subgroup.center K) → CoverIndex p d.1 →
    ∀ E : Subgroup (MulAut K), IsElemAbelian p E → Nat.card E = p ^ k →
      (¬ ExcIndex p d.1 ∨ (IsSixIndex d.1 ∧ E ≤ (MulAut.conj : K →* MulAut K).range)) →
      ¬ CoverScope d p E →
        seitzHyperGamma p E = ⊤

theorem seitzCoverRest_of_famRest (hGA : GriessMultipliersAllModels) {k : ℕ}
    (h : SeitzCoverFamRest k) : SeitzCoverRest k := by
  intro p hp hp2 K _ _ hq d hd hpd hL34 hz E hE hcard hex hIR
  obtain ⟨e⟩ := hd
  exact h p hp hp2 K hq d ⟨e⟩ hpd hL34 hz (coverIndex_of_dvd_card_center hGA hp hp2 hq d e hpd hz)
    E hE hcard hex hIR

@[expose] def SeitzExcParabolicRFor (P : TauCeti.LieTypeIndex → Prop) : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex) (p : ℕ), p.Prime → p ≠ d.1.characteristic → P d.1 →
    ∀ E : Subgroup (Cat d), IsElemAbelian p E → E ≠ ⊥ → NormalizesRSub d E →
      (⊤ : Subgroup (Cat d)) ≤ Subgroup.closure
        (CFSG.LieType.Chevalley.hyperRSet ⊤ E d.1.characteristic p)

theorem SeitzExcParabolicRFor.union {P Q : TauCeti.LieTypeIndex → Prop}
    (hP : SeitzExcParabolicRFor P) (hQ : SeitzExcParabolicRFor Q) :
    SeitzExcParabolicRFor fun d => P d ∨ Q d := by
  intro d p hp hpd hd E hE hE1 hR
  rcases hd with h | h
  · exact hP d p hp hpd h E hE hE1 hR
  · exact hQ d p hp hpd h E hE hE1 hR

@[expose] def ExcIsotropic {K : Type*} [Group K] (d : TauCeti.ValidLieTypeIndex)
    (E : Subgroup (MulAut K)) : Prop :=
  IsChevalleyExcIndex d.1 ∧ E ≤ (MulAut.conj : K →* MulAut K).range ∧
    ∃ e : K ⧸ Subgroup.center K ≃* Cat d, NormalizesRSub d ((innerImage E).map e.toMonoidHom)

@[expose] def SeitzCoverFamExcRest (k : ℕ) : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
    ∀ d : TauCeti.ValidLieTypeIndex,
    Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group) →
    p ≠ d.1.characteristic → ¬ (p = 3 ∧ IsLThreeFour (K ⧸ Subgroup.center K)) →
    p ∣ Nat.card (Subgroup.center K) → CoverIndex p d.1 →
    ∀ E : Subgroup (MulAut K), IsElemAbelian p E → Nat.card E = p ^ k →
      (¬ ExcIndex p d.1 ∨ (IsSixIndex d.1 ∧ E ≤ (MulAut.conj : K →* MulAut K).range)) →
      ¬ CoverScope d p E → ¬ ExcIsotropic d E →
        seitzHyperGamma p E = ⊤

section ExcGeneric

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.TauCetiBridge

theorem seitzExcParabolicRFor_untwisted (τ : Tag)
    (c : TauCeti.PrimePower → TauCeti.LieTypeIndex) (hchar : ∀ q, (c q).characteristic = q.p)
    (hB : Even.UntwistedBridgeAll τ c)
    (hS : ∀ q : TauCeti.PrimePower, (c q).Valid → ∀ (K : Type) [Field K] [Finite K],
      Nat.card K = q.card → IsSimpleGroup ↥(adjointGroup τ K)) :
    SeitzExcParabolicRFor fun d => ∃ q, d = c q := by
  rintro ⟨d, hv⟩ p hp hpd ⟨q, rfl⟩ E hE hE1 ⟨R, hR1, hRp, hRn⟩
  have : Fact p.Prime := ⟨hp⟩
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hrp : q.p ≠ p := fun h => hpd (by simp [hchar, h])
  obtain ⟨K, _, _, hK, hKchar⟩ : ∃ (K : Type) (_ : Field K) (_ : Finite K),
      Nat.card K = q.card ∧ CharP K q.p :=
    ⟨GaloisField q.p q.exponent, inferInstance, inferInstance, by
      rw [GaloisField.card _ _ q.exponent_pos.ne', TauCeti.PrimePower.card_def], inferInstance⟩
  obtain ⟨φ⟩ := hB q hv K hK
  have hZ : Subgroup.center ↥(adjointGroup τ K) = ⊥ := center_adjointGroup_eq_bot
  let e : Cat ⟨c q, hv⟩ ≃* ↥(adjointGroup τ K) :=
    φ.symm.trans ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot)
  have : IsSimpleGroup ↥(adjointGroup τ K) := hS q hv K hK
  have hgen : RootInvariantHyperGenerationR (adjointGroup τ K) q.p p := by
    intro A R hAC hA hA1 hRC hRr hR hAR
    have := hA
    exact ordinary_root_invariant_prime_subgroup_hyperplane_generation_r τ K q.p p hrp A hAC hA1
      R hRC hRr hR hAR
  have hc : (⟨c q, hv⟩ : TauCeti.ValidLieTypeIndex).1.characteristic = q.p := hchar q
  rw [hc]
  exact closure_hyperRSet_of_native e hgen hE hE1 ⟨R, hR1, by simpa [hchar] using hRp, hRn⟩

theorem seitzExcParabolicRFor_twisted (t : TwistTag)
    (c : TauCeti.PrimePower → TauCeti.LieTypeIndex) (hchar : ∀ q, (c q).characteristic = q.p)
    (hB : Even.TwistedBridgeAll t c)
    (hS : ∀ q : TauCeti.PrimePower, (c q).Valid → ∀ (G : Type) [Group G],
      TwistedChevalleyModel G t (q.p ^ q.exponent) → IsSimpleGroup G) :
    SeitzExcParabolicRFor fun d => ∃ q, d = c q := by
  rintro ⟨d, hv⟩ p hp hpd ⟨q, rfl⟩ E hE hE1 ⟨R, hR1, hRp, hRn⟩
  have : Fact p.Prime := ⟨hp⟩
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hrp : q.p ≠ p := fun h => hpd (by simp [hchar, h])
  obtain ⟨K, _, _, hK, hKchar⟩ : ∃ (K : Type) (_ : Field K) (_ : Finite K),
      Nat.card K = (q.p ^ q.exponent) ^ t.order ∧ CharP K q.p :=
    ⟨GaloisField q.p (q.exponent * t.order), inferInstance, inferInstance, by
      rw [GaloisField.card _ _ (Nat.mul_pos q.exponent_pos t.order_pos).ne', pow_mul],
      inferInstance⟩
  obtain ⟨σ, hσ, hord, -⟩ := finite_graph_field_parameter_fields t q.prime_p q.exponent_pos K hK
  have hσo : σ ^ t.order = 1 := by
    rw [← hord]
    exact pow_orderOf_eq_one σ
  have hσ'' : ∀ x, σ.toRingHom x = x ^ (q.p ^ q.exponent) := fun x => by
    rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hσ]
  have hσ' : ∀ x, σ.toRingHom x = x ^ q.card := fun x => by
    rw [TauCeti.PrimePower.card_def]
    exact hσ'' x
  obtain ⟨φ⟩ := hB q hv K (by rw [TauCeti.PrimePower.card_def]; exact hK) σ.toRingHom hσ'
  have hperf := finite_fixed_root_group_perfect t q.prime_p q.exponent_pos K hK σ.toRingHom hσ''
  have hZ : Subgroup.center ↥(graphFixedRootGroup t K σ.toRingHom) = ⊥ :=
    center_graphFixedRootGroup_eq_bot σ.surjective
  obtain ⟨ψ⟩ := nonempty_derivedCentralQuotient_equiv _ _ hperf.2.2.1 hZ
  let e : Cat ⟨c q, hv⟩ ≃* ↥(graphFixedRootGroup t K σ.toRingHom) := φ.symm.trans ψ
  have hsimple : IsSimpleGroup (Cat ⟨c q, hv⟩) :=
    hS q hv _ ⟨K, inferInstance, inferInstance, hK, σ.toRingHom, hσ'', ⟨φ.symm⟩⟩
  have : IsSimpleGroup ↥(graphFixedRootGroup t K σ.toRingHom) := MulEquiv.isSimpleGroup e.symm
  have hgen : RootInvariantHyperGenerationR (graphFixedRootGroup t K σ.toRingHom) q.p p := by
    intro A R hAC hA hA1 hRC hRr hR hAR
    have := hA
    exact fixed_root_invariant_prime_subgroup_hyperplane_generation_r t K q.p p hrp σ hσo A hAC
      hA1 R hRC hRr hR hAR
  have hc : (⟨c q, hv⟩ : TauCeti.ValidLieTypeIndex).1.characteristic = q.p := hchar q
  rw [hc]
  exact closure_hyperRSet_of_native e hgen hE hE1 ⟨R, hR1, by simpa [hchar] using hRp, hRn⟩

end ExcGeneric

section ExcAll

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.TauCetiBridge

theorem seitzExcParabolicRChevalley : SeitzExcParabolicRFor IsChevalleyExcIndex :=
  SeitzExcParabolicRFor.union
    (SeitzExcParabolicRFor.union
      (seitzExcParabolicRFor_untwisted .G2 TauCeti.LieTypeIndex.G2
        (fun _ => TauCeti.LieTypeIndex.characteristic_G2 _) Even.chevalleyBridgesAll.g2
        isSimpleGroup_adjointGroup_G2)
      (SeitzExcParabolicRFor.union
        (seitzExcParabolicRFor_untwisted .F4 TauCeti.LieTypeIndex.F4
          (fun _ => TauCeti.LieTypeIndex.characteristic_F4 _) Even.chevalleyBridgesAll.f4
          fun _ _ K _ _ _ => isSimpleGroup_adjointGroup_of_isQuasisimple
            (CFSG.LieType.Steinberg.Adjoint.isQuasisimple_f4 K))
        (SeitzExcParabolicRFor.union
          (seitzExcParabolicRFor_untwisted .E6 TauCeti.LieTypeIndex.E6
            (fun _ => TauCeti.LieTypeIndex.characteristic_E6 _) Even.chevalleyBridgesAll.e6
            fun _ _ K _ _ _ => isSimpleGroup_adjointGroup_of_isQuasisimple
              (CFSG.LieType.Simplicity.isQuasisimple_adjointGroup_e6 K))
          (SeitzExcParabolicRFor.union
            (seitzExcParabolicRFor_untwisted .E7 TauCeti.LieTypeIndex.E7
              (fun _ => TauCeti.LieTypeIndex.characteristic_E7 _) Even.chevalleyBridgesAll.e7
              fun _ _ K _ _ _ => isSimpleGroup_adjointGroup_of_isQuasisimple
                (CFSG.LieType.Simplicity.isQuasisimple_adjointGroup_e7 K))
            (seitzExcParabolicRFor_untwisted .E8 TauCeti.LieTypeIndex.E8
              (fun _ => TauCeti.LieTypeIndex.characteristic_E8 _) Even.chevalleyBridgesAll.e8
              fun _ _ K _ _ _ => isSimpleGroup_adjointGroup_of_isQuasisimple
                (CFSG.LieType.Steinberg.Adjoint.isQuasisimple_e8 K))))))
    (SeitzExcParabolicRFor.union
      (seitzExcParabolicRFor_twisted .D4 TauCeti.LieTypeIndex.trialityD4
        (fun _ => TauCeti.LieTypeIndex.characteristic_trialityD4 _)
        Even.chevalleyBridgesAll.trialityD4
        fun q _ G _ h => (CFSG.LieType.Simplicity.fam_3d4_simplicity G q.p q.exponent
          ⟨⟨q.prime_p, q.exponent_pos, rfl⟩, h⟩).2)
      (seitzExcParabolicRFor_twisted .E6 TauCeti.LieTypeIndex.twistedE6
        (fun _ => TauCeti.LieTypeIndex.characteristic_twistedE6 _)
        Even.chevalleyBridgesAll.twistedE6
        fun q _ G _ h => (CFSG.LieType.Simplicity.fam_2e6_simplicity G q.p q.exponent
          ⟨⟨q.prime_p, q.exponent_pos, rfl⟩, h⟩).2))

theorem seitzHyperGamma_eq_top_of_excIsotropic {K : Type*} [Group K] [Finite K]
    (hperf : commutator K = ⊤) {p : ℕ} (hp : p.Prime) {d : TauCeti.ValidLieTypeIndex}
    (hpd : p ≠ d.1.characteristic) {E : Subgroup (MulAut K)} (hE : IsElemAbelian p E)
    (hE1 : E ≠ ⊥) (h : ExcIsotropic d E) : seitzHyperGamma p E = ⊤ := by
  obtain ⟨hd, hinn, e, hR⟩ := h
  have hI := isElemAbelian_innerImage hE
  have hE₀ : IsElemAbelian p ((innerImage E).map e.toMonoidHom) :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hI _
  have hE₀1 : (innerImage E).map e.toMonoidHom ≠ ⊥ := fun h0 =>
    innerImage_ne_bot hinn hE1 ((Subgroup.map_eq_bot_iff_of_injective _ e.injective).1 h0)
  have hgen := seitzExcParabolicRChevalley d p hp hpd hd _ hE₀ hE₀1 hR
  exact seitzHyperGamma_eq_top_of_rGen hperf hp (TauCeti.LieTypeIndex.characteristic_prime d.1)
    (Ne.symm hpd) hE hinn (closure_hyperRSet_of_mulEquiv e hgen)

theorem seitzCoverFamRest_of_excRest {k : ℕ} (hk : 1 ≤ k) (h : SeitzCoverFamExcRest k) :
    SeitzCoverFamRest k := by
  intro p hp hp2 K _ _ hq d hd hpd hL34 hz hci E hE hcard hex hIR
  by_cases hX : ExcIsotropic d E
  · exact seitzHyperGamma_eq_top_of_excIsotropic hq.1 hp hpd hE (ne_bot_of_card hp hk hcard) hX
  · exact h p hp hp2 K hq d hd hpd hL34 hz hci E hE hcard hex hIR hX

end ExcAll

end CFSG.LieType.SeitzGeneration.QuasiHigh
