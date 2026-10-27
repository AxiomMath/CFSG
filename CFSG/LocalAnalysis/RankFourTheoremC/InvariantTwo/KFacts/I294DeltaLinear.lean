module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294DeltaBase
public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower.TwistedA
public import CFSG.Adapters.LinearCatalogStated

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.OuterAutomorphisms (inner inner_normal)

theorem DeltaTowerAt.of_projectiveSL {n : ℕ} {F : Type} [Field F] [Finite F] (hn : 3 ≤ n)
    {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hF : Nat.card F = ℓ ^ f) {p : ℕ} (hp : p.Prime)
    (hd : ¬ p ∣ Nat.gcd n (Nat.card F - 1)) : DeltaTowerAt p (projectiveSL n F) := by
  have : (linearAutGroup n F).Normal :=
    CFSG.HardMathSupport.Timmesfeld.Tables.T1b.linearAutGroup_normal hn
  refine DeltaTowerAt.of_card_not_dvd hp (linearAutGroup n F)
    (fun γ α _ => commutator_mem_linearAutGroup hn hℓ hf hF γ α) ?_
  have hdvd := CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.relIndex_inner_linearAutGroup_dvd
    (k := F) (n := n) (by omega)
  have e : Nat.card (linearAutGroup n F ⧸ (inner (projectiveSL n F)).subgroupOf
      (linearAutGroup n F)) = (inner (projectiveSL n F)).relIndex (linearAutGroup n F) := rfl
  rw [e]
  exact fun h => hd (h.trans hdvd)

theorem DeltaTowerAt.of_catA {m : ℕ} (hm : 2 ≤ m) {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.A m q).Valid) {p : ℕ} (hp : p.Prime)
    (hd : ¬ p ∣ Nat.gcd (m + 1) (q.card - 1)) :
    DeltaTowerAt p (TauCeti.CFSGIndex.lie ⟨.A m q, hv⟩).Group := by
  let e : (TauCeti.CFSGIndex.lie ⟨.A m q, hv⟩).Group ≃*
      projectiveSL (m + 1) (GaloisField q.p q.exponent) :=
    (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL m q hv).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL (m + 1) _)
  have hcardF : Nat.card (GaloisField q.p q.exponent) = q.p ^ q.exponent := by
    rw [GaloisField.card _ _ q.exponent_pos.ne']
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  refine DeltaTowerAt.of_mulEquiv e (DeltaTowerAt.of_projectiveSL (by omega) q.prime_p
    q.exponent_pos hcardF hp ?_)
  rwa [hcardF, ← TauCeti.PrimePower.card_def]

open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag in
theorem DeltaTowerAt.of_primeFormP {ℓ f : ℕ} {K : Type} [Field K] (hU : UnitaryFieldData ℓ f K)
    {N : ℕ} (hN : 3 ≤ N) (hq : ¬(N = 3 ∧ ℓ ^ f = 2)) {p : ℕ} (hp : p.Prime)
    (hd : ¬ p ∣ Nat.gcd N (ℓ ^ f + 1)) :
    DeltaTowerAt p (primeFormP hU ((1 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)) := by
  have : Finite K := hU.finite
  obtain ⟨-, -, hcard, -⟩ := unitary_full_diagonal_outer_order hU hN hq
  refine DeltaTowerAt.of_card_not_dvd hp (primeFormD hU ((1 : GL (Fin N) K) :
    Matrix (Fin N) (Fin N) K))
    (fun γ α _ => OuterDerived.commutator_mem_primeFormD hU hN hq γ α) ?_
  rw [hcard]
  exact hd

open CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower in
theorem DeltaTowerAt.of_cat_twistedA {m : ℕ} {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedA m q).Valid) {p : ℕ} (hp : p.Prime)
    (hd : ¬ p ∣ Nat.gcd (m + 1) (q.card + 1)) :
    DeltaTowerAt p (TauCeti.CFSGIndex.lie ⟨.twistedA m q, hv⟩).Group := by
  have hm2 : 2 ≤ m := TauCeti.LieTypeIndex.two_le_of_twistedA_inStandardRange
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have hmodel := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA m q hv (MulEquiv.refl _)
  have hq : ¬ (m + 1 = 3 ∧ q.p ^ q.exponent = 2) := fun h => hmodel.1.2.2.2 (by rw [h.1, h.2])
  obtain ⟨K, _, hU, ⟨e₀⟩, ⟨e⟩⟩ := exists_primeFormP_mulEquiv_of_statedModel hmodel
  have hd' : ¬ p ∣ Nat.gcd (m + 1) (q.p ^ q.exponent + 1) := by
    rwa [TauCeti.PrimePower.card_def] at hd
  exact DeltaTowerAt.of_mulEquiv e (DeltaTowerAt.of_primeFormP hU (by omega) hq hp hd')

theorem not_dvd_gcd_of_not_isLinearOrUnitaryAt_A {L : Type} [Group L] {p m : ℕ}
    {q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.A m q).Valid)
    (e : L ≃* TauCeti.ValidLieTypeIndex.Group ⟨.A m q, hv⟩) (hn : ¬ IsLinearOrUnitaryAt p L) :
    ¬ p ∣ Nat.gcd (m + 1) (q.card - 1) := by
  intro hd
  obtain ⟨-, K, _, _, hK, ⟨e'⟩⟩ := CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv_typeA hv e
  refine hn (Or.inl ⟨m + 1, K, inferInstance, inferInstance, hd.trans (Nat.gcd_dvd_left _ _),
    ?_, ⟨e'⟩⟩)
  rw [hK, ← TauCeti.PrimePower.card_def]
  exact hd.trans (Nat.gcd_dvd_right _ _)

theorem not_dvd_gcd_of_not_isLinearOrUnitaryAt_twistedA {L : Type} [Group L] {p m : ℕ}
    {q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.twistedA m q).Valid)
    (e : L ≃* TauCeti.ValidLieTypeIndex.Group ⟨.twistedA m q, hv⟩)
    (hn : ¬ IsLinearOrUnitaryAt p L) : ¬ p ∣ Nat.gcd (m + 1) (q.card + 1) := by
  intro hd
  rw [TauCeti.PrimePower.card_def] at hd
  obtain ⟨-, K, _, _, hK, ⟨e'⟩⟩ :=
    CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA m q hv e
  exact hn (Or.inr ⟨m + 1, q.p ^ q.exponent, K, inferInstance, inferInstance, hK,
    hd.trans (Nat.gcd_dvd_left _ _), hd.trans (Nat.gcd_dvd_right _ _), ⟨e'⟩⟩)

end CFSG.LocalAnalysis.RankFourTheoremC
