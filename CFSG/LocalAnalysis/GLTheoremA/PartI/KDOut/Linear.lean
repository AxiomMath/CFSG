module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.KDOut.Tower
public import CFSG.LocalAnalysis.GLTheoremA.PartI.KDOut.CyclicLemma
public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower.TwistedA

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.AGLEmbedding CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.OuterAutomorphisms (inner inner_normal)

theorem outTwoTowerAt_projectiveSL {n : ℕ} {F : Type} [Field F] [Finite F] (hn : 3 ≤ n)
    {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hF : Nat.card F = ℓ ^ f) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) : OutTwoTowerAt (projectiveSL n F) p := by
  have : (linearAutGroup n F).Normal :=
    CFSG.HardMathSupport.Timmesfeld.Tables.T1b.linearAutGroup_normal hn
  have : ((MulAut.conj : projectiveSL n F →* MulAut (projectiveSL n F)).range).Normal :=
    inner_normal _
  refine ⟨linearAutGroup n F, fun γ α _ => commutator_mem_linearAutGroup hn hℓ hf hF γ α,
    fun α ⟨k, hk⟩ δ hδ ⟨m, hm⟩ => ?_⟩
  have hcyc := CFSG.HardMathSupport.Timmesfeld.Tables.T1b.isCyclic_linearD_quotient (K := F) hn
  exact commutator_mem_of_isCyclic_quotient_two hcyc hp hp2 hk hδ hm

theorem outTwoTowerAt_catA {m : ℕ} (hm : 2 ≤ m) {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.A m q).Valid) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    OutTwoTowerAt (TauCeti.CFSGIndex.lie ⟨.A m q, hv⟩).Group p := by
  let e : (TauCeti.CFSGIndex.lie ⟨.A m q, hv⟩).Group ≃*
      projectiveSL (m + 1) (GaloisField q.p q.exponent) :=
    (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL m q hv).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL (m + 1) _)
  have hcardF : Nat.card (GaloisField q.p q.exponent) = q.p ^ q.exponent := by
    rw [GaloisField.card _ _ q.exponent_pos.ne']
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  exact OutTwoTowerAt.of_mulEquiv e (outTwoTowerAt_projectiveSL (by omega) q.prime_p
    q.exponent_pos hcardF hp hp2)

open CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag in
theorem outTwoTowerAt_primeFormP {ℓ f : ℕ} {K : Type} [Field K] (hU : UnitaryFieldData ℓ f K)
    {N : ℕ} (hN : 3 ≤ N) (hq : ¬(N = 3 ∧ ℓ ^ f = 2)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    OutTwoTowerAt (primeFormP hU ((1 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)) p := by
  have : Finite K := hU.finite
  obtain ⟨-, -, -, -, -, -, -, -, hDn, -, -⟩ :=
    unitary_prime_form_full_semilinear_realization hU (isPrimeFormGram_one (n := N)) hN hq
  obtain ⟨-, hcyc, hcard, -⟩ := unitary_full_diagonal_outer_order hU hN hq
  have : ((MulAut.conj : primeFormP hU ((1 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) →*
      MulAut (primeFormP hU ((1 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K))).range).Normal :=
    inner_normal _
  refine ⟨primeFormD hU ((1 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K),
    fun γ α _ => OuterDerived.commutator_mem_primeFormD hU hN hq γ α,
    fun α ⟨k, hk⟩ δ hδ ⟨m, hm⟩ => ?_⟩
  exact commutator_mem_of_isCyclic_quotient_two hcyc hp hp2 hk hδ hm

open CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower in
theorem outTwoTowerAt_cat_twistedA {m : ℕ} {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedA m q).Valid) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    OutTwoTowerAt (TauCeti.CFSGIndex.lie ⟨.twistedA m q, hv⟩).Group p := by
  have hm2 : 2 ≤ m := TauCeti.LieTypeIndex.two_le_of_twistedA_inStandardRange
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have hmodel := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA m q hv (MulEquiv.refl _)
  have hq : ¬ (m + 1 = 3 ∧ q.p ^ q.exponent = 2) := fun h => hmodel.1.2.2.2 (by rw [h.1, h.2])
  obtain ⟨K, _, hU, ⟨e₀⟩, ⟨e⟩⟩ := exists_primeFormP_mulEquiv_of_statedModel hmodel
  exact OutTwoTowerAt.of_mulEquiv e (outTwoTowerAt_primeFormP hU (by omega) hq hp hp2)

end CFSG.LocalAnalysis.GLTheoremA
