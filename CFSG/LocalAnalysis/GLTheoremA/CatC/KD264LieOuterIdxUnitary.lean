module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOuterIdx
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOuterUnitary
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzBridge
public import CFSG.Adapters.CatalogueFieldBridges.Unitary
public import CFSG.Adapters.CatalogueFieldBridges.UnitarySU
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.UnitaryDiag

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.Classical CFSG.LieType.Chevalley
open CFSG.QuasithinUnique.SQTK CFSG.Adapters.RankTwoModelTransports
open CFSG.Adapters.CatalogueFieldBridges
open CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower
open Matrix

private theorem idxCoreAt_twistedA_fieldHom {q : TauCeti.PrimePower} {K : Type} [Field K]
    (h : UnitaryFieldData q.p q.exponent K) {n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ≠ q.p) (hN : 3 ≤ n + 1)
    (hpdvd : p ∣ Nat.card (primeFormP h
      ((1 : GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K)))
    (hq₀ : ¬(n + 1 = 3 ∧ q.p ^ (q.exponent / p) = 2))
    {σ : K ≃+* K} (hσ : orderOf σ = p) :
    IdxCoreAt p (.twistedA n q)
      (primeFormFieldHom h (isPrimeFormGram_one (n := n + 1)) σ) := by
  classical
  haveI : Finite K := h.finite
  haveI : Fact p.Prime := ⟨hp⟩
  set N := n + 1 with hNdef
  set h₀ := fixSubfield_unitaryFieldData h hp hp2 hσ with hh₀
  have hbar := fixSubfield_unitaryFieldData_bar h hp hp2 hσ
  obtain ⟨hpf, hcard0⟩ := dvd_and_card_fixSubfield_unitary h hp hp2 hσ
  have hq₀pos : 0 < q.exponent / p :=
    Nat.div_pos (Nat.le_of_dvd (by have := h.one_le; omega) hpf) hp.pos
  let q₀ : TauCeti.PrimePower := ⟨q.p, q.exponent / p, h.prime, hq₀pos⟩
  let T : Subgroup (primeFormP h ((1 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)) :=
    (primeSubfieldPSU h hp hp2 hσ N).range
  have hTfix : T ≤ fixSubgroup (primeFormFieldHom h (isPrimeFormGram_one (n := N)) σ) :=
    range_subfieldPSU_le h N h₀ hbar
  have hTnormal : ∀ f ∈ fixSubgroup (primeFormFieldHom h (isPrimeFormGram_one (n := N)) σ),
      ∀ t ∈ T, f * t * f⁻¹ ∈ T := by
    intro f hf t ht
    exact conj_mem_range_subfieldPSU h h₀ hbar (mem_fixSubgroup.1 hf) ht
  have hJp : p ∣ Nat.card T :=
    dvd_card_primeSubfieldPSU_of_dvd_card h hp hp2 hσ hN hpq hpdvd
  have hinj : Function.Injective (subfieldPSU h h₀ hbar N) :=
    subfieldPSU_injective h h₀ hbar N (by omega)
  let eJ : primeFormP h₀
      ((1 : GL (Fin N) (fixSubfield σ)) : Matrix (Fin N) (Fin N) (fixSubfield σ)) ≃* T :=
    MonoidHom.ofInjective hinj
  have hsimpleT : IsSimpleGroup T := by
    have := isSimpleGroup_primeFormP_one h₀ hN hq₀
    exact eJ.symm.isSimpleGroup
  have hncT : ¬∀ a b : T, a * b = b * a := by
    intro hc
    apply not_commute_primeFormP_one h₀ hN hq₀
    intro a b
    have h1 := hc (eJ a) (eJ b)
    simpa using congrArg eJ.symm h1
  have hnabT : ∃ a b : T, a * b ≠ b * a := by
    obtain ⟨a, ha⟩ := Classical.not_forall.1 hncT
    obtain ⟨b, hb⟩ := Classical.not_forall.1 ha
    exact ⟨a, b, hb⟩
  have hTq : CFSG.IsQuasisimple T :=
    isQuasisimple_of_simple_nonabelian hncT
  have hZ : Subgroup.center T = ⊥ :=
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzBridgeAux.center_eq_bot_of_simple
      hsimpleT hnabT
  have hv : (TauCeti.LieTypeIndex.twistedA n q₀).Valid := by
    refine (TauCeti.LieTypeIndex.valid_iff _).2
      ⟨(TauCeti.LieTypeIndex.inStandardRange_iff _).2 ⟨by omega, fun h2 => ?_⟩,
        fun h => (TauCeti.LieTypeIndex.isDuplicateRepresentative_iff _).1 h⟩
    have hq2 : 2 ≤ q₀.card := by
      rw [TauCeti.PrimePower.card_def]
      exact q.prime_p.two_le.trans (Nat.le_self_pow (Nat.pos_iff_ne_zero.mp hq₀pos) q.p)
    have hne2 : q₀.card ≠ 2 := by
      intro hq2'
      have hq2'' : q.p ^ (q.exponent / p) = 2 := by
        rwa [TauCeti.PrimePower.card_def] at hq2'
      exact hq₀ ⟨by omega, hq2''⟩
    omega
  have hsub : subRelC p (.twistedA n q) (.lie ⟨.twistedA n q₀, hv⟩) := by
    show subRel p (.twistedA n q) (.twistedA n q₀)
    refine Or.inl ⟨rfl, ?_⟩
    show q₀.card ^ p = q.card
    rw [TauCeti.PrimePower.card_def q₀, TauCeti.PrimePower.card_def q, ← pow_mul,
      Nat.div_mul_cancel hpf]
  have eCat : primeFormP h₀
      ((1 : GL (Fin N) (fixSubfield σ)) : Matrix (Fin N) (Fin N) (fixSubfield σ)) ≃*
      TauCeti.ValidLieTypeIndex.Group ⟨.twistedA n q₀, hv⟩ :=
    Classical.choice (primeFormP_one_mulEquiv_twistedA h₀ hN hv)
  have hiso : Nonempty (T ⧸ Subgroup.center T ≃*
      (.lie ⟨.twistedA n q₀, hv⟩ : TauCeti.CFSGIndex).Group) :=
    ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans
      (eJ.symm.trans eCat)⟩
  exact ⟨T, hTfix, hTnormal, hTq, hJp, .lie ⟨.twistedA n q₀, hv⟩, hiso, hsub⟩

theorem lieOuterIdx_unitary : LieOuterIdx isUnitaryIdx := by
  intro d p hp hp2 hpc hP hpdvd hnExc
  obtain ⟨d, hd⟩ := d
  cases d with
  | twistedA n q =>
    let S := (TauCeti.CFSGIndex.lie ⟨.twistedA n q, hd⟩).Group
    have hmodel : StatedClassicalModel S .PSU (n + 1) q.p q.exponent :=
      statedClassicalModel_twistedA n q hd (MulEquiv.refl S)
    obtain ⟨K, _, hU, -, ⟨eP⟩⟩ := exists_primeFormP_mulEquiv_of_statedModel hmodel
    haveI : Finite (primeFormP hU
        ((1 : GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K)) :=
      CFSG.RankThree.PartOne.KCUnitaryModel.finite_primeFormP
    have hN : 3 ≤ n + 1 := hmodel.1.2.2.1
    have hne : ¬(n + 1 = 3 ∧ q.p ^ q.exponent = 2) := by
      rintro ⟨h1, h2⟩
      exact hmodel.1.2.2.2 (Prod.ext h1 h2)
    have hpq : p ≠ q.p := by
      simpa only [TauCeti.LieTypeIndex.characteristic_twistedA] using hpc
    have hpdvdP : p ∣ Nat.card (primeFormP hU
        ((1 : GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K)) := by
      rw [← Nat.card_congr eP.toEquiv]
      exact hpdvd
    have hexc : ¬(n + 1 = 3 ∧ q.p ^ q.exponent = 8 ∧ p = 3) := by
      rintro ⟨h1, h2, h3⟩
      apply hnExc
      refine Or.inl ⟨h3, Or.inl ⟨q, Or.inr ?_, ?_⟩⟩
      · show TauCeti.LieTypeIndex.twistedA n q = TauCeti.LieTypeIndex.twistedA 2 q
        rw [show n = 2 by omega]
      · rw [TauCeti.PrimePower.card_def]; exact h2
    have hcore : ∀ x : MulAut (primeFormP hU
        ((1 : GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K)),
        x ^ p = 1 → x ∉ innAutDerived (primeFormP hU
          ((1 : GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K)) →
        IdxCoreAt p (.twistedA n q) x := by
      intro x hxp hxout
      obtain ⟨σ, M, hσord, -, hq₀, hxδ⟩ :=
        exists_conj_primeFormFieldHom_of_not_inner hU hN hne hp hp2 hpq hpdvdP hexc hxp hxout
      have hcoreδ : IdxCoreAt p (.twistedA n q)
          (primeFormFieldHom hU (isPrimeFormGram_one (n := n + 1)) σ) :=
        idxCoreAt_twistedA_fieldHom hU hp hp2 hpq hN hpdvdP hq₀ hσord
      exact idxCoreAt_of_conj hcoreδ
        (primeFormConjHom hU ((1 : GL (Fin (n + 1)) K) :
          Matrix (Fin (n + 1)) (Fin (n + 1)) K) M)⁻¹ (by rw [hxδ]; group)
    exact outerIdxAt_of_mulEquiv hp eP.symm (outerIdxAt_of_idxCoreAt hp hcore)
  | A n q => exact absurd hP (by simp [isUnitaryIdx])
  | B n q => exact absurd hP (by simp [isUnitaryIdx])
  | C n q => exact absurd hP (by simp [isUnitaryIdx])
  | D n q => exact absurd hP (by simp [isUnitaryIdx])
  | twistedD n q => exact absurd hP (by simp [isUnitaryIdx])
  | E6 q => exact absurd hP (by simp [isUnitaryIdx])
  | E7 q => exact absurd hP (by simp [isUnitaryIdx])
  | E8 q => exact absurd hP (by simp [isUnitaryIdx])
  | F4 q => exact absurd hP (by simp [isUnitaryIdx])
  | G2 q => exact absurd hP (by simp [isUnitaryIdx])
  | twistedE6 q => exact absurd hP (by simp [isUnitaryIdx])
  | trialityD4 q => exact absurd hP (by simp [isUnitaryIdx])
  | suzuki k => exact absurd hP (by simp [isUnitaryIdx])
  | reeG2 k => exact absurd hP (by simp [isUnitaryIdx])
  | reeF4 k => exact absurd hP (by simp [isUnitaryIdx])
  | tits => exact absurd hP (by simp [isUnitaryIdx])

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
