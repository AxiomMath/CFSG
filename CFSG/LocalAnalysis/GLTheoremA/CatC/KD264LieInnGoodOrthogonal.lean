module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInnGoodInner
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Orth3Plane
public import CFSG.LieType.SeitzGeneration.OrthMix
public import CFSG.RankThree.PartOne.KC.OrthogonalCommutatorCore
public import CFSG.RankThree.PartOne.KC.OrthogonalLocalComponents
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxOrthogonal
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessBridge
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxSymplectic
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOuter
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinBOdd
public import CFSG.Adapters.TauCetiLieModels
public import CFSG.GroupTheory.PCore.SubgroupCore
public import CFSG.GroupTheory.SteinbergCBFTCores
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossSp
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOuterIdxSymplectic

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open TauCeti CFSG.Open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonalD4
  CFSG.RankThree.Classical CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.CrossChar
open Polynomial Module

section SpecialBlock

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

theorem specialBlock_quasisimple_le_orthDerived_dvd_card (hx : OddOrderIsometry Q p x)
    (hp : p.Prime) (hp2 : p ≠ 2) (h3 : p = 3 → 4 ≤ Nat.card K) {h : K[X]}
    (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1)
    (hm : 2 ≤ primaryMultiplicity x.toLinearMap h) :
    CFSG.IsQuasisimple ↥(specialBlock Q x h) ∧ specialBlock Q x h ≤ orthDerived Q ∧
      p ∣ Nat.card ↥(specialBlock Q x h) := by
  rcases lt_or_ge 3 p with hp3 | hp3
  · exact ⟨hx.quasisimple_specialBlock hp hp3 hh hne1 hm,
      hx.specialBlock_le_orthDerived hp hp3 hh hne1 hm,
      dvd_card_orthSpecialBlock hx hp hp3 hh hne1 hm⟩
  · have hp3' : p = 3 := by
      have hp2' := hp.two_le
      omega
    have hK4 : 4 ≤ Nat.card K := h3 hp3'
    exact ⟨orth3_quasisimple_specialBlock hx hp hp2 hK4 hh hne1 hm,
      orth3_specialBlock_le_orthDerived hx hp hp2 hK4 hh hne1 hm,
      orth3_dvd_card_orthSpecialBlock hx hp hp2 hh hne1 hm⟩

end SpecialBlock

section Planes

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem perfectCentralizerPlanes_projOrthDerived
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, Module.finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpl : p ≠ ringChar K) (h3 : p = 3 → 4 ≤ Nat.card K) :
    PerfectCentralizerPlanes p (ProjOrthDerived Q) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hℓ : (ringChar K).Prime := CharP.char_is_prime K _
  have : CharP K (ringChar K) := ringChar.charP K
  have : Nontrivial V := nontrivial_of_totallySingular_orth hT
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  intro A hA hAc
  have hA' : CFSG.Assembly.IsElemAbelian p A := ⟨hA.1, hA.2⟩
  obtain ⟨Ã, hÃM, hsyl, e, he, -, -, -, -, hline, -, -, -, -, -⟩ :=
    orthogonal_inner_plane_kernel_line_quadratic_decomposition hℓ hp hp2 hpl Q hQ A hA' hAc
  have hK := kernelLineData Q hQ hp hp2 hpl A hA' hAc Ã ⟨hÃM, hsyl⟩
  obtain ⟨M, N, hM, hN, hMN, hVM, hVN⟩ := hK.two_active
  obtain ⟨a, ha1, h, hh, hne1, hm, -, -⟩ :=
    CFSG.LieType.SeitzGeneration.exists_mixing_factor_orth hQ hp hpl hK hM hN hMN hVM hVN
  have hord : orderOf (a : orthDerived Q) = p := by
    refine orderOf_eq_prime ?_ ?_
    · have := congrArg (fun z : Ã => (z : orthDerived Q)) (hK.exp a)
      simpa using this
    · intro h1
      exact ha1 (Subtype.ext h1)
  have hx : OddOrderIsometry Q p ((a : orthDerived Q) : V ≃ₗ[K] V) :=
    oddOrderIsometry_of_orthDerived hp hpl hQ _ hord
  have hxa : (QuotientGroup.mk (a : orthDerived Q) : ProjOrthDerived Q) = e a :=
    (he a).symm
  have haT : orderOf (e a : ProjOrthDerived Q) = p := by
    rw [← hxa]
    exact orth3_orderOf_mk_projOrth hQ hT hp hp2 hord
  obtain ⟨Rep, hRep, hmemRep⟩ : ∃ Rep : Finset K[X],
      IsOrbitRepresentatives ((a : orthDerived Q) : V ≃ₗ[K] V) Rep ∧ h ∈ Rep :=
    CFSG.RankThree.PartOne.KCOrthComm.exists_orbitRepresentatives_mem hx hh
  obtain ⟨hqF, hFΩ, hdvdF⟩ :=
    specialBlock_quasisimple_le_orthDerived_dvd_card hx hp hp2 h3 (hRep.1 hmemRep) hne1 hm
  have hqJ : CFSG.IsQuasisimple ↥(componentImage Q (a : V ≃ₗ[K] V) h) :=
    isQuasisimple_map_projective hFΩ hqF
  have hJcent : componentImage Q (a : V ≃ₗ[K] V) h ≤
      Subgroup.centralizer ({(e a : ProjOrthDerived Q)} : Set (ProjOrthDerived Q)) := by
    by_cases hp3 : 3 < p
    · obtain ⟨-, hmain⟩ :=
        orthogonal_primary_local_components_and_fixed_residue hQ hT hp hp3 hpl (⊤ :
          Subgroup (MulAut (ProjOrthDerived Q))) le_top (e a) haT (a : orthDerived Q) hxa hord
      obtain ⟨-, -, -, -, -, hspec, -, -⟩ := hmain Rep hRep
      exact (hspec h hmemRep hne1 hm).2.2.2.2.1
    · have hp3' : p = 3 := by
        have := hp.two_le
        omega
      have hK4 : 4 ≤ Nat.card K := h3 hp3'
      exact (orth3_special_facts hQ hT hp hp2 hK4 hpl (⊤ :
        Subgroup (MulAut (ProjOrthDerived Q))) le_top (e a) haT (a : orthDerived Q) hxa
        hord hRep hmemRep hne1 hm).2.2.1
  have hPperf : ⁅componentImage Q (a : V ≃ₗ[K] V) h,
      componentImage Q (a : V ≃ₗ[K] V) h⁆ = componentImage Q (a : V ≃ₗ[K] V) h := by
    haveI : Group.IsPerfect ↥(componentImage Q (a : V ≃ₗ[K] V) h) := hqJ.1
    exact Subgroup.commutator_eq_self
  have hPdvd : p ∣ Nat.card ↥(componentImage Q (a : V ≃ₗ[K] V) h) := by
    obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' p hdvdF
    set s' : orthDerived Q := ⟨(s : V ≃ₗ[K] V), hFΩ s.2⟩ with hs'
    have hs'p : orderOf s' = p := by
      rw [← hs, ← Subgroup.orderOf_coe s, ← Subgroup.orderOf_coe s']
    have hρ := orth3_orderOf_mk_projOrth hQ hT hp hp2 hs'p
    have hmem : (QuotientGroup.mk s' : ProjOrthDerived Q) ∈
        componentImage Q (a : V ≃ₗ[K] V) h :=
      ⟨s', Subgroup.mem_subgroupOf.mpr s.2, rfl⟩
    rw [← hρ]
    exact Subgroup.orderOf_dvd_natCard _ hmem
  refine ⟨e a, (e a).2, ?_, componentImage Q (a : V ≃ₗ[K] V) h, hJcent, hPperf, hPdvd⟩
  intro h1
  have := haT
  rw [h1, orderOf_one] at this
  exact hp.one_lt.ne' this.symm

end Planes

theorem four_le_card_of_ringChar_ne_three {K : Type} [Field K] [Finite K]
    (h3 : ringChar K ≠ 3) (h2 : Nat.card K ≠ 2) : 4 ≤ Nat.card K := by
  have hℓ : (ringChar K).Prime := CharP.char_is_prime K _
  obtain ⟨f, -, hcard⟩ := CFSG.RankThree.PartOne.KCOrthogonalAut.exists_card_eq_pow K
  have h3dvd : ¬ 3 ∣ Nat.card K := by
    intro hd
    rw [hcard] at hd
    have h3ℓ : 3 ∣ ringChar K := Nat.prime_three.dvd_of_dvd_pow hd
    exact h3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hℓ).mp h3ℓ).symm
  have h3ne : Nat.card K ≠ 3 := by
    intro h
    rw [h] at h3dvd
    exact h3dvd (dvd_refl 3)
  have hge : 1 < Nat.card K := Finite.one_lt_card
  by_contra h4
  push Not at h4
  interval_cases Nat.card K
  · exact h2 rfl
  · exact h3ne rfl

theorem innGoodAt_matrixProjectiveDerived {K : Type} [Field K] [Finite K] {d : ℕ} (hd : 0 < d)
    {Q : QuadraticForm K (Fin d → K)}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hZ : Subgroup.center (matrixProjectiveDerived Q) = ⊥)
    (hinner : ∀ p : ℕ, p.Prime → p ≠ 2 →
      ∀ β ∈ innAutDerived (matrixProjectiveDerived Q), β ^ p = 1 →
        β ∈ inner (matrixProjectiveDerived Q))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpl : p ≠ ringChar K)
    (h3 : p = 3 → 4 ≤ Nat.card K) (e : TauCeti.LieTypeIndex) :
    InnGoodAt p e (matrixProjectiveDerived Q) := by
  have hplanes : PerfectCentralizerPlanes p (ProjOrthDerived Q) :=
    perfectCentralizerPlanes_projOrthDerived hQ hT hp hp2 hpl h3
  exact innGoodAt_of_inner_planes hZ (hinner p hp hp2)
    (PerfectCentralizerPlanes.of_mulEquiv (bridgeEquiv Q hd).symm hplanes) e

theorem innGoodAt_pomegaOdd {n ℓ f p : ℕ} {G : Type} [Group G] [Finite G]
    (hG : CFSG.Open.StatedClassicalModel G .POmegaOdd n ℓ f)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ)
    (h32 : ¬ (p = 3 ∧ ℓ ^ f = 2)) (d : TauCeti.LieTypeIndex) :
    InnGoodAt p d G := by
  have hG0 := hG
  obtain ⟨hadm, K, hfield, hfinite, hK, ⟨e⟩⟩ := hG
  letI := hfield
  letI := hfinite
  have hn : 3 ≤ n := hadm.2.2.1
  have hchar : ringChar K = ℓ :=
    CFSG.ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq hadm.1 hadm.2.1 hK
  have hpl : p ≠ ringChar K := by rw [hchar]; exact hpℓ
  have h3 : p = 3 → 4 ≤ Nat.card K := fun hp3 =>
    four_le_card_of_ringChar_ne_three (fun h => hpl (hp3.trans h.symm))
      (fun h2 => h32 ⟨hp3, by rw [← hK]; exact h2⟩)
  obtain ⟨hnd, hT, hZ, hinner⟩ := matrixModel_facts_pomegaOdd hG0 hK e
  have hd : 0 < 2 * n + 1 := by omega
  exact innGoodAt_of_mulEquiv (coordinateOddWitnessEquiv K e).symm
    (innGoodAt_matrixProjectiveDerived hd hnd hT hZ hinner hp hp2 hpl h3 d)

theorem innGoodAt_pomegaPlus {n ℓ f p : ℕ} {G : Type} [Group G] [Finite G]
    (hG : CFSG.Open.StatedClassicalModel G .POmegaPlus n ℓ f) (hn : 5 ≤ n)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ)
    (h32 : ¬ (p = 3 ∧ ℓ ^ f = 2)) (d : TauCeti.LieTypeIndex) :
    InnGoodAt p d G := by
  have hG0 := hG
  obtain ⟨hadm, K, hfield, hfinite, hK, ⟨e⟩⟩ := hG
  letI := hfield
  letI := hfinite
  have hchar : ringChar K = ℓ :=
    CFSG.ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq hadm.1 hadm.2.1 hK
  have hpl : p ≠ ringChar K := by rw [hchar]; exact hpℓ
  have h3 : p = 3 → 4 ≤ Nat.card K := fun hp3 =>
    four_le_card_of_ringChar_ne_three (fun h => hpl (hp3.trans h.symm))
      (fun h2 => h32 ⟨hp3, by rw [← hK]; exact h2⟩)
  obtain ⟨hnd, hT, hZ, hinner⟩ := matrixModel_facts_pomegaPlus hG0 hn hK e
  have hd : 0 < 2 * n := by omega
  exact innGoodAt_of_mulEquiv (coordinatePlusWitnessEquiv K e).symm
    (innGoodAt_matrixProjectiveDerived hd hnd hT hZ hinner hp hp2 hpl h3 d)

theorem innGoodAt_pomegaMinus {n ℓ f p : ℕ} {G : Type} [Group G] [Finite G]
    (hG : CFSG.Open.StatedClassicalModel G .POmegaMinus n ℓ f)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ)
    (h32 : ¬ (p = 3 ∧ ℓ ^ f = 2)) (d : TauCeti.LieTypeIndex) :
    InnGoodAt p d G := by
  have hG0 := hG
  obtain ⟨hadm, K, hfield, hfinite, hK, b, c, hirr, ⟨e⟩⟩ := hG
  letI := hfield
  letI := hfinite
  have hn4 : 4 ≤ n := hadm.2.2
  have hn1 : 1 ≤ n := by omega
  have hchar : ringChar K = ℓ :=
    CFSG.ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq hadm.1 hadm.2.1 hK
  have hpl : p ≠ ringChar K := by rw [hchar]; exact hpℓ
  have h3 : p = 3 → 4 ≤ Nat.card K := fun hp3 =>
    four_le_card_of_ringChar_ne_three (fun h => hpl (hp3.trans h.symm))
      (fun h2 => h32 ⟨hp3, by rw [← hK]; exact h2⟩)
  obtain ⟨hnd, hT, hZ, hinner⟩ := matrixModel_facts_pomegaMinus hG0 hK hn1 b c hirr e
  have hd : 0 < 2 * n := by omega
  exact innGoodAt_of_mulEquiv (coordinateMinusWitnessEquiv K hn1 b c e).symm
    (innGoodAt_matrixProjectiveDerived hd hnd hT hZ hinner hp hp2 hpl h3 d)

@[expose] def isOrthogonalIdx : TauCeti.LieTypeIndex → Prop
  | .B r q => r ≠ 2 ∧ q.p ≠ 2
  | .D r _ => r ≠ 4
  | .twistedD _ _ => True
  | _ => False

theorem lieInnGood_orthogonal : LieInnGood isOrthogonalIdx := by
  intro d p hp hp2 hpc h3 h5 hd
  obtain ⟨idx, hv⟩ := d
  haveI : Finite ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨idx, hv⟩) :=
    CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
  cases idx with
  | B r q =>
    obtain ⟨hr2, hq2⟩ := hd
    have hr : 3 ≤ r := by
      have h2r := ((TauCeti.LieTypeIndex.inStandardRange_iff _).1
        ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1).1
      omega
    have hpℓ : p ≠ q.p := by
      intro h
      exact hpc (by rw [TauCeti.LieTypeIndex.characteristic_B r q, h])
    have hfs : fieldSize (.B r q) = q.p ^ q.exponent := by
      simp [fieldSize, TauCeti.PrimePower.card_def]
    have h32 : ¬ (p = 3 ∧ q.p ^ q.exponent = 2) := by
      rintro ⟨hp3, h2⟩
      exact h3 ⟨hp3, by
        show fieldSize (.B r q) = 2
        rw [hfs]
        exact h2⟩
    have hSC := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_odd r q hv hq2 hr
      (MulEquiv.refl _)
    haveI : Finite (TauCeti.ValidLieTypeIndex.Group ⟨.B r q, hv⟩) :=
      CFSG.LieType.Simplicity.finite_of_statedClassicalModel hSC
    exact innGoodAt_pomegaOdd hSC hp hp2 hpℓ h32 (.B r q)
  | D n q =>
    have h4 : n ≠ 4 := hd
    have hpℓ : p ≠ q.p := by
      intro h
      exact hpc (by rw [TauCeti.LieTypeIndex.characteristic_D n q, h])
    have hfs : fieldSize (.D n q) = q.p ^ q.exponent := by
      simp [fieldSize, TauCeti.PrimePower.card_def]
    have h32 : ¬ (p = 3 ∧ q.p ^ q.exponent = 2) := by
      rintro ⟨hp3, h2⟩
      exact h3 ⟨hp3, by
        show fieldSize (.D n q) = 2
        rw [hfs]
        exact h2⟩
    obtain ⟨hadm, hSC | ⟨h0, -⟩⟩ := CFSG.Models.lieModel_D n q hv (MulEquiv.refl _)
    · have hn : 5 ≤ n := by
        have h4n : 4 ≤ n := hSC.1.2.2
        omega
      haveI : Finite (TauCeti.ValidLieTypeIndex.Group ⟨.D n q, hv⟩) :=
        CFSG.LieType.Simplicity.finite_of_statedClassicalModel hSC
      exact innGoodAt_pomegaPlus hSC hn hp hp2 hpℓ h32 (.D n q)
    · have h4n : 4 ≤ n := hadm.2.2
      omega
  | twistedD n q =>
    have hpℓ : p ≠ q.p := by
      intro h
      exact hpc (by rw [TauCeti.LieTypeIndex.characteristic_twistedD n q, h])
    have hfs : fieldSize (.twistedD n q) = q.p ^ q.exponent := by
      simp [fieldSize, TauCeti.PrimePower.card_def]
    have h32 : ¬ (p = 3 ∧ q.p ^ q.exponent = 2) := by
      rintro ⟨hp3, h2⟩
      exact h3 ⟨hp3, by
        show fieldSize (.twistedD n q) = 2
        rw [hfs]
        exact h2⟩
    obtain ⟨hadm, hSC | ⟨h0, -⟩⟩ := CFSG.Models.lieModel_twistedD n q hv (MulEquiv.refl _)
    · haveI : Finite (TauCeti.ValidLieTypeIndex.Group ⟨.twistedD n q, hv⟩) :=
        CFSG.LieType.Simplicity.finite_of_statedClassicalModel hSC
      exact innGoodAt_pomegaMinus hSC hp hp2 hpℓ h32 (.twistedD n q)
    · have h4n : 4 ≤ n := hadm.2.2
      omega
  | A n q => exact absurd hd (by simp [isOrthogonalIdx])
  | twistedA n q => exact absurd hd (by simp [isOrthogonalIdx])
  | C n q => exact absurd hd (by simp [isOrthogonalIdx])
  | E6 q => exact absurd hd (by simp [isOrthogonalIdx])
  | E7 q => exact absurd hd (by simp [isOrthogonalIdx])
  | E8 q => exact absurd hd (by simp [isOrthogonalIdx])
  | F4 q => exact absurd hd (by simp [isOrthogonalIdx])
  | G2 q => exact absurd hd (by simp [isOrthogonalIdx])
  | twistedE6 q => exact absurd hd (by simp [isOrthogonalIdx])
  | trialityD4 q => exact absurd hd (by simp [isOrthogonalIdx])
  | suzuki k => exact absurd hd (by simp [isOrthogonalIdx])
  | reeG2 k => exact absurd hd (by simp [isOrthogonalIdx])
  | reeF4 k => exact absurd hd (by simp [isOrthogonalIdx])
  | tits => exact absurd hd (by simp [isOrthogonalIdx])

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
