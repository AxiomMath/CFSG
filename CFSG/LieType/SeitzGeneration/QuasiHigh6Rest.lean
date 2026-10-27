module

public import CFSG.LieType.SeitzGeneration.QuasiHigh4
public import CFSG.LieType.SeitzGeneration.QuasiHigh6

public section

namespace CFSG.LieType.SeitzGeneration.QuasiHigh6

open CFSG.Open CFSG.LieType.Seitz CFSG.LieType.SeitzGeneration
  CFSG.LieType.SeitzGeneration.QuasiHigh CFSG.LieType.SeitzGeneration.QuasiHigh2
  CFSG.LieType.SeitzGeneration.QuasiHigh3 CFSG.LieType.SeitzGeneration.QuasiHigh4
  CFSG.LieType.SeitzGeneration.QuasiHigh5
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ (ExcIndex IsSixIndex)

theorem seitzHyperGamma_eq_top_unitaryCube
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {K : Type} [Group K] [Finite K]
    (hperf : commutator K = ⊤) {m : ℕ} {q : TauCeti.PrimePower}
    {hv : (TauCeti.LieTypeIndex.twistedA m q).Valid}
    (e : K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie ⟨.twistedA m q, hv⟩).Group)
    (hci : CoverIndex p (.twistedA m q)) {E : Subgroup (MulAut K)}
    (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ 3)
    (hex : ¬ ExcIndex p (.twistedA m q) ∨
      (IsSixIndex (.twistedA m q) ∧ E ≤ (MulAut.conj : K →* MulAut K).range)) :
    seitzHyperGamma p E = ⊤ := by
  classical
  obtain ⟨hℓ, hf, hn3, hne, Kf, _, hU, ⟨θ⟩⟩ :=
    CFSG.RankThree.PartOne.exists_primeFormP_of_statedClassicalModel_PSU
      (CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA m q hv e)
  have hqcard : q.p ^ q.exponent = q.card := (TauCeti.PrimePower.card_def q).symm
  have hpq1 : p ∣ q.p ^ q.exponent + 1 := by
    rw [hqcard]
    exact hci.2
  have hpm : p ∣ m + 1 := hci.1
  have hq2 : q.p ^ q.exponent ≠ 2 := by
    intro h2
    have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (by
      rw [h2] at hpq1
      exact hpq1)
    subst hp3
    have hm2 : m ≠ 2 := fun hm => hne ⟨by omega, h2⟩
    obtain ⟨hX, hS⟩ := excIndex_twistedA_two (by rw [← hqcard]; exact h2) hpm hm2
    rcases hex with h1 | h1
    · exact h1 hX
    · exact hS h1.1
  by_cases hD : E.map (modelAut θ) ≤ primeFormD hU (idGram Kf (m + 1))
  · exact seitzHyperGamma_eq_top_of_le_primeFormD_cover hperf hU hn3 hq2 hp hp2 hpq1 θ hE hcard hD
  · refine seitzHyperGamma_eq_top_of_not_le_primeFormD_cover hperf hU hn3 hq2 hp hp2 hpq1 ?_ θ hE
      hcard hD
    rintro ⟨rfl, h8⟩
    have hq' : q.p ^ q.exponent = 2 ^ 3 := by rw [h8]; norm_num
    have hp2' : q.p = 2 := by
      have h1 : q.p ∣ 2 ^ 3 := hq' ▸ dvd_pow_self q.p q.exponent_pos.ne'
      exact (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).1 (q.prime_p.dvd_of_dvd_pow h1)
    have he3 : q.exponent = 3 := by
      rw [hp2'] at hq'
      exact Nat.pow_right_injective (le_refl 2) hq'
    have hTP : CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.IsTwoPow q 3 := ⟨hp2', he3⟩
    have hX : ExcIndex 3 (.twistedA m q) := by
      obtain ⟨k, hk⟩ := hpm
      by_cases h25 : m = 2 ∨ m = 5
      · exact Or.inr ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hTP, h25⟩)))))⟩
      · have hk3 : 3 ≤ k := by omega
        exact Or.inr ⟨rfl, Or.inr (Or.inl ⟨Or.inr hTP, k, hk3, hk⟩)⟩
    rcases hex with h1 | h1
    · exact h1 hX
    · exact hD (map_modelAut_le_primeFormD_of_inner hU θ h1.2)

@[expose] def SeitzCoverCubeRest5 : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
    ∀ d : TauCeti.ValidLieTypeIndex,
    Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group) →
    p ≠ d.1.characteristic → ¬ (p = 3 ∧ IsLThreeFour (K ⧸ Subgroup.center K)) →
    p ∣ Nat.card (Subgroup.center K) → CoverIndex p d.1 →
    ((∃ q, d.1 = TauCeti.LieTypeIndex.E6 q) ∨ (∃ q, d.1 = TauCeti.LieTypeIndex.twistedE6 q)) →
    ∀ E : Subgroup (MulAut K), IsElemAbelian p E → Nat.card E = p ^ 3 →
      (¬ ExcIndex p d.1 ∨ (IsSixIndex d.1 ∧ E ≤ (MulAut.conj : K →* MulAut K).range)) →
      ¬ CoverScope d p E → ¬ ExcIsotropic d E → ¬ LinearDiag p E → ¬ InvP'Pair p E →
      ¬ UDiagGU p E → ¬ UFieldSplit p E → ¬ UFieldStd p E → seitzHyperGamma p E = ⊤

theorem seitzCoverCubeRest4_of_rest5
    (h : SeitzCoverCubeRest5) : SeitzCoverCubeRest4 := by
  intro p hp hp2 K _ _ hq d hd hpd hL34 hz hci hA E hE hcard hex hCS hX hLD hP hU hS hStd
  obtain ⟨dd, hv⟩ := d
  cases dd with
  | A m q => exact absurd rfl (hA m q)
  | twistedA m q =>
    obtain ⟨e⟩ := hd
    exact seitzHyperGamma_eq_top_unitaryCube hp hp2 hq.1 e hci hE hcard hex
  | E6 q =>
    exact h p hp hp2 K hq ⟨.E6 q, hv⟩ hd hpd hL34 hz hci (Or.inl ⟨q, rfl⟩) E hE hcard hex hCS hX
      hLD hP hU hS hStd
  | twistedE6 q =>
    exact h p hp hp2 K hq ⟨.twistedE6 q, hv⟩ hd hpd hL34 hz hci (Or.inr ⟨q, rfl⟩) E hE hcard hex
      hCS hX hLD hP hU hS hStd
  | _ => exact hci.elim

end CFSG.LieType.SeitzGeneration.QuasiHigh6
