module

public import CFSG.LieType.SeitzGeneration.QuasiHigh2
public import CFSG.LieType.SeitzGeneration.QuasiHigh3Linear

public section

namespace CFSG.LieType.SeitzGeneration.QuasiHigh3

open CFSG.Open CFSG.LieType.Seitz CFSG.LieType.SeitzGeneration
  CFSG.LieType.SeitzGeneration.QuasiHigh CFSG.LieType.SeitzGeneration.QuasiHigh2
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ (ExcIndex IsSixIndex)

theorem invP'Pair_of_invPairAt_model {K P : Type*} [Group K] [Group P]
    (θ : K ⧸ Subgroup.center K ≃* P) {p : ℕ} {E : Subgroup (MulAut K)}
    (h : InvPairAt p (E.map (modelAut θ))) : InvP'Pair p E := by
  have h1 : InvPairAt p (E.map (quotientCenterAut' K)) :=
    invPairAt_of_congr θ (by rwa [Subgroup.map_map])
  obtain ⟨H₁, H₂, h₁, h₂, hs₁, hs₂, hgen⟩ := h1
  refine ⟨H₁, H₂, h₁, h₂, fun f hf s hs => ?_, fun f hf s hs => ?_, hgen⟩
  · rw [quotAut_eq_quotientCenterAut_model]
    exact hs₁ _ ⟨f, hf, rfl⟩ s hs
  · rw [quotAut_eq_quotientCenterAut_model]
    exact hs₂ _ ⟨f, hf, rfl⟩ s hs

theorem seitzHyperGamma_eq_top_of_linear_field {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {K : Type} [Group K] [Finite K] (hperf : commutator K = ⊤)
    {m : ℕ} {q : TauCeti.PrimePower} {hv : (TauCeti.LieTypeIndex.A m q).Valid}
    (e : K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie ⟨.A m q, hv⟩).Group)
    (hpq : p ≠ q.p) (hci : CoverIndex p (.A m q)) (h64 : ¬ (p = 3 ∧ m = 2 ∧ q.card = 64))
    {E : Subgroup (MulAut K)} (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ 3)
    (hLD : ¬ LinearDiag p E) (hP : ¬ InvP'Pair p E) : seitzHyperGamma p E = ⊤ := by
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  haveI : Fact p.Prime := ⟨hp⟩
  set θ := standardLinearModel e with hθ
  have hout := not_le_linearAutGroup_of_cubeRest e hp hp2 hpq hci hLD
  have hinj := modelAut_injective hperf θ
  have hE' : IsElemAbelian p (E.map (modelAut θ)) :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hE _
  have hc' : Nat.card (E.map (modelAut θ)) = p ^ 3 := by
    rw [Subgroup.card_map_of_injective hinj, hcard]
  have hn : 3 ≤ m + 1 := by
    have := Nat.le_of_dvd (by omega) hci.1
    have := hp.two_le
    omega
  have hK : Nat.card (GaloisField q.p q.exponent) = q.p ^ q.exponent :=
    GaloisField.card q.p q.exponent q.exponent_pos.ne'
  have hKq : Nat.card (GaloisField q.p q.exponent) = q.card := by
    rw [hK, TauCeti.PrimePower.card_def]
  have hpq1 : p ∣ Nat.card (GaloisField q.p q.exponent) - 1 := by
    rw [hKq]
    exact hci.2
  have h64' : m + 1 = p → p = 3 → Nat.card (GaloisField q.p q.exponent) ≠ 64 :=
    fun hmp hp3 hF => h64 ⟨hp3, by omega, by rw [← hKq, hF]⟩
  rcases invPairAt_or_closure_hyperLiftSet q.prime_p q.exponent_pos hn hK hp hp2 h64' hpq hpq1 hE'
    hc' hout with h | h
  · exact absurd (invP'Pair_of_invPairAt_model θ h) hP
  · exact seitzHyperGamma_eq_top_of_closure_hyperLiftSet_model hperf
      (isPGroup_of_isElemAbelian hE) θ h

@[expose] def SeitzCoverCubeRest3 : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
    ∀ d : TauCeti.ValidLieTypeIndex,
    Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group) →
    p ≠ d.1.characteristic → ¬ (p = 3 ∧ IsLThreeFour (K ⧸ Subgroup.center K)) →
    p ∣ Nat.card (Subgroup.center K) → CoverIndex p d.1 →
    (∀ (m : ℕ) (q : TauCeti.PrimePower), d.1 = TauCeti.LieTypeIndex.A m q →
      p = 3 ∧ m = 2 ∧ q.card = 64) →
    ∀ E : Subgroup (MulAut K), IsElemAbelian p E → Nat.card E = p ^ 3 →
      (¬ ExcIndex p d.1 ∨ (IsSixIndex d.1 ∧ E ≤ (MulAut.conj : K →* MulAut K).range)) →
      ¬ CoverScope d p E → ¬ ExcIsotropic d E → ¬ LinearDiag p E → ¬ InvP'Pair p E →
      ¬ UDiagGU p E → seitzHyperGamma p E = ⊤

theorem seitzCoverCubeRest_of_rest3 (h : SeitzCoverCubeRest3) :
    SeitzCoverCubeRest := by
  intro p hp hp2 K _ _ hq d hd hpd hL34 hz hci E hE hcard hex hCS hX hLD hP hU
  by_cases hlin : ∃ (m : ℕ) (q : TauCeti.PrimePower), d.1 = TauCeti.LieTypeIndex.A m q ∧
      ¬ (p = 3 ∧ m = 2 ∧ q.card = 64)
  · obtain ⟨m, q, hdq, h64⟩ := hlin
    obtain ⟨d, hv⟩ := d
    simp only at hdq
    subst hdq
    obtain ⟨e⟩ := hd
    exact seitzHyperGamma_eq_top_of_linear_field hp hp2 hq.1 e (by simpa using hpd) hci h64 hE
      hcard hLD hP
  · refine h p hp hp2 K hq d hd hpd hL34 hz hci (fun m q hdq => ?_) E hE hcard hex hCS hX hLD hP
      hU
    by_contra hcon
    exact hlin ⟨m, q, hdq, hcon⟩

end CFSG.LieType.SeitzGeneration.QuasiHigh3
