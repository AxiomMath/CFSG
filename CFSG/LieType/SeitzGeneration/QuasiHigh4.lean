module

public import CFSG.LieType.SeitzGeneration.QuasiHigh4Unitary
public import CFSG.HardMathSupport.Dickson.Sec6.Heis
public import CFSG.LieType.SeitzGeneration.QuasiHigh3

public section

namespace CFSG.LieType.SeitzGeneration.QuasiHigh4

open CFSG.Open CFSG.LieType.Seitz CFSG.LieType.SeitzGeneration
  CFSG.LieType.SeitzGeneration.QuasiHigh CFSG.LieType.SeitzGeneration.QuasiHigh2
  CFSG.LieType.SeitzGeneration.QuasiHigh3
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (c25Fix mem_c25Fix)
open CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3 (GenP dPart LiftsCommute gen_toral)
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ (ExcIndex IsSixIndex)

theorem closure_hyperLiftSet_of_genP {P : Type*} [Group P] {A : Subgroup (MulAut P)}
    (hA : IsElemAbelian 3 A) (hc : Nat.card A = 27) (h : GenP A) :
    Subgroup.closure (hyperLiftSet 3 A) = ⊤ := by
  haveI : Finite A := Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  obtain ⟨H₀, hH₀A, hH₀⟩ := exists_hyperplane_of_ne_bot Nat.prime_three hA
    (ne_bot_of_card (k := 3) Nat.prime_three (by norm_num) (by rw [hc]; norm_num))
  rw [eq_top_iff]
  refine h.trans (iSup₂_le fun S hS => ?_)
  obtain ⟨H, hHA, hHrel, hSH⟩ : ∃ H ≤ A, H.relIndex A = 3 ∧
      ∀ y : P, (∀ α ∈ S, α y = y) → y ∈ fixedPoints H := by
    have hdvd : Nat.card S ∣ 3 ^ 3 := by
      rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← hc]
      exact Subgroup.card_dvd_of_le hS.1
    obtain ⟨k, hk3, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
    have h27 := hS.2
    rw [hc, hk] at h27
    have hk2 : 2 ≤ k := by
      by_contra hcon
      have : 3 ^ k ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    interval_cases k
    · refine ⟨S, hS.1, ?_, fun y hy => mem_fixedPoints.2 hy⟩
      have h1 := Subgroup.relIndex_mul_card S A
      rw [inf_of_le_left hS.1, hk, hc] at h1
      omega
    · have hSA : S = A := Subgroup.eq_of_le_of_card_ge hS.1 (by rw [hk, hc]; norm_num)
      exact ⟨H₀, hH₀A, hH₀, fun y hy => mem_fixedPoints.2 fun α hα => hy α (hSA ▸ hH₀A hα)⟩
  apply sup_le
  · rw [Subgroup.commutator_le]
    intro x hx y hy
    exact Subgroup.subset_closure (commutator_mem_hyperLiftSet hHA hHrel
      (hSH x (mem_c25Fix.1 hx)) (hSH y (mem_c25Fix.1 hy)))
  · rw [Subgroup.closure_le]
    rintro x ⟨hx, hco⟩
    refine Subgroup.subset_closure (mem_hyperLiftSet_of_pow hHA hHrel (m := orderOf x) ?_
      (pow_orderOf_eq_one x) (hSH x (mem_c25Fix.1 hx)))
    intro h3
    have h33 : Nat.Coprime 3 3 := Nat.Coprime.coprime_dvd_left h3 hco
    norm_num at h33

theorem seitzHyperGamma_eq_top_of_l364 {K : Type} [Group K] [Finite K]
    (hperf : commutator K = ⊤) {q : TauCeti.PrimePower} {hv : (TauCeti.LieTypeIndex.A 2 q).Valid}
    (e : K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie ⟨.A 2 q, hv⟩).Group)
    (hq : q.card = 64) {E : Subgroup (MulAut K)} (hE : IsElemAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 3) (hLD : ¬ LinearDiag 3 E) : seitzHyperGamma 3 E = ⊤ := by
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hpq : (3 : ℕ) ≠ q.p := by
    intro h
    have h1 : q.p ∣ q.card := by
      rw [TauCeti.PrimePower.card_def]
      exact dvd_pow_self _ q.exponent_pos.ne'
    rw [← h, hq] at h1
    norm_num at h1
  have hci : CoverIndex 3 (.A 2 q) := ⟨by norm_num, by rw [hq]; norm_num⟩
  set θ := standardLinearModel e with hθ
  have hout := not_le_linearAutGroup_of_cubeRest e Nat.prime_three (by norm_num) hpq hci hLD
  have hinj := modelAut_injective hperf θ
  have hE' : IsElemAbelian 3 (E.map (modelAut θ)) :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map 3 hE _
  have hc' : Nat.card (E.map (modelAut θ)) = 27 := by
    rw [Subgroup.card_map_of_injective hinj, hcard]
    norm_num
  have hK : Nat.card (GaloisField q.p q.exponent) = 64 := by
    rw [GaloisField.card q.p q.exponent q.exponent_pos.ne', ← TauCeti.PrimePower.card_def, hq]
  have hb : ∃ b ∈ E.map (modelAut θ), b ∉ linearAutGroup 3 (GaloisField q.p q.exponent) := by
    by_contra hcon
    push Not at hcon
    exact hout hcon
  have hgen : GenP (E.map (modelAut θ)) := by
    by_cases hL : LiftsCommute (E.map (modelAut θ))
    · exact gen_toral (by rw [hK]; norm_num) _ hE' hc' hb hL
    · exact CFSG.HardMathSupport.Dickson.Sec6.Heis.heisP hK hE' hc' hb hL
  exact seitzHyperGamma_eq_top_of_closure_hyperLiftSet_model hperf (isPGroup_of_isElemAbelian hE)
    θ (closure_hyperLiftSet_of_genP hE' hc' hgen)

@[expose] def SeitzCoverCubeRest4 : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
    ∀ d : TauCeti.ValidLieTypeIndex,
    Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group) →
    p ≠ d.1.characteristic → ¬ (p = 3 ∧ IsLThreeFour (K ⧸ Subgroup.center K)) →
    p ∣ Nat.card (Subgroup.center K) → CoverIndex p d.1 →
    (∀ (m : ℕ) (q : TauCeti.PrimePower), d.1 ≠ TauCeti.LieTypeIndex.A m q) →
    ∀ E : Subgroup (MulAut K), IsElemAbelian p E → Nat.card E = p ^ 3 →
      (¬ ExcIndex p d.1 ∨ (IsSixIndex d.1 ∧ E ≤ (MulAut.conj : K →* MulAut K).range)) →
      ¬ CoverScope d p E → ¬ ExcIsotropic d E → ¬ LinearDiag p E → ¬ InvP'Pair p E →
      ¬ UDiagGU p E → ¬ UFieldSplit p E → ¬ UFieldStd p E → seitzHyperGamma p E = ⊤

theorem seitzCoverCubeRest3_of_rest4
    (h : SeitzCoverCubeRest4) :
    SeitzCoverCubeRest3 := by
  intro p hp hp2 K _ _ hq d hd hpd hL34 hz hci hA E hE hcard hex hCS hX hLD hP hU
  by_cases hS : UFieldSplit p E
  · exact seitzHyperGamma_eq_top_of_uFieldSplit hq.1 hp hp2 hE hcard hS
  by_cases hStd : UFieldStd p E
  · exact seitzHyperGamma_eq_top_of_uFieldStd hq.1 hp hp2 hE hcard hStd
  by_cases hlin : ∃ (m : ℕ) (q : TauCeti.PrimePower), d.1 = TauCeti.LieTypeIndex.A m q
  · obtain ⟨m, q, hdq⟩ := hlin
    obtain ⟨hp3, hm2, hq64⟩ := hA m q hdq
    subst hp3 hm2
    obtain ⟨d, hv⟩ := d
    simp only at hdq
    subst hdq
    obtain ⟨e⟩ := hd
    exact seitzHyperGamma_eq_top_of_l364 hq.1 e hq64 hE hcard hLD
  · exact h p hp hp2 K hq d hd hpd hL34 hz hci (fun m q hdq => hlin ⟨m, q, hdq⟩) E hE hcard hex
      hCS hX hLD hP hU hS hStd

end CFSG.LieType.SeitzGeneration.QuasiHigh4
