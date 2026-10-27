module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieI5LowE6
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieI5LowThree
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInputs
public import CFSG.LocalAnalysis.GLTheoremA.S4.FullCover.MultLie
public import CFSG.HardMathSupport.Foote.FamilyReduction.ClassicalFive

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Assembly.LowTwoRank


theorem ne_char_of_dvd {p : ℕ} (hp : p.Prime) {q : TauCeti.PrimePower}
    (h : p ∣ q.card - 1 ∨ p ∣ q.card + 1) : p ≠ q.p := by
  intro hpq
  have hf : 0 < q.exponent := q.exponent_pos
  have hcard : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
  rw [← hpq] at hcard
  rw [hcard] at h
  have hN : 0 < p ^ q.exponent := pow_pos hp.pos _
  have hpf : p ∣ p ^ q.exponent := dvd_pow_self p hf.ne'
  generalize p ^ q.exponent = N at h hpf hN
  rcases h with h | h
  · have h1 := Nat.dvd_sub hpf h
    have h2 : N - (N - 1) = 1 := by omega
    rw [h2] at h1
    exact hp.not_dvd_one h1
  · have h1 := Nat.dvd_sub h hpf
    have h2 : N + 1 - N = 1 := by omega
    rw [h2] at h1
    exact hp.not_dvd_one h1

theorem bound_A (hGA : CFSG.Open.GriessAllModelsStatement) {K : Type} [Group K] [Finite K]
    (hK : CFSG.Open.IsQuasisimple K) {n : ℕ} {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.A n q).Valid) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ q.card - 1) (hn : 2 ≤ n)
    (e : K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie ⟨.A n q, hv⟩).Group) :
    n - 1 + CFSG.Open.pRank p (Subgroup.center K) ≤ CFSG.Open.pRank p (⊤ : Subgroup K) := by
  have hne : p ≠ q.p := ne_char_of_dvd hp (Or.inl hpq)
  have hpq' : p ∣ q.p ^ q.exponent - 1 := by rw [← TauCeti.PrimePower.card_def]; exact hpq
  have hX : CFSG.Models.LieModel (TauCeti.CFSGIndex.lie ⟨.A n q, hv⟩).Group .PSL (n + 1)
      q.p q.exponent :=
    CFSG.Models.lieModel_A n q hv (MulEquiv.refl _)
  have hmK : CFSG.Models.LieModel (K ⧸ Subgroup.center K) .PSL (n + 1) q.p q.exponent :=
    CFSG.Models.lieModel_A n q hv e
  obtain ⟨hadm, hcl | ⟨h0, -⟩⟩ := hmK
  swap
  · omega
  obtain ⟨-, F, _, _, hF, ⟨eF⟩⟩ := hcl
  haveI : Fact p.Prime := ⟨hp⟩
  by_cases hZ : p ∣ Nat.card (Subgroup.center K)
  · have hZ1 := pRank_center_le_one hGA hK e hX (Or.inl rfl) hp hp2 hne
    by_cases hN : 4 ≤ n + 1
    · have h1 := pRank_ge_PSL hGA hK hadm hF eF hp hp2 hN hpq' hne hZ
      omega
    · obtain rfl : n = 2 := by omega
      have h2 := pRank_ge_two_PSL hGA hK hadm hF eF hp hp2 hpq' hne hZ
      omega
  · have hZ0 := pRank_eq_zero_of_not_dvd hp (Subgroup.center K) hZ
    have hT := (CFSG.SectionRank.OddCover.scalar_quotient_diagonal_torus_rank (K := F)
      (p := q.p) (f := q.exponent) (n := n + 1) (r := p) hadm.1 (by omega) hp2
      (H := StatedSL (n + 1) F) (Or.inl ⟨hF, rfl, hpq'⟩)
      ((StatedScalars (Fin (n + 1)) F).subgroupOf (StatedSL (n + 1) F)) le_rfl).1
    have hT' : n + 1 - 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup (K ⧸ Subgroup.center K)) := by
      rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt eF]
      exact hT
    have hq := CFSG.SectionRank.pRank_quotient_eq (Subgroup.center K) hZ
    omega

theorem bound_twistedA (hGA : CFSG.Open.GriessAllModelsStatement) {K : Type} [Group K]
    [Finite K] (hK : CFSG.Open.IsQuasisimple K) {n : ℕ} {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedA n q).Valid) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ q.card + 1)
    (e : K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie ⟨.twistedA n q, hv⟩).Group) :
    n - 1 + CFSG.Open.pRank p (Subgroup.center K) ≤ CFSG.Open.pRank p (⊤ : Subgroup K) := by
  have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
    ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
  have hn : 2 ≤ n := hr.1
  have hne : p ≠ q.p := ne_char_of_dvd hp (Or.inr hpq)
  have hpq' : p ∣ q.p ^ q.exponent + 1 := by rw [← TauCeti.PrimePower.card_def]; exact hpq
  have hX : CFSG.Models.LieModel (TauCeti.CFSGIndex.lie ⟨.twistedA n q, hv⟩).Group .PSU (n + 1)
      q.p q.exponent :=
    CFSG.LocalAnalysis.GLTheoremA.lieModel_twistedA' n q hv (MulEquiv.refl _)
  have hmK : CFSG.Models.LieModel (K ⧸ Subgroup.center K) .PSU (n + 1) q.p q.exponent :=
    CFSG.LocalAnalysis.GLTheoremA.lieModel_twistedA' n q hv e
  obtain ⟨hadm, hcl | ⟨h0, -⟩⟩ := hmK
  swap
  · omega
  obtain ⟨-, F, _, _, hF, ⟨eF⟩⟩ := hcl
  haveI : Fact p.Prime := ⟨hp⟩
  by_cases hZ : p ∣ Nat.card (Subgroup.center K)
  · have hZ1 := pRank_center_le_one hGA hK e hX (Or.inr (Or.inl rfl)) hp hp2 hne
    by_cases hN : 4 ≤ n + 1
    · have h1 := pRank_ge_PSU hGA hK hadm hF eF hp hp2 hN hpq' hne hZ
      omega
    · obtain rfl : n = 2 := by
        omega
      have hq3 : 3 ≤ q.p ^ q.exponent := by
        rw [← TauCeti.PrimePower.card_def]
        exact hr.2 rfl
      have h2 := pRank_ge_two_PSU hGA hK hadm hF hq3 eF hp hp2 hpq' hne hZ
      omega
  · have hZ0 := pRank_eq_zero_of_not_dvd hp (Subgroup.center K) hZ
    have hT := (CFSG.SectionRank.OddCover.scalar_quotient_diagonal_torus_rank (K := F)
      (p := q.p) (f := q.exponent) (n := n + 1) (r := p) hadm.1 (by omega) hp2
      (H := StatedSU (n + 1) (q.p ^ q.exponent) F) (Or.inr ⟨hF, rfl, hpq'⟩)
      ((StatedScalars (Fin (n + 1)) F).subgroupOf (StatedSU (n + 1) (q.p ^ q.exponent) F))
      le_rfl).1
    have hT' : n + 1 - 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup (K ⧸ Subgroup.center K)) := by
      rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt eF]
      exact hT
    have hq := CFSG.SectionRank.pRank_quotient_eq (Subgroup.center K) hZ
    omega

theorem kd264I5Low_holds : KD264I5Low := by
  intro p hp hp2 K _ _ hK e k hk hiso
  have hGA := CFSG.HardMathSupport.Foote.FamilyReduction.griessAllModelsStatement
  obtain ⟨idx, hv⟩ := e
  obtain ⟨e'⟩ := hiso
  cases idx with
  | A n q =>
    simp only [i5LowBound] at hk
    obtain ⟨hpq, rfl⟩ := hk
    rcases Nat.lt_or_ge n 2 with hn | hn
    · have hk0 : n - 1 = 0 := by omega
      rw [hk0, zero_add]
      exact CFSG.SectionRank.pRank_mono hp.one_lt le_top
    · exact bound_A hGA hK hv hp hp2 hpq hn e'
  | twistedA n q =>
    simp only [i5LowBound] at hk
    obtain ⟨hpq, rfl⟩ := hk
    exact bound_twistedA hGA hK hv hp hp2 hpq e'
  | E6 q =>
    simp only [i5LowBound] at hk
    obtain ⟨rfl, h3, rfl⟩ := hk
    exact bound_E6 hGA hK hv h3 e'
  | twistedE6 q =>
    simp only [i5LowBound] at hk
    obtain ⟨rfl, h3, rfl⟩ := hk
    exact bound_twistedE6 hGA hK hv h3 e'
  | _ => simp only [i5LowBound] at hk

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
