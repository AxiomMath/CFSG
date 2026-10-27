module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2017ClsOut

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I2017Cls

open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived)

open CFSG.LocalAnalysis.GLTheoremA (I2017LieA8Shape I2017LieClassification)


@[expose] def LinTwoA8 : Prop :=
  ∀ (n : ℕ) (d : TauCeti.ValidLieTypeIndex), d.1 = .A n gfTwoPP →
    Finite (TauCeti.CFSGIndex.lie d).Group → IsSimpleGroup (TauCeti.CFSGIndex.lie d).Group →
    ∀ β : MulAut (TauCeti.CFSGIndex.lie d).Group, β ∈ innAutDerived _ → β ^ 3 = 1 → β ≠ 1 →
      HasA8Comp β → Even (n + 1)

@[expose] def UniTwoNoA8 : Prop :=
  ∀ (n : ℕ) (d : TauCeti.ValidLieTypeIndex), d.1 = .twistedA n gfTwoPP →
    Finite (TauCeti.CFSGIndex.lie d).Group → IsSimpleGroup (TauCeti.CFSGIndex.lie d).Group →
    ∀ β : MulAut (TauCeti.CFSGIndex.lie d).Group, β ∈ innAutDerived _ → β ^ 3 = 1 → β ≠ 1 →
      ¬ HasA8Comp β

@[expose] def SympTwoNoA8 : Prop :=
  ∀ (n : ℕ) (d : TauCeti.ValidLieTypeIndex), d.1 = .B n gfTwoPP →
    Finite (TauCeti.CFSGIndex.lie d).Group → IsSimpleGroup (TauCeti.CFSGIndex.lie d).Group →
    ∀ β : MulAut (TauCeti.CFSGIndex.lie d).Group, β ∈ innAutDerived _ → β ^ 3 = 1 → β ≠ 1 →
      ¬ HasA8Comp β

@[expose] def ExcTwoNoA8 : Prop :=
  ∀ d : TauCeti.ValidLieTypeIndex, (d.1 = .E6 gfTwoPP ∨ d.1 = .E7 gfTwoPP ∨ d.1 = .E8 gfTwoPP ∨
      d.1 = .F4 gfTwoPP ∨ d.1 = .twistedE6 gfTwoPP) →
    Finite (TauCeti.CFSGIndex.lie d).Group → IsSimpleGroup (TauCeti.CFSGIndex.lie d).Group →
    ∀ β : MulAut (TauCeti.CFSGIndex.lie d).Group, β ∈ innAutDerived _ → β ^ 3 = 1 → β ≠ 1 →
      ¬ HasA8Comp β

private theorem eq_gfTwo_of_card {q : TauCeti.PrimePower} (h : q.card = 2) : q = gfTwoPP := by
  rw [TauCeti.PrimePower.card_def] at h
  obtain ⟨hp, he⟩ := (Nat.Prime.pow_eq_iff Nat.prime_two).1 h
  exact TauCeti.PrimePower.ext hp he

private theorem two_pow_ne_two {m : ℕ} (hm : 1 ≤ m) : 2 ^ (2 * m + 1) ≠ 2 := by
  intro h
  have h8 : 2 ^ 3 ≤ 2 ^ (2 * m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [h] at h8
  norm_num at h8

section Certs


theorem innA8_of (hL : LinTwoA8) (hU : UniTwoNoA8) (hS : SympTwoNoA8) (hD : D4TwoNoA8)
    (hE : ExcTwoNoA8) : InnA8 := by
  intro d hq hfin hsimp β hmem hβ3 hβ1 hA8
  haveI := hfin
  have hcard := CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds d
    (TauCeti.CFSGIndex.lie d).Group ⟨MulEquiv.refl _⟩
  have hdvd : 20160 ∣ CFSG.HardMathSupport.Solomon.Coordinator.I1420.lieOrderFormula d.1 := by
    rw [← hcard]
    exact dvd_card_of_hasA8Comp hA8
  obtain ⟨d, hv⟩ := d
  have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
    ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
  have hnd := ((TauCeti.LieTypeIndex.valid_iff _).mp hv).2
  cases d with
  | A n q =>
    have hq2 : q = gfTwoPP := eq_gfTwo_of_card hq
    subst hq2
    have hn : 4 ≤ n := by
      simp only [TauCeti.LieTypeIndex.isDuplicateRepresentative_iff, gfTwoPP,
        TauCeti.PrimePower.card_def] at hnd hr
      omega
    obtain ⟨k, hk⟩ := hL n ⟨_, hv⟩ rfl hfin hsimp β hmem hβ3 hβ1 hA8
    refine Or.inr (Or.inl ⟨n + 1, by omega, ⟨k, hk⟩, by simp⟩)
  | twistedA n q =>
    have hq2 : q = gfTwoPP := eq_gfTwo_of_card hq
    subst hq2
    exact (hU n ⟨_, hv⟩ rfl hfin hsimp β hmem hβ3 hβ1 hA8).elim
  | B n q =>
    have hq2 : q = gfTwoPP := eq_gfTwo_of_card hq
    subst hq2
    exact (hS n ⟨_, hv⟩ rfl hfin hsimp β hmem hβ3 hβ1 hA8).elim
  | C n q =>
    have hq2 : q = gfTwoPP := eq_gfTwo_of_card hq
    subst hq2
    exact absurd rfl hr.2
  | D n q =>
    have hq2 : q = gfTwoPP := eq_gfTwo_of_card hq
    subst hq2
    rcases Nat.lt_or_ge n 5 with h5 | h5
    · obtain rfl : n = 4 := by omega
      exact (hD ⟨_, hv⟩ rfl hfin hsimp β hβ3 hβ1 hA8).elim
    · exact Or.inr (Or.inr (Or.inr ⟨n, h5, Or.inl rfl⟩))
  | twistedD n q =>
    have hq2 : q = gfTwoPP := eq_gfTwo_of_card hq
    subst hq2
    rcases Nat.lt_or_ge n 5 with h5 | h5
    · obtain rfl : n = 4 := by omega
      exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr ⟨n, h5, Or.inr rfl⟩))
  | E6 q =>
    have hq2 : q = gfTwoPP := eq_gfTwo_of_card hq
    subst hq2
    exact (hE ⟨_, hv⟩ (Or.inl rfl) hfin hsimp β hmem hβ3 hβ1 hA8).elim
  | E7 q =>
    have hq2 : q = gfTwoPP := eq_gfTwo_of_card hq
    subst hq2
    exact (hE ⟨_, hv⟩ (Or.inr (Or.inl rfl)) hfin hsimp β hmem hβ3 hβ1 hA8).elim
  | E8 q =>
    have hq2 : q = gfTwoPP := eq_gfTwo_of_card hq
    subst hq2
    exact (hE ⟨_, hv⟩ (Or.inr (Or.inr (Or.inl rfl))) hfin hsimp β hmem hβ3 hβ1 hA8).elim
  | F4 q =>
    have hq2 : q = gfTwoPP := eq_gfTwo_of_card hq
    subst hq2
    exact (hE ⟨_, hv⟩ (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hfin hsimp β hmem hβ3 hβ1 hA8).elim
  | G2 q =>
    have hq' : q.card = 2 := hq
    have hr' : 3 ≤ q.card := hr
    omega
  | twistedE6 q =>
    have hq2 : q = gfTwoPP := eq_gfTwo_of_card hq
    subst hq2
    exact (hE ⟨_, hv⟩ (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) hfin hsimp β hmem hβ3 hβ1 hA8).elim
  | trialityD4 q =>
    have hq2 : q = gfTwoPP := eq_gfTwo_of_card hq
    subst hq2
    exact (not_dvd_lieOrder_triD4_two hdvd).elim
  | suzuki m => exact (two_pow_ne_two hr hq).elim
  | reeG2 m =>
    have hq' : 3 ^ (2 * m + 1) = 2 := hq
    have h3 : 3 ^ 1 ≤ 3 ^ (2 * m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [hq'] at h3
    norm_num at h3
  | reeF4 m => exact (two_pow_ne_two hr hq).elim
  | tits => exact (not_dvd_lieOrder_tits hdvd).elim

end Certs

section Assembly


theorem i2017LieClassification_of_residuals (hL : LinTwoA8) (hU : UniTwoNoA8) (hS : SympTwoNoA8)
    (hD : D4TwoNoA8) (hE : ExcTwoNoA8) : I2017LieClassification :=
  i2017LieClassification_of (innA8_of hL hU hS hD hE) (outA8_of hD)

end Assembly

end CFSG.LocalAnalysis.GLTheoremA.I2017Cls

end
