module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCoreS

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.ComponentClassification.OuterAutomorphisms

private theorem kd264ExcNoGood_of_outer (hOutCyc : KD264OutCyc) (hOuterIdx : KD264OuterIdx)
    (hTriInnGood : KD264TriInnGood) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hPL : KD264PL p) (e : TauCeti.ValidLieTypeIndex)
    [Finite (TauCeti.CFSGIndex.lie e).Group] (hpchar : p ≠ e.1.characteristic)
    (hpdvd : p ∣ Nat.card (TauCeti.CFSGIndex.lie e).Group)
    (D : Subgroup (MulAut (TauCeti.CFSGIndex.lie e).Group))
    (hD : IsElemAbelian p D) (hDcard : p ^ 2 ≤ Nat.card D)
    (hgood : ∀ a ∈ D, a ≠ 1 → GLAPLayer p (fixSubgroup a) = ⊥)
    (hDout : ¬ D ≤ innAutDerived (TauCeti.CFSGIndex.lie e).Group) :
    (p = 3 ∧ ov2Idx e.1) ∨
    (p = 3 ∧ (∃ q : TauCeti.PrimePower, (e.1 = .A 1 q ∨ e.1 = .twistedA 2 q) ∧ q.card = 8) ∧
      ∃ a ∈ D, a ∉ innAutDerived (TauCeti.CFSGIndex.lie e).Group) ∨
    (p = 5 ∧ (e.1 = .suzuki 2 ∨ e.1 = .tits)) ∨
    (lpEpsIdx p e.1 ∧ Nat.card D = p ^ 2) := by
  obtain ⟨a, haD, haout⟩ := IsConcreteLE.not_le_iff_exists.mp hDout
  have hane : a ≠ 1 := by
    rintro rfl
    exact haout (Subgroup.one_mem _)
  have hapow : a ^ p = 1 := hD.2 a haD
  by_cases hx2 : p = 3 ∧ ∃ q : TauCeti.PrimePower,
      (e.1 = .A 1 q ∨ e.1 = .twistedA 2 q) ∧ q.card = 8
  · exact Or.inr (Or.inl ⟨hx2.1, hx2.2, a, haD, haout⟩)
  by_cases hx3 : p = 5 ∧ e.1 = .suzuki 2
  · exact Or.inr (Or.inr (Or.inl ⟨hx3.1, Or.inl hx3.2⟩))
  by_cases htri : p = 3 ∧ ∃ q : TauCeti.PrimePower, e.1 = .trialityD4 q
  ·
    obtain ⟨hp3, q, heq⟩ := htri
    subst hp3
    by_cases hq : q.card = 2
    · exact Or.inl ⟨rfl, by rw [heq]; exact hq⟩
    · exfalso
      have hq2 : 2 ≤ q.card := by
        rw [TauCeti.PrimePower.card_def]
        calc 2 ≤ q.p := q.prime_p.two_le
          _ = q.p ^ 1 := (pow_one _).symm
          _ ≤ q.p ^ q.exponent := Nat.pow_le_pow_right q.prime_p.pos q.exponent_pos
      have hqgt : 2 < q.card := lt_of_le_of_ne hq2 (Ne.symm hq)
      have hN1 := hOutCyc e 3 Nat.prime_three (by norm_num) hpchar D hD
      have hD9 : 9 ≤ Nat.card D := by simpa using hDcard
      have hne : D ⊓ innAutDerived (TauCeti.CFSGIndex.lie e).Group ≠ ⊥ := by
        intro hbot
        rw [hbot, Subgroup.card_bot] at hN1
        omega
      obtain ⟨x, hx, hxne⟩ :=
        (Subgroup.bot_or_exists_ne_one
          (D ⊓ innAutDerived (TauCeti.CFSGIndex.lie e).Group)).resolve_left hne
      obtain ⟨P, hPle, hPperf, hPdvd⟩ :=
        hTriInnGood e ⟨q, heq, hqgt⟩ hpchar x hx.2 (hD.2 x hx.1) hxne
      obtain ⟨J, hJcomp, hJdvd⟩ := hPL e hpchar x (hD.2 x hx.1) hxne P hPle hPperf hPdvd
      have hJle : J ≤ GLAPLayer 3 (fixSubgroup x) := le_sSup hJcomp
      have hJne : J ≠ ⊥ := by
        intro hJbot
        rw [hJbot, Subgroup.card_bot] at hJdvd
        exact Nat.Prime.not_dvd_one Nat.prime_three hJdvd
      exact hJne (le_bot_iff.1 (hJle.trans (le_of_eq (hgood x hx.1 hxne))))
  ·
    have hN2 : ¬ (p = 3 ∧
        ((∃ q : TauCeti.PrimePower, (e.1 = .A 1 q ∨ e.1 = .twistedA 2 q) ∧ q.card = 8) ∨
          ∃ q : TauCeti.PrimePower, e.1 = .trialityD4 q)) := by
      rintro ⟨hp3, h | h⟩
      · exact hx2 ⟨hp3, h⟩
      · exact htri ⟨hp3, h⟩
    obtain ⟨J, hJcomp, hJdvd, -⟩ :=
      hOuterIdx e p hp hp2 hpchar hpdvd hN2 hx3 a hapow haout
    exfalso
    have hJle : J ≤ GLAPLayer p (fixSubgroup a) := le_sSup hJcomp
    have hJne : J ≠ ⊥ := by
      intro hJbot
      rw [hJbot, Subgroup.card_bot] at hJdvd
      exact hp.not_dvd_one hJdvd
    exact hJne (le_bot_iff.1 (hJle.trans (le_of_eq (hgood a haD hane))))

private theorem kd264ExcNoGood_of_inner (hInnGood : KD264InnGood) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hPL : KD264PL p) (e : TauCeti.ValidLieTypeIndex)
    [Finite (TauCeti.CFSGIndex.lie e).Group] (hpchar : p ≠ e.1.characteristic)
    (D : Subgroup (MulAut (TauCeti.CFSGIndex.lie e).Group))
    (hD : IsElemAbelian p D) (hDcard : p ^ 2 ≤ Nat.card D)
    (hgood : ∀ a ∈ D, a ≠ 1 → GLAPLayer p (fixSubgroup a) = ⊥)
    (hDin : D ≤ innAutDerived (TauCeti.CFSGIndex.lie e).Group) :
    (p = 3 ∧ ov2Idx e.1) ∨
    (p = 3 ∧ (∃ q : TauCeti.PrimePower, (e.1 = .A 1 q ∨ e.1 = .twistedA 2 q) ∧ q.card = 8) ∧
      ∃ a ∈ D, a ∉ innAutDerived (TauCeti.CFSGIndex.lie e).Group) ∨
    (p = 5 ∧ (e.1 = .suzuki 2 ∨ e.1 = .tits)) ∨
    (lpEpsIdx p e.1 ∧ Nat.card D = p ^ 2) := by
  by_cases hx1 : p = 3 ∧ ov2Idx e.1
  · exact Or.inl hx1
  by_cases hx3 : p = 5 ∧ e.1 = .tits
  · exact Or.inr (Or.inr (Or.inl ⟨hx3.1, Or.inr hx3.2⟩))
  obtain ⟨D', hD'le, hD'card⟩ : ∃ D' : Subgroup (MulAut (TauCeti.CFSGIndex.lie e).Group),
      D' ≤ D ∧ Nat.card D' = p ^ 2 := by
    obtain ⟨H, hHcard⟩ :=
      Sylow.exists_subgroup_card_pow_prime_of_le_card (G := ↥D) hp
        (CFSG.LocalAnalysis.GLTheoremA.isPGroup_of_isElemAbelian hD) hDcard
    exact ⟨H.map D.subtype, Subgroup.map_subtype_le H, by rw [Subgroup.card_subtype, hHcard]⟩
  have hD' : IsElemAbelian p D' := CFSG.LocalAnalysis.GLTheoremA.isElemAbelian_mono hD hD'le
  rcases hInnGood e p hp hp2 hpchar hx1 hx3 D' hD' hD'card (hD'le.trans hDin) with
    ⟨β, hβD', hβne, P, hPle, hPperf, hPdvd⟩ | ⟨hlp, hcen⟩
  ·
    exfalso
    obtain ⟨J, hJcomp, hJdvd⟩ := hPL e hpchar β (hD.2 β (hD'le hβD')) hβne P hPle hPperf hPdvd
    have hJle : J ≤ GLAPLayer p (fixSubgroup β) := le_sSup hJcomp
    have hJne : J ≠ ⊥ := by
      intro hJbot
      rw [hJbot, Subgroup.card_bot] at hJdvd
      exact hp.not_dvd_one hJdvd
    exact hJne (le_bot_iff.1 (hJle.trans (le_of_eq (hgood β (hD'le hβD') hβne))))
  ·
    refine Or.inr (Or.inr (Or.inr ⟨hlp, ?_⟩))
    have hDle : D ≤ innAutDerived (TauCeti.CFSGIndex.lie e).Group ⊓
        Subgroup.centralizer (D' : Set (MulAut (TauCeti.CFSGIndex.lie e).Group)) := by
      refine le_inf hDin ?_
      intro d hd
      rw [Subgroup.mem_centralizer_iff]
      intro d' hd'
      exact (CFSG.LocalAnalysis.GLTheoremA.isElemAbelian_commute hD hd (hD'le hd')).symm
    rw [hcen] at hDle
    have hDeq : D = D' := le_antisymm hDle hD'le
    rw [hDeq, hD'card]

theorem kd264ExcNoGood_of_inputs (hOutCyc : KD264OutCyc) (hOuterIdx : KD264OuterIdx)
    (hInnGood : KD264InnGood) (hTriInnGood : KD264TriInnGood) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hPL : KD264PL p) : KD264ExcNoGood p := by
  intro e _ hpchar hpdvd D hD hDcard hgood
  by_cases hDin : D ≤ innAutDerived (TauCeti.CFSGIndex.lie e).Group
  · exact kd264ExcNoGood_of_inner hInnGood hp hp2 hPL e hpchar D hD hDcard hgood hDin
  · exact kd264ExcNoGood_of_outer hOutCyc hOuterIdx hTriInnGood hp hp2 hPL e hpchar hpdvd D hD
      hDcard hgood hDin

theorem kd264ExcNoGood_holds (hI : KD264LieInputs) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hPL : KD264PL p) : KD264ExcNoGood p :=
  kd264ExcNoGood_of_inputs hI.outCyc hI.outerIdx hI.innGood hI.triInnGood hp hp2 hPL

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
