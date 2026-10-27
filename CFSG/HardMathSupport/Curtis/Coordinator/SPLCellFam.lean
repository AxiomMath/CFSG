module

public import CFSG.HardMathSupport.Curtis.Coordinator.SPLLieCell
public import CFSG.HardMathSupport.Curtis.Coordinator.SPLCellTransport
public import CFSG.HardMathSupport.Curtis.Coordinator.SPLCellSp

public section

open CFSG.AGLEmbedding CFSG.Assembly.LowTwoRank

namespace CFSG.HardMathSupport.Curtis.Coordinator

theorem prime_facts {p r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hr : r.Prime) (hr1 : r ∣ p ^ 2 + 1)
    (hr2 : ¬ r ∣ p ^ 2 - 1) : 5 ≤ r ∧ ¬ r ∣ p - 1 := by
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  constructor
  · by_contra hlt
    push Not at hlt
    have hr2' := hr.two_le
    interval_cases r
    · exfalso
      apply hr2
      obtain ⟨m, rfl⟩ := hpodd
      have : (2 * m + 1) ^ 2 - 1 = 2 * (2 * m * m + 2 * m) := by
        have : (2 * m + 1) ^ 2 = 2 * (2 * m * m + 2 * m) + 1 := by ring
        omega
      rw [this]
      exact dvd_mul_right _ _
    · exfalso
      have hmod : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2 := by omega
      rcases hmod with h | h | h
      · have : (p ^ 2 + 1) % 3 = 1 := by simp [Nat.add_mod, Nat.pow_mod, h]
        omega
      · have : (p ^ 2 + 1) % 3 = 2 := by simp [Nat.add_mod, Nat.pow_mod, h]
        omega
      · have : (p ^ 2 + 1) % 3 = 2 := by simp [Nat.add_mod, Nat.pow_mod, h]
        omega
    · exact absurd hr (by norm_num)
  · intro h
    apply hr2
    refine h.trans ?_
    obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, by have := hp.pos; omega⟩
    refine ⟨m + 2, ?_⟩
    simp only [Nat.add_sub_cancel]
    have : (m + 1) ^ 2 = m * (m + 2) + 1 := by ring
    omega


@[expose] def SPLLieInnerCellFam (F : TauCeti.LieTypeIndex → Prop) : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (d : TauCeti.ValidLieTypeIndex), IsClassicalOrG2Index d.1 →
    F d.1 → Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group) →
    ∀ (p r : ℕ), p.Prime → p ≠ 2 → r.Prime → r ∣ p ^ 2 + 1 → ¬ r ∣ p ^ 2 - 1 →
    SPLCellFor S p r

@[expose] def IsIdxA : TauCeti.LieTypeIndex → Prop := fun i => ∃ r q, i = .A r q
@[expose] def IsIdxTwistedA : TauCeti.LieTypeIndex → Prop := fun i => ∃ r q, i = .twistedA r q
@[expose] def IsIdxB : TauCeti.LieTypeIndex → Prop := fun i => ∃ r q, i = .B r q
@[expose] def IsIdxD : TauCeti.LieTypeIndex → Prop := fun i => ∃ r q, i = .D r q
@[expose] def IsIdxTwistedD : TauCeti.LieTypeIndex → Prop := fun i => ∃ r q, i = .twistedD r q
@[expose] def IsIdxG2 : TauCeti.LieTypeIndex → Prop := fun i => ∃ q, i = .G2 q

theorem splLieInnerCell_of_families (hA : SPLLieInnerCellFam IsIdxA)
    (hTA : SPLLieInnerCellFam IsIdxTwistedA) (hB : SPLLieInnerCellFam IsIdxB)
    (hD : SPLLieInnerCellFam IsIdxD) (hTD : SPLLieInnerCellFam IsIdxTwistedD)
    (hG : SPLLieInnerCellFam IsIdxG2) : SPLLieInnerCell := by
  intro S _ _ d hd he p r hp hp2 hr hr1 hr2
  obtain ⟨idx, hv⟩ := d
  cases idx with
  | A r0 q => exact hA S ⟨.A r0 q, hv⟩ hd ⟨r0, q, rfl⟩ he p r hp hp2 hr hr1 hr2
  | twistedA r0 q => exact hTA S ⟨.twistedA r0 q, hv⟩ hd ⟨r0, q, rfl⟩ he p r hp hp2 hr hr1 hr2
  | B r0 q => exact hB S ⟨.B r0 q, hv⟩ hd ⟨r0, q, rfl⟩ he p r hp hp2 hr hr1 hr2
  | C r0 q => exact hd.elim
  | D r0 q => exact hD S ⟨.D r0 q, hv⟩ hd ⟨r0, q, rfl⟩ he p r hp hp2 hr hr1 hr2
  | twistedD r0 q => exact hTD S ⟨.twistedD r0 q, hv⟩ hd ⟨r0, q, rfl⟩ he p r hp hp2 hr hr1 hr2
  | G2 q => exact hG S ⟨.G2 q, hv⟩ hd ⟨q, rfl⟩ he p r hp hp2 hr hr1 hr2
  | E6 q => exact hd.elim
  | E7 q => exact hd.elim
  | E8 q => exact hd.elim
  | F4 q => exact hd.elim
  | twistedE6 q => exact hd.elim
  | trialityD4 q => exact hd.elim
  | suzuki m => exact hd.elim
  | reeG2 m => exact hd.elim
  | reeF4 m => exact hd.elim
  | tits => exact hd.elim


theorem splLieInnerCellFam_B : SPLLieInnerCellFam IsIdxB := by
  intro S _ _ d hd hF ⟨e⟩ p r hp hp2 hr hr1 hr2
  obtain ⟨r0, q, hdq⟩ := hF
  obtain ⟨idx, hv⟩ := d
  obtain rfl : idx = .B r0 q := hdq
  have hq : q.p = 2 := hd
  obtain ⟨n, f, hmodel⟩ : ∃ n f, StatedClassicalModel S .PSp n 2 f := by
    have hrange := ((TauCeti.LieTypeIndex.inStandardRange_iff _).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1)
    by_cases h2 : r0 = 2
    · subst h2
      have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e
      rw [hq] at h
      exact ⟨_, _, h⟩
    · have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even r0 q hv hq
        (by omega) e
      rw [hq] at h
      exact ⟨_, _, h⟩
  obtain ⟨⟨-, hf, hn, hne⟩, K, _, _, hK, ⟨eK⟩⟩ := hmodel
  obtain ⟨hr5, hrp⟩ := prime_facts hp hp2 hr hr1 hr2
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, hK])
  have hrq : ¬ (n = 2 ∧ 2 ^ f = 2) := fun h => hne (by rw [h.1, h.2])
  exact SPLCellFor.of_mulEquiv eK fun Ē ζ γ hE hcard hζp hζE hsolv hγ hγE hcomm hnt =>
    SPLCell.sp_cell_P hn hf hK hrq hp hp2 hr hr5 hrp Ē hE hcard ζ γ hζp hζE hsolv hγ hγE hcomm hnt

end CFSG.HardMathSupport.Curtis.Coordinator
