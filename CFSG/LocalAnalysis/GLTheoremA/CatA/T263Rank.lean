module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267Cover

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA

section Bounds

variable {G : Type} [Group G] [Finite G]

theorem glaTwoLocal_eq (p : ℕ) : GLATwoLocalRank p G = CFSG.Open.twoLocalPrimeRank p G := rfl

theorem exp_le_card_of_mem {p : ℕ} [Fact p.Prime] {H : Subgroup G} {k : ℕ}
    (hk : k ∈ {k | ∃ E : Subgroup G, E ≤ H ∧ CFSG.Open.IsElemAbelian p E ∧ Nat.card E = p ^ k}) : k ≤ Nat.card G := by
  obtain ⟨E, -, -, hE⟩ := hk
  have h1 : p ^ k ≤ Nat.card G := hE ▸ Subgroup.card_le_card_group E
  have h2 : k < p ^ k := Nat.lt_pow_self (Fact.out : p.Prime).one_lt
  omega

theorem bdd_elemAbelian (p : ℕ) [Fact p.Prime] (H : Subgroup G) :
    BddAbove {k | ∃ E : Subgroup G, E ≤ H ∧ CFSG.Open.IsElemAbelian p E ∧ Nat.card E = p ^ k} :=
  ⟨Nat.card G, fun _ hk => exp_le_card_of_mem hk⟩

theorem pRank_le_card (p : ℕ) [Fact p.Prime] (H : Subgroup G) : CFSG.Open.pRank p H ≤ Nat.card G :=
  csSup_le' fun _ hk => exp_le_card_of_mem hk

theorem twoLocal_bdd (p : ℕ) [Fact p.Prime] :
    BddAbove {k | ∃ H : Subgroup G, CFSG.Open.IsTwoLocal H ∧ CFSG.Open.pRank p H = k} :=
  ⟨Nat.card G, by rintro _ ⟨H, -, rfl⟩; exact pRank_le_card p H⟩

theorem le_pRank {p : ℕ} [Fact p.Prime] {H E : Subgroup G} {k : ℕ} (hEH : E ≤ H) (hE : CFSG.Open.IsElemAbelian p E)
    (hk : Nat.card E = p ^ k) : k ≤ CFSG.Open.pRank p H :=
  le_csSup (bdd_elemAbelian p H) ⟨E, hEH, hE, hk⟩

theorem le_twoLocal_of_pRank {p : ℕ} [Fact p.Prime] {K : Subgroup G} {k : ℕ} (hK : CFSG.Open.IsTwoLocal K)
    (hk : k ≤ CFSG.Open.pRank p K) : k ≤ CFSG.Open.twoLocalPrimeRank p G :=
  hk.trans (le_csSup (twoLocal_bdd p) ⟨K, hK, rfl⟩)

theorem pRank_normalizer_le {p : ℕ} [Fact p.Prime] {T : Subgroup G} (hT : T ≠ ⊥) (hT2 : IsPGroup 2 T) :
    CFSG.Open.pRank p (Subgroup.normalizer (T : Set G)) ≤ CFSG.Open.twoLocalPrimeRank p G :=
  le_csSup (twoLocal_bdd p) ⟨_, ⟨T, hT, hT2, rfl⟩, rfl⟩

theorem card_le_of_normalizes {p : ℕ} [Fact p.Prime] {T E : Subgroup G} (hT : T ≠ ⊥) (hT2 : IsPGroup 2 T)
    (hE : CFSG.Open.IsElemAbelian p E) (hEN : E ≤ Subgroup.normalizer (T : Set G)) :
    Nat.card E ≤ p ^ CFSG.Open.twoLocalPrimeRank p G := by
  obtain ⟨k, hk⟩ := (isPGroup_of_isElemAbelian hE).exists_card_eq
  have h1 : k ≤ CFSG.Open.pRank p (Subgroup.normalizer (T : Set G)) := le_pRank hEN hE hk
  have h2 := h1.trans (pRank_normalizer_le hT hT2)
  rw [hk]
  exact Nat.pow_le_pow_right (Fact.out : p.Prime).pos h2

end Bounds

section Lift

variable {A : Type} [Group A] [Finite A]

theorem lift_normalizing {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (N : Subgroup A) [N.Normal]
    (hN : ¬ p ∣ Nat.card N) {Pb Eb : Subgroup (A ⧸ N)} (hP : Pb ≠ ⊥) (hP2 : IsPGroup 2 Pb)
    (hE : CFSG.Open.IsElemAbelian p Eb) (hEN : Eb ≤ Subgroup.normalizer (Pb : Set (A ⧸ N))) :
    ∃ T E : Subgroup A, T ≠ ⊥ ∧ IsPGroup 2 T ∧ CFSG.Open.IsElemAbelian p E ∧ Nat.card E = Nat.card Eb ∧
      E ≤ Subgroup.normalizer (T : Set A) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨S, hSel, hSmap, hScard⟩ := CFSG.LocalAnalysis.GLTheoremB.exists_elemAbelian_lift N hN hE
  have hEN' : S.map (QuotientGroup.mk' N) ≤ Subgroup.normalizer (Pb : Set (A ⧸ N)) := by
    rw [hSmap]
    exact hEN
  obtain ⟨T, hT2, hSN, hTmap, -, -⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.S267.exists_twoGroup_lift hp hp2 N hN hP2 (isPGroup_of_isElemAbelian hSel) hEN'
  refine ⟨T, S, ?_, hT2, hSel, hScard, hSN⟩
  intro hT0
  apply hP
  rw [← hTmap, hT0, Subgroup.map_bot]

end Lift

section Quot

variable {G : Type} [Group G] [Finite G]

theorem twoLocalPrimeRank_quot_le {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (H : Subgroup G) (N : Subgroup ↥H)
    [N.Normal] (hN : ¬ p ∣ Nat.card N) :
    CFSG.Open.twoLocalPrimeRank p (↥H ⧸ N) ≤ CFSG.Open.twoLocalPrimeRank p G := by
  haveI : Fact p.Prime := ⟨hp⟩
  unfold twoLocalPrimeRank
  apply csSup_le'
  rintro k ⟨K, ⟨Pb, hP, hP2, rfl⟩, rfl⟩
  have hK : CFSG.Open.pRank p (Subgroup.normalizer (Pb : Set (↥H ⧸ N))) ≤ CFSG.Open.twoLocalPrimeRank p G := by
    apply csSup_le'
    rintro j ⟨Eb, hEbK, hEb, hj⟩
    obtain ⟨T, E, hT, hT2, hE, hEcard, hEN⟩ := lift_normalizing hp hp2 N hN hP hP2 hEb hEbK
    have hTG : (T.map H.subtype) ≠ ⊥ := fun h => hT ((Subgroup.map_eq_bot_iff_of_injective T H.subtype_injective).1 h)
    have hTG2 : IsPGroup 2 (T.map H.subtype) := hT2.map _
    have hEG : CFSG.Open.IsElemAbelian p (E.map H.subtype) := CFSG.Open.IsElemAbelian.map hE H.subtype
    have hEGcard : Nat.card (E.map H.subtype) = p ^ j := by
      rw [Subgroup.card_map_of_injective H.subtype_injective, hEcard, hj]
    have hENG : E.map H.subtype ≤ Subgroup.normalizer ((T.map H.subtype : Subgroup G) : Set G) :=
      (Subgroup.map_mono hEN).trans (Subgroup.le_normalizer_map _)
    exact le_pRank hENG hEG hEGcard |>.trans (pRank_normalizer_le hTG hTG2)
  exact hK
end Quot

end CFSG.LocalAnalysis.GLTheoremA.T263

end
