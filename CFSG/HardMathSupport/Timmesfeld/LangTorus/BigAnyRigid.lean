module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.BigAnyDefs
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidCriterion
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidRank
public import CFSG.Sporadic.He.Setup

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.DefChar CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

set_option linter.unusedSectionVars false

section Statements

@[expose] def CentralizerTrivialAny (τ : Tag) : Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] (p : ℕ) (S : LangSetup τ L p), τ ≠ .G2 → 3 ≤ S.D.q →
    ∀ {D₁ : Subgroup (ModGL τ L)}, D₁ ≤ S.E → BigAnyComponentsGenerate S D₁ →
      CentralizerTrivial S D₁

@[expose] def NoFrobeniusInnerAny (τ : Tag) : Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] (p : ℕ) (S : LangSetup τ L p), τ ≠ .G2 →
    (S.D.q ≠ 4 ∨ SimplyLacedTag τ) → ∀ {D₁ : Subgroup (ModGL τ L)}, D₁ ≤ S.E →
      HasBigAnyComponent S D₁ → NoFrobeniusInner S D₁

end Statements

section Classes

@[expose] def InnerPlaneBalanceSmall (k : LieFamily) (e : ℕ) : Prop :=
  ∀ (q : TauCeti.PrimePower) (hv : (excIndex k q).Valid) (p : ℕ), p.Prime → 7 ≤ p → p ≠ q.p →
    orderOf ((q.card : ℕ) : ZMod p) = e → q.card ≤ 3 →
      InnerPlaneBalance p (CatT ⟨excIndex k q, hv⟩)

theorem small_field_order_six {p c : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) (hc : c = 2 ∨ c = 3)
    (he : orderOf ((c : ℕ) : ZMod p) = 6) : c = 3 ∧ p = 7 := by
  have h6 : ((c : ℕ) : ZMod p) ^ 6 = 1 := by rw [← he]; exact pow_orderOf_eq_one _
  have hdvd : p ∣ c ^ 6 - 1 := by
    have h1 : 1 ≤ c ^ 6 := Nat.one_le_pow _ _ (by omega)
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub h1]
    push_cast
    rw [h6, sub_self]
  have p3 : ¬ p ∣ 3 := fun h => by have := Nat.le_of_dvd (by norm_num) h; omega
  have p2 : ¬ p ∣ 2 := fun h => by have := Nat.le_of_dvd (by norm_num) h; omega
  rcases hc with rfl | rfl
  · exfalso
    have h63 : p ∣ 7 * (3 * 3) := by simpa using hdvd
    rcases (Nat.Prime.dvd_mul hp).1 h63 with h | h
    · have := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h
      subst this
      have h3 := orderOf_dvd_of_pow_eq_one (show (((2 : ℕ) : ZMod 7)) ^ 3 = 1 by decide)
      rw [he] at h3
      omega
    · rcases (Nat.Prime.dvd_mul hp).1 h with h | h <;> exact p3 h
  · refine ⟨rfl, ?_⟩
    have h728 : p ∣ 7 * (13 * (2 * (2 * 2))) := by simpa using hdvd
    rcases (Nat.Prime.dvd_mul hp).1 h728 with h | h
    · exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h
    · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
      · exfalso
        have := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h
        subst this
        have h3 := orderOf_dvd_of_pow_eq_one (show (((3 : ℕ) : ZMod 13)) ^ 3 = 1 by decide)
        rw [he] at h3
        omega
      · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
        · exact absurd h p2
        · rcases (Nat.Prime.dvd_mul hp).1 h with h | h <;> exact absurd h p2

theorem InnerPlaneBalanceSmall.of_E8_six_three_seven
    (h : ∀ (q : TauCeti.PrimePower) (hv : (excIndex .E8 q).Valid), q.card = 3 →
      InnerPlaneBalance 7 (CatT ⟨excIndex .E8 q, hv⟩)) : InnerPlaneBalanceSmall .E8 6 := by
  intro q hv p hp hp7 _ he hq3
  have hq2 : 2 ≤ q.card := by
    have := Nat.one_lt_pow q.exponent_pos.ne' q.prime_p.one_lt
    rw [TauCeti.PrimePower.card_def]
    omega
  obtain ⟨h3, rfl⟩ := small_field_order_six hp hp7 (by omega) he
  exact h q hv h3

end Classes

end CFSG.HardMathSupport.Timmesfeld.LangTorus
