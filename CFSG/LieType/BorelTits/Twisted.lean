module

public import CFSG.LieType.Chevalley.TwistPerfect
public import CFSG.LieType.Chevalley.TwistMapFixed
public import CFSG.LieType.BorelTits.DerivedQuotient
public import CFSG.LieType.BorelTits.Exceptional

public section

namespace CFSG.LieType.BorelTits

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem exists_units_sq_ne_one {K : Type} [Field K] [Finite K] (hK : 4 ≤ Nat.card K) :
    ∃ u : Kˣ, (u : K) ^ 2 ≠ 1 := by
  classical
  have := Fintype.ofFinite K
  obtain ⟨x, -, hx⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({0, 1, -1} : Finset K)) (t := Finset.univ) (by
      calc ({0, 1, -1} : Finset K).card ≤ 3 := Finset.card_le_three
        _ < Finset.univ.card := by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; omega)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
  obtain ⟨h0, h1, hm1⟩ := hx
  refine ⟨Units.mk0 x h0, fun h => ?_⟩
  rw [Units.val_mk0, sq] at h
  rcases mul_self_eq_one_iff.1 h with h' | h'
  · exact h1 h'
  · exact hm1 h'

theorem exists_sylow_le_commutator_twistFixed (t : TwistTag) (K : Type) [Field K] [Finite K]
    (σ : K →+* K) (p : ℕ) [Fact p.Prime] [CharP K p] (hσ : Function.Surjective σ)
    (hU : ∀ x ∈ (nativeData t.tag K).U, twistC t K σ x = x → x ∈ twistDerived t K σ) :
    ∃ S : Sylow p (twistFixed t K σ),
      (S : Subgroup (twistFixed t K σ)) ≤ commutator (twistFixed t K σ) := by
  obtain ⟨S, hS⟩ := exists_sylow_twistFixed t K σ p hσ
  refine ⟨S, fun x hx => ?_⟩
  rw [hS] at hx
  obtain ⟨y, hy, hyx⟩ := hU x hx x.2
  rwa [Subtype.ext hyx] at hy

theorem holds_twistedDerivedQuotient (t : TwistTag) (K : Type) [Field K] [Finite K]
    (σ : K →+* K) (p : ℕ) [Fact p.Prime] [CharP K p] (hσ : Function.Surjective σ)
    (hU : ∀ x ∈ (nativeData t.tag K).U, twistC t K σ x = x → x ∈ twistDerived t K σ) :
    Holds (DerivedCentralQuotient (twistedFixedGroup t K σ)) p := by
  obtain ⟨S, hS⟩ := exists_sylow_le_commutator_twistFixed t K σ p hσ hU
  exact holds_derivedCentralQuotient (twistedFixedGroup t K σ) (twistedFixedGroupEquiv t K σ)
    (holds_twistFixed t K σ p hσ) S hS

theorem holds_of_twistedChevalleyModel {G : Type} [Group G] {t : TwistTag} {p f : ℕ}
    [Fact p.Prime] (hf : 1 ≤ f) (h : TwistedChevalleyModel G t (p ^ f)) : Holds G p := by
  obtain ⟨K, _, _, hK, σ, hσc, ⟨e⟩⟩ := h
  have := Fintype.ofFinite K
  have hcard : Nat.card K = p ^ (f * t.order) := by rw [hK, pow_mul]
  have : CharP K p := charP_of_natCard_eq hcard
  have hσ : Function.Surjective σ := surjective_ringHom_of_finite K σ
  have hfr : ∀ c : K, c ^ Nat.card K = c := fun c => by
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.pow_card c
  have hq : 2 ≤ p ^ f :=
    (Nat.Prime.two_le Fact.out).trans (Nat.le_self_pow (by omega) p)
  have h4 : 4 ≤ Nat.card K := by
    rw [hK]
    have hm : 2 ≤ t.order := by cases t <;> decide
    calc 4 = 2 ^ 2 := rfl
      _ ≤ (p ^ f) ^ 2 := Nat.pow_le_pow_left hq 2
      _ ≤ (p ^ f) ^ t.order := Nat.pow_le_pow_right (by omega) hm
  obtain ⟨u, hu⟩ := exists_units_sq_ne_one h4
  have hU : ∀ x ∈ (nativeData t.tag K).U, twistC t K σ x = x → x ∈ twistDerived t K σ := by
    cases t with
    | E6 =>
      refine e6_U_le_twistDerived hσ (fun c => ?_) hu
      have hc : p ^ f * p ^ f = Nat.card K := by
        rw [hK]
        change _ = (p ^ f) ^ 2
        ring
      rw [hσc, hσc, ← pow_mul, hc, hfr]
    | D4 =>
      refine d4_U_le_twistDerived hσ (fun c => ?_) hu
      have hc : p ^ f * (p ^ f * p ^ f) = Nat.card K := by
        rw [hK]
        change _ = (p ^ f) ^ 3
        ring
      rw [hσc, hσc, hσc, ← pow_mul, ← pow_mul, hc, hfr]
  exact (holds_twistedDerivedQuotient t K σ p hσ hU).of_mulEquiv e.symm

theorem holds_of_chevalleyExceptionalModel {G : Type} [Group G]
    {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {p f : ℕ}
    (h : ChevalleyExceptionalModel G t p f) : Holds G p := by
  by_cases ht : t = .twistedE6
  · subst ht
    obtain ⟨hadm, hmodel⟩ := h
    have : Fact p.Prime := ⟨hadm.1⟩
    exact holds_of_twistedChevalleyModel hadm.2.1 hmodel
  by_cases ht' : t = .trialityD4
  · subst ht'
    obtain ⟨hadm, hmodel⟩ := h
    have : Fact p.Prime := ⟨hadm.1⟩
    exact holds_of_twistedChevalleyModel hadm.2.1 hmodel
  exact holds_of_chevalleyExceptionalModel_untwisted h ht ht'

end CFSG.LieType.BorelTits
