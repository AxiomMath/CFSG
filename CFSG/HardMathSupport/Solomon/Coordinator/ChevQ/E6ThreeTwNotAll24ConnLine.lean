module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnStr
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24Dim
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeDiagParTw
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwCoreDefs

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Seitz
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LieType.SeitzGeneration.ExcWideThree

section Line

set_option linter.unusedSectionVars false


theorem twE6_conj_injective (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (q : ℕ)
    (hσ : ∀ c, σ c = c ^ q) (hKq : Nat.card K = q ^ 2) (hq2 : 2 ≤ q) :
    Function.Injective (twistedE6InndiagConj K σ) := by
  obtain ⟨hp, f, hf, hqf⟩ := prime_ringChar_and_eq_pow_of_card_sq K q hKq hq2
  refine twistedE6InndiagConj_injective hp hf ?_ σ ?_
  · rw [← hqf]
    exact hKq
  · intro c
    rw [← hqf]
    exact hσ c

theorem exists_matrix_lift_of_mem (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (q : ℕ)
    (hσ : ∀ c, σ c = c ^ q) (hKq : Nat.card K = q ^ 2) (hq2 : 2 ≤ q)
    {E : Subgroup (MulAut (twistedE6RootGroup K σ))} (hE : IsElemAbelian 3 E)
    (hED : E ≤ twistedE6Inn K σ ⊔ twistedE6Diag K σ) {f : MulAut (twistedE6RootGroup K σ)}
    (hf : f ∈ E) (hf1 : f ≠ 1) :
    ∃ h : twistedE6InndiagGL K σ, twistedE6InndiagConj K σ h = f ∧ h ≠ 1 ∧ h ^ 3 = 1 := by
  have hinj := twE6_conj_injective K σ q hσ hKq hq2
  have hmem : f ∈ (twistedE6InndiagConj K σ).range := by
    rw [range_twistedE6InndiagConj]
    exact hED hf
  obtain ⟨h, hh⟩ := hmem
  refine ⟨h, hh, ?_, ?_⟩
  · rintro rfl
    exact hf1 (hh.symm.trans (map_one _))
  · apply hinj
    rw [map_pow, hh, map_one]
    exact hE.2 f hf

theorem twE6MatFixDim_mem_of_mem (hD : TwE6Order3Dim) (K : Type) [Field K] [Finite K]
    (σ : K ≃+* K) (q : ℕ) (hK3 : ringChar K ≠ 3) (hσ : ∀ c, σ c = c ^ q)
    (hKq : Nat.card K = q ^ 2) (h3 : 3 ∣ q + 1) (hq2 : q ≠ 2)
    {E : Subgroup (MulAut (twistedE6RootGroup K σ))} (hE : IsElemAbelian 3 E)
    (hED : E ≤ twistedE6Inn K σ ⊔ twistedE6Diag K σ) {f : MulAut (twistedE6RootGroup K σ)}
    (hf : f ∈ E) (hf1 : f ≠ 1) :
    ∃ h : twistedE6InndiagGL K σ, twistedE6InndiagConj K σ h = f ∧ h ≠ 1 ∧
      twE6MatFixDim K σ h ∈ ({24, 28, 30, 36, 46} : Set ℕ) := by
  obtain ⟨h, hh, hh1, hh3⟩ := exists_matrix_lift_of_mem K σ q hσ hKq
    (by have := Nat.le_of_dvd (by omega) h3; omega) hE hED hf hf1
  exact ⟨h, hh, hh1, hD K σ q hK3 hσ hKq h3 hq2 h hh3 hh1⟩

theorem twE6MatFixDim_of_inner (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (q : ℕ)
    (hσ : ∀ c, σ c = c ^ q) (hKq : Nat.card K = q ^ 2) (hq2 : 2 ≤ q)
    (s : twistedE6RootGroup K σ) (h : twistedE6InndiagGL K σ)
    (hh : twistedE6InndiagConj K σ h = MulAut.conj s) :
    twE6MatFixDim K σ h = twE6FixDim K σ s := by
  have hinj := twE6_conj_injective K σ q hσ hKq hq2
  have hs : twistedE6RootGroup K σ ≤ twistedE6InndiagGL K σ := le_sup_left
  have hsh : twistedE6InndiagConj K σ ⟨(s : ModGL TwistTag.E6.tag K), hs s.2⟩ = MulAut.conj s := by
    ext c
    rfl
  have : h = ⟨(s : ModGL TwistTag.E6.tag K), hs s.2⟩ := hinj (hh.trans hsh.symm)
  subst this
  rfl

end Line

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
