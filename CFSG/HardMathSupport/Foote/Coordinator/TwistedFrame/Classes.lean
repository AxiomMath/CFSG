module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.ClassLeaves
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Transport
public import CFSG.LieType.SeitzGeneration.ExcAnisotropicClasses
public import CFSG.Sporadic.He.Setup

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
open CFSG.TauCetiBridge TauCeti
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame

set_option linter.unusedSectionVars false

theorem not_orderOf_two_zmod_seven : orderOf ((2 : ℕ) : ZMod 7) ≠ 6 := by
  have h3 : ((2 : ℕ) : ZMod 7) ^ 3 = 1 := by decide
  intro h
  have := orderOf_dvd_of_pow_eq_one h3
  rw [h] at this
  omega

theorem three_le_of_orderOf_six {p q : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (h : orderOf ((q : ℕ) : ZMod p) = 6) : 3 ≤ q := by
  by_contra hlt
  push Not at hlt
  have : Fact p.Prime := ⟨hp⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 := by omega
  rcases hq with rfl | rfl | rfl
  · simp at h
  · simp at h
  · have h6 : ((2 : ℕ) : ZMod p) ^ 6 = 1 := by rw [← h]; exact pow_orderOf_eq_one _
    have h63 : ((63 : ℕ) : ZMod p) = 0 := by
      have : ((2 : ℕ) : ZMod p) ^ 6 - 1 = 0 := sub_eq_zero.2 h6
      have e : ((63 : ℕ) : ZMod p) = ((2 : ℕ) : ZMod p) ^ 6 - 1 := by norm_num
      rw [e]
      exact this
    have hdvd : p ∣ 63 := (ZMod.natCast_eq_zero_iff 63 p).1 h63
    have h63' : (63 : ℕ) = 7 * 9 := by norm_num
    have hp7 : p = 7 := by
      rw [h63'] at hdvd
      rcases (Nat.Prime.dvd_mul hp).1 hdvd with h7 | h9
      · exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h7
      · exfalso
        have h3 : p ∣ 3 := hp.dvd_of_dvd_pow (show p ∣ 3 ^ 2 by norm_num; exact h9)
        have := Nat.le_of_dvd (by norm_num) h3
        omega
    subst hp7
    exact not_orderOf_two_zmod_seven h


theorem seitzExcAnisotropicF4Class_six_of_leaves (h : TwClassLeaves TwClass.f4Six) :
    SeitzExcAnisotropicF4Class 6 := by
  intro d p hp _ _ _ E hE hcard hS
  obtain ⟨hin, -, ⟨hp5, q, hdq, -, hord⟩, -, -⟩ := hS
  obtain ⟨d₁, hv⟩ := d
  simp only at hdq
  subst hdq
  obtain ⟨K, _, _, hKq, -, ⟨e⟩⟩ :=
    exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.f4 q hv
  have : Fintype K := Fintype.ofFinite K
  have hordK : orderOf ((Nat.card K : ℕ) : ZMod p) = 6 := by rw [hKq]; exact hord
  have hK3 : 3 ≤ Nat.card K := three_le_of_orderOf_six hp hp5 hordK
  refine planeGen_of_native_closure e center_adjointGroup_eq_bot (fun E₀ hE₀p hE₀c => ?_) hE hcard hin
  exact closure_centralizers_eq_top_of_class TwClass.f4Six h K hK3 hp hp5 hordK E₀ hE₀p hE₀c

theorem seitzExcAnisotropicE6Class_six_of_leaves (h : TwClassLeaves TwClass.e6Six) :
    SeitzExcAnisotropicE6Class 6 := by
  intro d p hp _ _ _ E hE hcard hS
  obtain ⟨hin, -, ⟨hp5, q, hdq, -, hord⟩, -, -⟩ := hS
  obtain ⟨d₁, hv⟩ := d
  simp only at hdq
  subst hdq
  obtain ⟨K, _, _, hKq, -, ⟨e⟩⟩ :=
    exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e6 q hv
  have : Fintype K := Fintype.ofFinite K
  have hordK : orderOf ((Nat.card K : ℕ) : ZMod p) = 6 := by rw [hKq]; exact hord
  have hK3 : 3 ≤ Nat.card K := three_le_of_orderOf_six hp hp5 hordK
  refine planeGen_of_native_closure e center_adjointGroup_eq_bot (fun E₀ hE₀p hE₀c => ?_) hE hcard hin
  exact closure_centralizers_eq_top_of_class TwClass.e6Six h K hK3 hp hp5 hordK E₀ hE₀p hE₀c

theorem seitzExcAnisotropicE8Class_ten_of_leaves (h : TwClassLeaves TwClass.e8Ten) :
    SeitzExcAnisotropicE8Class 10 := by
  intro d p hp _ _ _ E hE hcard hS
  obtain ⟨hin, -, ⟨hp5, q, hdq, -, hord⟩, -, -⟩ := hS
  obtain ⟨d₁, hv⟩ := d
  simp only at hdq
  subst hdq
  obtain ⟨K, _, _, hKq, -, ⟨e⟩⟩ :=
    exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e8 q hv
  have : Fintype K := Fintype.ofFinite K
  have hordK : orderOf ((Nat.card K : ℕ) : ZMod p) = 10 := by rw [hKq]; exact hord
  have hK2 : TwClass.e8Ten.minQ ≤ Nat.card K := Finite.one_lt_card
  refine planeGen_of_native_closure e center_adjointGroup_eq_bot (fun E₀ hE₀p hE₀c => ?_) hE hcard hin
  exact closure_centralizers_eq_top_of_class TwClass.e8Ten h K hK2 hp hp5 hordK E₀ hE₀p hE₀c

theorem seitzExcAnisotropicE8Class_twelve_of_leaves (h : TwClassLeaves TwClass.e8Twelve) :
    SeitzExcAnisotropicE8Class 12 := by
  intro d p hp _ _ _ E hE hcard hS
  obtain ⟨hin, -, ⟨hp5, q, hdq, -, hord⟩, -, -⟩ := hS
  obtain ⟨d₁, hv⟩ := d
  simp only at hdq
  subst hdq
  obtain ⟨K, _, _, hKq, -, ⟨e⟩⟩ :=
    exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e8 q hv
  have : Fintype K := Fintype.ofFinite K
  have hordK : orderOf ((Nat.card K : ℕ) : ZMod p) = 12 := by rw [hKq]; exact hord
  have hK2 : TwClass.e8Twelve.minQ ≤ Nat.card K := Finite.one_lt_card
  refine planeGen_of_native_closure e center_adjointGroup_eq_bot (fun E₀ hE₀p hE₀c => ?_) hE hcard hin
  exact closure_centralizers_eq_top_of_class TwClass.e8Twelve h K hK2 hp hp5 hordK E₀ hE₀p hE₀c

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame
