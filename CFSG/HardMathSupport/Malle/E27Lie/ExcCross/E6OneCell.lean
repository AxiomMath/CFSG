module

public import CFSG.HardMathSupport.Malle.E27Lie.ExcCross.E6OneBound
public import CFSG.HardMathSupport.Curtis.Coordinator.ExcLeafDefs
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.ExcSylowN
public import CFSG.HardMathSupport.Curtis.Proving.CentralizerMono
public import CFSG.HardMathSupport.Foote.E27.SporCentKill
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.E6Index

public section

namespace CFSG.HardMathSupport.Malle.E27Lie.ExcCross

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
  CFSG.HardMathSupport.Foote.E27 TauCeti Subgroup
open CFSG.HardMathSupport.Malle.E27Lie (InnerLeaf)
open CFSG.HardMathSupport.Curtis.Coordinator.ExcLeaf (IdxExc)
open CFSG.HardMathSupport.Curtis.Proving (eightyOne_dvd_centralizer_of_sub)
open CFSG.HardMathSupport.Curtis.UnitaryLevi (exists_sylow_three_le_of_factorization_eq)

section E6Cell


theorem exists_sylow_three_le_monomialSub_E6 (K : Type) [Field K] [Finite K]
    (h3 : 3 ∣ Nat.card K - 1) :
    ∃ P : Sylow 3 (adjointGroup .E6 K),
      (P : Subgroup (adjointGroup .E6 K)) ≤ monomialSub .E6 K := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite (adjointGroup .E6 K) := generated_group_finite .E6 K
  refine exists_sylow_three_le_of_factorization_eq _ ?_
  have hidx := CFSG.HardMathSupport.Timmesfeld.Tables.T1b.index_monomialSub_not_dvd_three
    (K := K) h3
  have hcard := Subgroup.card_mul_index (monomialSub .E6 K)
  have h0 : Nat.card (monomialSub .E6 K) ≠ 0 := Nat.card_pos.ne'
  have h1 : (monomialSub .E6 K).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  rw [← hcard, Nat.factorization_mul h0 h1, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hidx, add_zero]

theorem exists_sylow_centralizer_kill_adjointE6 (K : Type) [Field K] [Finite K]
    (h3 : 3 ∣ Nat.card K - 1) :
    ∃ Q : Subgroup (adjointGroup .E6 K),
      Nat.card Q = 3 ^ (Nat.card (adjointGroup .E6 K)).factorization 3 ∧
        ∀ s ∈ Q, s ^ 3 = 1 → s ≠ 1 →
          81 ∣ Nat.card (Subgroup.centralizer ({s} : Set (adjointGroup .E6 K))) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite (adjointGroup .E6 K) := generated_group_finite .E6 K
  obtain ⟨P, hP⟩ := exists_sylow_three_le_monomialSub_E6 K h3
  refine ⟨P, ?_, ?_⟩
  · rw [P.card_eq_multiplicity]
  · intro s hs hs3 hs1
    have hsN : s ∈ monomialSub .E6 K := hP hs
    have hord : orderOf (⟨s, hsN⟩ : monomialSub .E6 K) = 3 := by
      rw [Subgroup.orderOf_mk]
      exact orderOf_eq_prime hs3 hs1
    exact eightyOne_dvd_centralizer_of_sub hsN (eightyOne_dvd_centralizer_E6 K h3 _ hord)

theorem innerLeaf_E6_one : InnerLeaf (IdxExc .E6 1) := by
  intro X _ _ K R T z h hz d hd e
  obtain ⟨i, hv⟩ := d
  obtain ⟨q, hq, hr, rfl⟩ := hd
  obtain ⟨ψ⟩ := e
  obtain ⟨F, _, _, hF, -, ⟨ε⟩⟩ :=
    exists_catEquiv_adjointGroup CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e6 q hv
  have h3 : 3 ∣ Nat.card F - 1 := by rw [hF]; omega
  obtain ⟨Q, hQ, hk⟩ := exists_sylow_centralizer_kill_adjointE6 F h3
  exact h.false_of_centralizer_kill hz (ψ.trans ε) Q hQ hk

end E6Cell

end CFSG.HardMathSupport.Malle.E27Lie.ExcCross

end
