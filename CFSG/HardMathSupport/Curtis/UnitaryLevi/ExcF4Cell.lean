module

public import CFSG.HardMathSupport.Curtis.Coordinator.ExcLeafDefs
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.ExcSylowN
public import CFSG.HardMathSupport.Curtis.Proving.CentralizerMono
public import CFSG.HardMathSupport.Foote.E27.SporCentKill

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
  CFSG.HardMathSupport.Foote.E27 TauCeti Subgroup
open CFSG.HardMathSupport.Malle.E27Lie (InnerLeaf)
open CFSG.HardMathSupport.Curtis.Coordinator.ExcLeaf (IdxExc)
open CFSG.HardMathSupport.Curtis.Proving (eightyOne_dvd_centralizer_of_sub)

@[expose] def MonomialThreeCentralizerBoundF4 :
    Prop :=
  ∀ (K : Type) [Field K] [Finite K], 3 ∣ Nat.card K - 1 →
    ∀ n : monomialSub .F4 K, orderOf n = 3 →
      81 ∣ Nat.card (Subgroup.centralizer ({n} : Set (monomialSub .F4 K)))

theorem exists_sylow_centralizer_kill_adjointF4
    (K : Type) [Field K] [Finite K] (h3 : 3 ∣ Nat.card K - 1)
    (hN : ∀ n : monomialSub .F4 K, orderOf n = 3 →
      81 ∣ Nat.card (Subgroup.centralizer ({n} : Set (monomialSub .F4 K)))) :
    ∃ Q : Subgroup (adjointGroup .F4 K),
      Nat.card Q = 3 ^ (Nat.card (adjointGroup .F4 K)).factorization 3 ∧
        ∀ s ∈ Q, s ^ 3 = 1 → s ≠ 1 →
          81 ∣ Nat.card (Subgroup.centralizer ({s} : Set (adjointGroup .F4 K))) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite (adjointGroup .F4 K) := generated_group_finite .F4 K
  obtain ⟨P, hP⟩ := exists_sylow_three_le_monomialSub_F4 K h3
  refine ⟨P, ?_, ?_⟩
  · rw [P.card_eq_multiplicity]
  · intro s hs hs3 hs1
    have hsN : s ∈ monomialSub .F4 K := hP hs
    have hord : orderOf (⟨s, hsN⟩ : monomialSub .F4 K) = 3 := by
      rw [Subgroup.orderOf_mk]
      exact orderOf_eq_prime hs3 hs1
    exact eightyOne_dvd_centralizer_of_sub hsN (hN _ hord)

theorem innerLeaf_F4_one_of_monomialBound
    (hN : MonomialThreeCentralizerBoundF4) : InnerLeaf (IdxExc .F4 1) := by
  intro X _ _ K R T z h hz d hd e
  obtain ⟨i, hv⟩ := d
  obtain ⟨q, hq, hr, rfl⟩ := hd
  obtain ⟨ψ⟩ := e
  obtain ⟨F, _, _, hF, -, ⟨ε⟩⟩ :=
    exists_catEquiv_adjointGroup CFSG.TauCetiBridge.Even.chevalleyBridgesAll.f4 q hv
  have h3 : 3 ∣ Nat.card F - 1 := by rw [hF]; omega
  obtain ⟨Q, hQ, hk⟩ := exists_sylow_centralizer_kill_adjointF4 F h3 (hN F h3)
  exact h.false_of_centralizer_kill hz (ψ.trans ε) Q hQ hk

end CFSG.HardMathSupport.Curtis.UnitaryLevi

end
