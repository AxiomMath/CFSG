module

public import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalThreeDefs
public import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPPrimeCoreBasics
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.Input19DeltaReduction

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.Proving

theorem isLocallyBalancedAbs_three_two_of_central {K : Type*} [Group K] [Finite K]
    (h : ∀ D : Subgroup (MulAut K), IsElemAbelian 3 D → Nat.card D = 9 →
      ∀ y ∈ Subgroup.centralizer (D : Set (MulAut K)), Nat.Coprime 3 (orderOf y) → y = 1) :
    IsLocallyBalancedAbs 3 2 K := by
  intro D hD hcard H _ _
  rw [eq_bot_iff]
  intro y hy
  rw [Subgroup.mem_bot]
  have hD1 : ∃ d ∈ D, d ≠ 1 := by
    by_contra hall
    push Not at hall
    have : Nat.card D = 1 := Subgroup.card_eq_one.2 (Subgroup.eq_bot_iff_forall _ |>.2 hall)
    rw [hcard] at this
    norm_num at this
  obtain ⟨d₀, hd₀, hd₀1⟩ := hD1
  have hmem : ∀ d ∈ D, d ≠ 1 → y ∈ GLAPPrimeCoreOf 3 (H ⊓ Subgroup.centralizer ({d} : Set (MulAut K))) := by
    intro d hd hd1
    have := (Subgroup.mem_iInf.1 hy d)
    have := (Subgroup.mem_iInf.1 this) hd
    exact (Subgroup.mem_iInf.1 this) hd1
  refine h D hD (by rw [hcard]; norm_num) y ?_ ?_ 
  · rw [Subgroup.mem_centralizer_iff]
    intro d hd
    by_cases hd1 : d = 1
    · rw [hd1, one_mul, mul_one]
    · have hy' : y ∈ H ⊓ Subgroup.centralizer ({d} : Set (MulAut K)) := by
        obtain ⟨z, -, hz⟩ := Subgroup.mem_map.1 (hmem d hd hd1)
        rw [← hz]
        exact z.2
      exact (Subgroup.mem_centralizer_singleton_iff.1 hy'.2).symm
  · have hc := coprime_card_GLAPPrimeCoreOf (G := MulAut K) Nat.prime_three
      (H ⊓ Subgroup.centralizer ({d₀} : Set (MulAut K)))
    have hdv : orderOf y ∣ Nat.card (GLAPPrimeCoreOf 3 (H ⊓ Subgroup.centralizer ({d₀} : Set (MulAut K)))) :=
      Subgroup.orderOf_dvd_natCard _ (hmem d₀ hd₀ hd₀1)
    exact Nat.Coprime.coprime_dvd_right hdv hc

end CFSG.HardMathSupport.Solomon.Coordinator
