module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.H248L227Main
public import CFSG.LocalAnalysis.GLTheoremA.CatA.H248FactsM
public import CFSG.HardMathSupport.Solomon.Coordinator.I22_7TrSub
public import CFSG.LocalAnalysis.GLTheoremA.CatA.H248L227Tr

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H248L227

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem l227FactM_of_outer
    (hOut : ∀ (A : Type) [Group A] [Finite A], CFSG.Open.IsKGroup A → ∀ {J : Subgroup A},
      IsComponentOf J ⊤ → Group.IsSolvable (Outer ↥J)) : H248.L227FactM := by
  intro p q hp hp2 hq hq2 hqp G _ _ K Q hK hlay hqs _ hrkp hQK hQ hQc hrk hrkM hquot
  have hperf : commutator ↥K = ⊤ := perfect_of_layer hlay
  have hlayer : GLAPLayer p (⊤ : Subgroup ↥K) = ⊤ := i227m_layer_top_of_subtype hp hlay
  have hcov : ∀ C : Subgroup ↥K, C.Normal → C ⊔ GLAPPrimeCore p ↥K = ⊤ → C = ⊤ :=
    fun C hC h => @cover_eq_top _ _ _ p hp hlayer hqs C hC h
  have hM : ∀ N : Subgroup ↥K, N.Normal → N ≠ ⊤ → N ≤ H248.M227 p K :=
    fun N hN hne => @le_comap_center_of_normal _ _ _ _ hqs hcov N hN hne
  have hSL : ∀ φ : ↥K →* Matrix.SpecialLinearGroup (Fin 2) (ZMod q), φ = 1 := fun φ =>
    sl2_hom_eq_one hp hp2 hq hq2 hqp (H248.M227 p K) hM hrkp φ
  have hWM : H248.W227 p K ≤ H248.M227 p K := by
    intro w hw
    have hwR : w ∈ GLAPPrimeCore p ↥K := Subgroup.commutator_le_left _ ⊤ hw
    rw [H248.M227, Subgroup.mem_comap, QuotientGroup.mk'_apply,
      (QuotientGroup.eq_one_iff w).2 hwR]
    exact Subgroup.one_mem _
  have hQx : IsPGroup q (Q.subgroupOf K) := hQ.of_equiv (Subgroup.subgroupOfEquivOfLe hQK).symm
  have hQxc : Nat.card (Q.subgroupOf K) = q ^ (Nat.card ↥K).factorization q := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQK).toEquiv]
    exact hQc
  exact coreIn_eq_of_subtype hq.one_lt
    (coreIn_eq_top_of_rankM hq hq2 hOut hK hperf (GLAPPrimeCore p ↥K) (H248.W227 p K) rfl hcov
      hSL (Q.subgroupOf K) hQx hQxc hrk hquot (H248.M227 p K) hWM hM hrkM)

end CFSG.LocalAnalysis.GLTheoremA.H248L227
