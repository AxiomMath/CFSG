module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwAutBalance

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.E6Heis

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.CrossChar

variable {K : Type*} [Group K] [Finite K] {p : ℕ}

theorem localDeltaIn_eq_bot_of_aut_components_rigid_comm (hp : p.Prime)
    (hinj : Function.Injective (MulAut.conj : K →* MulAut K))
    {H : Subgroup (MulAut K)} (hH : innerAut K ≤ H) {E : Subgroup (MulAut K)} (hE : E ≠ ⊥)
    {S : Set K}
    (hrig : ∀ δ ∈ H, Nat.Coprime p (orderOf δ) → (∀ e ∈ E, δ * e = e * δ) →
      (∀ s ∈ S, δ s = s) → δ = 1)
    (hcomp : ∀ s ∈ S, ∃ e ∈ E, e ≠ 1 ∧ ∃ L : Subgroup K, s ∈ L ∧ L ≤ fixSub e ∧
      CFSG.IsQuasisimple L ∧ (L.subgroupOf (fixSub e)).IsSubnormal ∧
      ¬ Nat.Coprime p (Nat.card L)) :
    localDeltaIn p H E = ⊥ := by
  refine eq_bot_iff.2 fun g hg => ?_
  obtain ⟨e₀, he₀, he₀1⟩ : ∃ e ∈ E, e ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hE ((Subgroup.eq_bot_iff_forall E).2 hcon)
  have : Finite (MulAut K) := Finite.of_injective (fun f : MulAut K => (f : K → K))
    fun f f' h => MulEquiv.ext (congrFun h)
  have hgC : ∀ e ∈ E, e ≠ 1 → g ∈ H ⊓ Subgroup.centralizer ({e} : Set (MulAut K)) := fun e he he1 =>
    CFSG.HardMathSupport.Timmesfeld.Balance.gLAPPrimeCoreOf_le_self' _
      (le_core_of_mem_localDeltaIn hg he he1)
  have hgH : g ∈ H := (hgC e₀ he₀ he₀1).1
  refine Subgroup.mem_bot.2
    (hrig g hgH (coprime_orderOf_of_mem_localDeltaIn hp hg he₀ he₀1) (fun e he => ?_)
      fun s hs => ?_)
  · by_cases he1 : e = 1
    · subst he1
      simp
    · exact (Subgroup.mem_centralizer_singleton_iff.1 (hgC e he he1).2)
  · obtain ⟨e, he, he1, L, hsL, hLC, hLq, hLsn, hLp⟩ := hcomp s hs
    exact le_fixSub_of_aut_component hp hinj hH hg he he1 hLC hLq hLsn hLp hsL

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.E6Heis
