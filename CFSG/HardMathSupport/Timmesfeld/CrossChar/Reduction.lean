module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.OuterPlane
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalThreeDefs
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.Tables112Families

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator

theorem isLocallyBalancedAbs_of_innerPlanes {K : Type*} [Group K] {p : ℕ} (hp : p.Prime)
    (hcyc : IsCyclic (MulAut K ⧸ innerAut K))
    (h : ∀ E : Subgroup (MulAut K), E ≤ innerAut K → IsElemAbelian p E → Nat.card E = p ^ 2 →
      ∀ H : Subgroup (MulAut K), innerAut K ≤ H → localDeltaIn p H E = ⊥) :
    IsLocallyBalancedAbs p 3 K := by
  intro D hD hcard H hH _
  obtain ⟨E, hED, hEin, hE, hEc⟩ := exists_inner_plane_of_cyclic hcyc hp D hD hcard
  exact le_bot_iff.1 ((localDeltaIn_antitone H hED).trans (h E hEin hE hEc H hH).le)

theorem localDeltaIn_eq_bot_of_faithful_component {K : Type*} [Group K] [Finite K] {p : ℕ}
    (hp : p.Prime) (hinj : Function.Injective (MulAut.conj : K →* MulAut K))
    {H D : Subgroup (MulAut K)} {x : MulAut K} (hx : x ∈ D) (hx1 : x ≠ 1) (T : Subgroup K)
    (hTC : T.map (MulAut.conj : K →* MulAut K) ≤ H ⊓ Subgroup.centralizer ({x} : Set (MulAut K)))
    (hcomp : CFSG.IsComponent ((T.map (MulAut.conj : K →* MulAut K)).subgroupOf
      (H ⊓ Subgroup.centralizer ({x} : Set (MulAut K)))))
    (hTp : ¬ Nat.Coprime p (Nat.card T))
    (hfaith : ∀ g : MulAut K, Nat.Coprime p (orderOf g) → (∀ t ∈ T, g t = t) → g = 1) :
    localDeltaIn p H D = ⊥ := by
  refine eq_bot_iff.2 fun g hg => ?_
  rw [Subgroup.mem_bot]
  exact hfaith g (coprime_orderOf_of_mem_localDeltaIn hp hg hx hx1)
    fun t ht => mem_fixSub.1 (le_fixSub_of_component hp hinj hg hx hx1 hTC hcomp hTp ht)

end CFSG.HardMathSupport.Timmesfeld.CrossChar
