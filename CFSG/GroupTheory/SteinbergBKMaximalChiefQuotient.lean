module

public import CFSG.GroupTheory.SteinbergBKInvariantChiefSeries
public import CFSG.GroupTheory.SteinbergBKChiefFactorModule

public section

namespace CFSG.GroupTheory.SteinbergBK

theorem maximal_normal_chief_quotient {G : Type*} [Group G] [Finite G] (hG : Group.IsSolvable G)
    (K : Subgroup G) [K.Normal] (hK : K ≠ ⊥) :
    ∃ (L : Subgroup G) (_ : L.Normal), L < K ∧
      (∀ Z : Subgroup G, Z.Normal → ¬ (L < Z ∧ Z < K)) ∧
      ∃ q e : ℕ, q.Prime ∧ 1 ≤ e ∧ IsElementaryAbelian q (chiefQuot K L) ∧
        Nat.card (chiefQuot K L) = q ^ e := by
  obtain ⟨m, Ns, h0, hm, hnorm, hstep, -⟩ := invariant_chief_series K
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := by
    refine Nat.exists_eq_succ_of_ne_zero fun hm0 => hK ?_
    subst hm0
    rw [← hm, ← h0]
    rfl
  have hlast : (Fin.last n).succ = Fin.last (n + 1) := Fin.succ_last n
  have := hnorm (Fin.last n).castSucc
  obtain ⟨hlt, hchief⟩ := hstep (Fin.last n)
  rw [hlast, hm] at hlt hchief
  obtain ⟨q, e, hq, he, helem, hcard, -⟩ := solvable_chief_factor_module hG hlt hchief
  exact ⟨_, this, hlt, hchief, q, e, hq.out, he, helem, hcard⟩

end CFSG.GroupTheory.SteinbergBK
