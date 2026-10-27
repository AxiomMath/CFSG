module

public import Mathlib.GroupTheory.PGroup
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.ComplementConjugacy
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Cardinalities
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConj

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open scoped commutatorElement

universe u

theorem normalizes_commutator_of_commute {G : Type u} [Group G] {B P Q : Subgroup G}
    (hBQ : Q ≤ Subgroup.normalizer (B : Set G)) (hPQ : ⁅P, Q⁆ = ⊥) :
    Q ≤ Subgroup.normalizer ((⁅B, P⁆ : Subgroup G) : Set G) := by
  have hQP : ⁅Q, P⁆ = ⊥ := by
    simpa [Subgroup.commutator_comm] using hPQ
  have hQcentP : Q ≤ Subgroup.centralizer (P : Set G) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hQP
  have hQnormP : Q ≤ Subgroup.normalizer (P : Set G) :=
    hQcentP.trans (Subgroup.centralizer_le_normalizer (P : Set G))
  apply subgroup_le_normalizer_of_conj_mem
  intro q x hx
  have hmapB : B.map (MulAut.conj (q : G)).toMonoidHom = B := by
    have h := map_conj_mul_right_eq_of_mem_normalizer (H := B) (g := (1 : G))
      ⟨q, hBQ q.property⟩
    have hid : B.map (MulAut.conj (1 : G)).toMonoidHom = B := by
      ext y
      simp [MulAut.conj]
    simpa only [one_mul] using h.trans hid
  have hmapP : P.map (MulAut.conj (q : G)).toMonoidHom = P := by
    have h := map_conj_mul_right_eq_of_mem_normalizer (H := P) (g := (1 : G))
      ⟨q, hQnormP q.property⟩
    have hid : P.map (MulAut.conj (1 : G)).toMonoidHom = P := by
      ext y
      simp [MulAut.conj]
    simpa only [one_mul] using h.trans hid
  have hmapU : (⁅B, P⁆).map (MulAut.conj (q : G)).toMonoidHom = ⁅B, P⁆ := by
    rw [Subgroup.map_commutator, hmapB, hmapP]
  have hxmap : (MulAut.conj (q : G)).toMonoidHom x ∈
      (⁅B, P⁆).map (MulAut.conj (q : G)).toMonoidHom :=
    Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
  rw [hmapU] at hxmap
  simpa [MulAut.conj] using hxmap

theorem thompson_p_times_perfect
    {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P Q B : Subgroup G)
    (hPp : IsPGroup p P) (hBp : IsPGroup p B) (hQ : ⁅Q, Q⁆ = Q)
    (hPB : P ≤ Subgroup.normalizer (B : Set G))
    (hQB : Q ≤ Subgroup.normalizer (B : Set G))
    (hPQ : ⁅P, Q⁆ = ⊥)
    (hfixed : B ⊓ Subgroup.centralizer (P : Set G) ≤ Subgroup.centralizer (Q : Set G)) :
    ⁅B, Q⁆ = ⊥ := by
  classical
  induction hcard : Nat.card B using Nat.strong_induction_on generalizing B with
  | h n ih =>
      by_cases hBbot : B = ⊥
      · simp [hBbot]
      let U : Subgroup G := ⁅B, P⁆
      have hUleB : U ≤ B :=
        (Subgroup.le_normalizer_iff_commutator_le_left).mp hPB
      have hUltB : U < B := by
        simpa [U] using
          (GorensteinWalter.SchurZassenhaus.commutator_lt_of_pGroups B P hBp hPp hPB hBbot)
      have hUcard : Nat.card U < n := by
        rw [← hcard]
        exact natCard_lt_of_subgroup_lt hUltB
      have hUp : IsPGroup p U := hBp.to_le hUleB
      have hPnormU : P ≤ Subgroup.normalizer (U : Set G) := by
        simpa [U] using Subgroup.normalizer_commutator_ge_right B P
      have hQnormU : Q ≤ Subgroup.normalizer (U : Set G) :=
        normalizes_commutator_of_commute hQB hPQ
      have hfixedU : U ⊓ Subgroup.centralizer (P : Set G) ≤
          Subgroup.centralizer (Q : Set G) := by
        intro x hx
        exact hfixed ⟨hUleB hx.1, hx.2⟩
      have hUQ : ⁅U, Q⁆ = ⊥ :=
        ih (Nat.card U) hUcard (B := U) hUp hPnormU hQnormU hfixedU rfl
      have hPQB : ⁅⁅P, Q⁆, B⁆ = ⊥ := by simp [hPQ]
      have hQBP : ⁅⁅Q, B⁆, P⁆ = ⊥ :=
        Subgroup.commutator_commutator_eq_bot_of_rotate hUQ hPQB
      have hBQcentP : ⁅B, Q⁆ ≤ Subgroup.centralizer (P : Set G) := by
        have h := (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hQBP
        simpa [Subgroup.commutator_comm] using h
      have hBQleB : ⁅B, Q⁆ ≤ B :=
        (Subgroup.le_normalizer_iff_commutator_le_left).mp hQB
      have hBQcentQ : ⁅B, Q⁆ ≤ Subgroup.centralizer (Q : Set G) :=
        (le_inf hBQleB hBQcentP).trans hfixed
      have hdouble : ⁅⁅B, Q⁆, Q⁆ = ⊥ :=
        (Subgroup.commutator_eq_bot_iff_le_centralizer).mpr hBQcentQ
      have h1 : ⁅⁅Q, B⁆, Q⁆ = ⊥ := by rw [Subgroup.commutator_comm Q B]; exact hdouble
      have h2 : ⁅⁅Q, Q⁆, B⁆ = ⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate h1 hdouble
      rw [hQ] at h2
      rw [Subgroup.commutator_comm]
      exact h2

end CFSG.CGT.PushingUpLit.CGT6
