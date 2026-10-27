module

public import CFSG.LocalAnalysis.LargeEvenClassification.ElementarySubgroupPathsExchange

public section

namespace CFSG.LargeEvenClassification.Helpers

open CFSG.Open

universe u

theorem elementary_equal_rank_subgroup_path {D : Type u} [CommGroup D] [Finite D]
    {p k d : ℕ} (hprime : p.Prime) (hD : ∀ x : D, x ^ p = 1)
    (hk : 1 ≤ k) (X Y : Subgroup D) (hXcard : Nat.card X = p ^ k)
    (hYcard : Nat.card Y = p ^ k) (hJcard : Nat.card (X ⊓ Y : Subgroup D) = p ^ d) :
    ∃ n : ℕ, n ≤ k - d ∧ ∃ path : Fin (n + 1) → Subgroup D,
      path 0 = X ∧ path (Fin.last n) = Y ∧
      (∀ i, Nat.card (path i) = p ^ k) ∧
      ∀ i : Fin n, Nat.card (path i.castSucc ⊓ path i.succ : Subgroup D) =
        p ^ (k - 1) := by
  have hdle : d ≤ k := by
    apply (Nat.pow_le_pow_iff_right hprime.one_lt).mp
    rw [← hJcard, ← hXcard]
    exact Subgroup.card_le_of_le inf_le_left
  generalize hdeficiency : k - d = deficiency
  induction deficiency using Nat.strong_induction_on generalizing X d with
  | h deficiency induction =>
    by_cases hdk : d = k
    · have hXY : X = Y := by
        have hJX : X ⊓ Y = X := Subgroup.eq_of_le_of_card_ge inf_le_left (by
          rw [hJcard, hdk, hXcard])
        have hXYle : X ≤ Y := hJX ▸ (inf_le_right : X ⊓ Y ≤ Y)
        exact Subgroup.eq_of_le_of_card_ge hXYle (by rw [hXcard, hYcard])
      refine ⟨0, by omega, fun _ => X, rfl, hXY, fun _ => hXcard, ?_⟩
      intro i
      exact Fin.elim0 i
    · have hdlt : d < k := by
        by_cases hdZero : d = 0
        · rw [hdZero]
          exact hk
        · omega
      obtain ⟨X₁, d₁, hX₁card, hstep, hJ₁card, hd₁large, hd₁le⟩ :=
        elementary_path_exchange hprime hD X Y hXcard hYcard hJcard hdlt
      have hsmaller : k - d₁ < deficiency := by omega
      obtain ⟨n, hn, path, hfirst, hlast, hcards, hsteps⟩ :=
        induction (k - d₁) hsmaller X₁ hX₁card hJ₁card hd₁le rfl
      let extended : Fin (n + 2) → Subgroup D := Fin.cons X path
      refine ⟨n + 1, by omega, extended, ?_, ?_, ?_, ?_⟩
      · exact Fin.cons_zero _ _
      · simpa only [extended, Fin.cons_last] using hlast
      · intro i
        refine Fin.cases hXcard (fun j => ?_) i
        simpa only [extended, Fin.cons_succ] using hcards j
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simpa only [extended, Fin.castSucc_zero, Fin.succ_zero_eq_one,
            Fin.cons_zero, Fin.cons_one, hfirst] using hstep
        · simpa only [extended, ← Fin.succ_castSucc, Fin.cons_succ] using hsteps j

theorem elementary_equal_rank_subgroup_path_of_elementary
    {D : Type u} [Group D] [Finite D] {p k d : ℕ} (hprime : p.Prime)
    (hD : IsElemAbelian p (⊤ : Subgroup D)) (hk : 1 ≤ k)
    (X Y : Subgroup D) (hXcard : Nat.card X = p ^ k)
    (hYcard : Nat.card Y = p ^ k) (hJcard : Nat.card (X ⊓ Y : Subgroup D) = p ^ d) :
    ∃ n : ℕ, n ≤ k - d ∧ ∃ path : Fin (n + 1) → Subgroup D,
      path 0 = X ∧ path (Fin.last n) = Y ∧
      (∀ i, Nat.card (path i) = p ^ k) ∧
      ∀ i : Fin n, Nat.card (path i.castSucc ⊓ path i.succ : Subgroup D) =
        p ^ (k - 1) := by
  have hcommutative : IsMulCommutative D := by
    apply IsMulCommutative.of_comm
    intro x y
    exact congrArg Subtype.val (@mul_comm' (⊤ : Subgroup D) _ hD.1 ⟨x, by trivial⟩
      ⟨y, by trivial⟩)
  let : CommGroup D := { (inferInstance : Group D) with
    mul_comm := @mul_comm' D _ hcommutative }
  exact elementary_equal_rank_subgroup_path hprime (fun x => hD.2 x (by trivial))
    hk X Y hXcard hYcard hJcard

end CFSG.LargeEvenClassification.Helpers
