module

public import Certificates.Data.Kernel.U33Pair
public import CFSG.RankThree.PartTwo.Sec8.Hering88FG2Inputs

public section

namespace CFSG.KC.U33Pair

open CFSG.RankThree.PartTwo.Sec8.Hering88F

theorem u33PtK_eq : ∀ (k : Fin 5) (x : Fin 28), u33PtK k.val x = u33Pt k x := by
  decide +kernel

theorem pairOrbit_succ (K : ℕ) : pairOrbit (K + 1) = pairStep (pairOrbit K) :=
  Function.iterate_succ_apply' _ _ _

theorem u33StepK_mem {K : ℕ} {pq : Fin 28 × Fin 28} (h : pq ∈ pairOrbit K) {d : ℕ} (hd : d < 6) :
    u33StepK d pq ∈ pairOrbit (K + 1) := by
  rw [pairOrbit_succ, pairStep, Finset.mem_union]
  unfold u33StepK
  split
  · exact Or.inl h
  · right
    rw [Finset.mem_biUnion]
    refine ⟨⟨d - 1, by omega⟩, Finset.mem_univ _, Finset.mem_image.mpr ⟨pq, h, ?_⟩⟩
    rw [← u33PtK_eq, ← u33PtK_eq]

theorem u33EvalK_mem (n : ℕ) :
    ∀ (c : ℕ) {K : ℕ} {pq : Fin 28 × Fin 28}, pq ∈ pairOrbit K → u33EvalK n c pq ∈ pairOrbit (K + n) := by
  induction n with
  | zero => exact fun _ _ _ h => h
  | succ n ih =>
    intro c K pq h
    have h' := ih (c / 6) (u33StepK_mem h (Nat.mod_lt c (by decide)))
    rw [Nat.add_assoc, Nat.add_comm 1 n] at h'
    exact h'

theorem u33PairsK_sound :
    ∀ (L : List ℕ) (i : ℕ), u33PairsK L i = true → ∀ j < L.length, u33OkK (i + j) (L.getD j 0) = true
  | [], _, _, _, hj => absurd hj (Nat.not_lt_zero _)
  | c :: L, i, h, j, hj => by
    change (u33OkK i c && u33PairsK L (i + 1)) = true at h
    rw [Bool.and_eq_true] at h
    cases j with
    | zero => simpa using h.1
    | succ j =>
      have h2 := u33PairsK_sound L (i + 1) h.2 j (by simpa using hj)
      rw [Nat.add_assoc, Nat.add_comm 1 j] at h2
      simpa using h2

theorem u33TwoTransOK_of_pairsK (L : List ℕ) (hl : L.length = 784) (h : u33PairsK L 0 = true) :
    u33TwoTransOK () = true := by
  unfold u33TwoTransOK
  rw [List.all_eq_true]
  intro p _
  rw [List.all_eq_true]
  intro q _
  apply decide_eq_true
  intro hpq
  have hp := p.isLt
  have hq := q.isLt
  have hok := u33PairsK_sound L 0 h (28 * p.val + q.val) (by omega)
  rw [Nat.zero_add] at hok
  have hdiv : (28 * p.val + q.val) / 28 = p.val := by omega
  have hmod : (28 * p.val + q.val) % 28 = q.val := by omega
  unfold u33OkK at hok
  rw [hdiv, hmod, Fin.ofNat_val_eq_self, Fin.ofNat_val_eq_self] at hok
  have hne : Nat.beq p.val q.val = false := by
    rw [Bool.eq_false_iff]
    exact fun hb => hpq (Fin.ext (Nat.eq_of_beq_eq_true hb))
  rw [hne, Bool.false_or] at hok
  have heq := of_decide_eq_true hok
  have hm := u33EvalK_mem 9 (L.getD (28 * p.val + q.val) 0) (K := 0) (pq := (0, 1))
    (by simp [pairOrbit])
  rw [heq, Nat.zero_add] at hm
  exact hm

end CFSG.KC.U33Pair
