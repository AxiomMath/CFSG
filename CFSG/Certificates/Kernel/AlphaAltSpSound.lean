module

public import Certificates.Data.Kernel.AlphaAltSp
import Mathlib.Algebra.BigOperators.Fin

public section

namespace CFSG.AGLEmbedding.R3

private theorem fsum_eq_sum (N : Nat) (f : Fin N → Int) : fsum N f = ∑ i, f i :=
  (Fin.sum_univ_def f).symm

private theorem fsum_zero (N : Nat) : fsum N (fun _ => (0 : Int)) = 0 := by
  rw [fsum_eq_sum, Finset.sum_const_zero]

private theorem fsum_indicator {J n : Nat} {S : List (Nat × Nat × Nat)} (hS : S.Nodup)
    (hr : ∀ q ∈ S, q.1 < J ∧ q.2.1 < n ∧ q.2.2 < n) (F : Nat → Nat → Nat → Int) :
    fsum J (fun j => fsum n fun r => fsum n fun s =>
      (if ((j : Nat), (r : Nat), (s : Nat)) ∈ S then (1 : Int) else 0) * F j r s) =
      (S.map fun q => F q.1 q.2.1 q.2.2).sum := by
  let ι : Fin J × Fin n × Fin n ↪ Nat × Nat × Nat :=
    ⟨fun t => ((t.1 : Nat), (t.2.1 : Nat), (t.2.2 : Nat)), fun t t' h => by
      simp only [Prod.mk.injEq] at h
      exact Prod.ext (Fin.ext h.1) (Prod.ext (Fin.ext h.2.1) (Fin.ext h.2.2))⟩
  have hL : fsum J (fun j => fsum n fun r => fsum n fun s =>
      (if ((j : Nat), (r : Nat), (s : Nat)) ∈ S then (1 : Int) else 0) * F j r s) =
      ∑ t : Fin J × Fin n × Fin n, if ι t ∈ S then F (ι t).1 (ι t).2.1 (ι t).2.2 else 0 := by
    simp only [fsum_eq_sum, Fintype.sum_prod_type, ite_mul, one_mul, zero_mul]
    rfl
  have hmap : (Finset.univ.filter fun t => ι t ∈ S).map ι = S.toFinset := by
    ext x
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, List.mem_toFinset]
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ht
    · intro hx
      obtain ⟨h1, h2, h3⟩ := hr x hx
      exact ⟨(⟨x.1, h1⟩, ⟨x.2.1, h2⟩, ⟨x.2.2, h3⟩), hx, rfl⟩
  rw [hL, ← Finset.sum_filter, ← List.sum_toFinset _ hS, ← hmap, Finset.sum_map]

theorem altOK_of_altSp {p n : Nat} {m : NMod} {T : List (List (Nat × Nat × Nat))}
    {ci : Nat → Nat → Nat → Nat → Nat → Int} {ct : Nat → Nat → Nat → Nat → Int}
    {tgt : Nat → Nat → Nat → Nat → Int}
    (hci : ∀ a₀ b₀ j r s, ci a₀ b₀ j r s = if (j, r, s) ∈ T.getD (n * a₀ + b₀) [] then 1 else 0)
    (hct : ∀ a₀ b₀ r s, ct a₀ b₀ r s = 0) (h : altSp p m n T tgt = true) :
    m.altOK p ci ct tgt = true := by
  simp only [altSp, spRowOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, beq_iff_eq] at h
  obtain ⟨hlen, hrow⟩ := h
  subst hlen
  have hget : ∀ j : Fin m.acts.length, m.acts.get j = m.acts.getD j default := fun j => by
    rw [List.get_eq_getElem, List.getElem_eq_getD default]
  simp only [NMod.altOK, List.all_eq_true, List.mem_finRange, true_implies, forall_const,
    beq_iff_eq]
  intro a₀ b₀ a b
  obtain ⟨⟨hnd, hall⟩, hcoef⟩ := hrow a₀ a₀.isLt b₀ b₀.isLt
  simp only [hci, hct, zero_mul, fsum_zero, add_zero, hget]
  have key := fsum_indicator (J := m.acts.length) (n := m.basis.length) hnd
    (fun q hq => ⟨(hall q hq).1.1, (hall q hq).1.2, (hall q hq).2⟩)
    (fun j r s => (m.acts.getD j default).ent m.basis.length a r *
      (m.acts.getD j default).ent m.basis.length b s - kd a r * kd b s)
  beta_reduce at key
  rw [key]
  exact hcoef a a.isLt b b.isLt

end CFSG.AGLEmbedding.R3

end
