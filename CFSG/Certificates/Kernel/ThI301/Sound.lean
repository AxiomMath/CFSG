module

public import Certificates.Data.Kernel.ThI301.Defs
public import CFSG.Certificates.Kernel.Enum.ZCGlue
public import Mathlib.GroupTheory.Perm.Fin
public import CFSG.Certificates.Kernel.Enum.ZCSound

public section

namespace CFSG.KC.ThI301Sound

open CFSG.KC.Enum CFSG.KC.ThI301 CFSG.KC.EnumSound CFSG.KS CFSG.KS.Raw.Orb Equiv
  CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal

theorem pg15 {P : Nat} {g : Perm (Fin 9)} (h : PRep 9 4 P g) (a : Fin 9) :
    pg (nat_lit 4) (nat_lit 15) P a = (g a : Nat) :=
  h a

theorem ncAt_prep {x y yi p : Nat} {X G : Perm (Fin 9)} (h : ncAt x y yi p = true) (hp : p < 9)
    (hX : PRep 9 4 x X) (hy : PRep 9 4 y G) (hyi : PRep 9 4 yi G⁻¹) :
    X * (G * X * G⁻¹) ≠ G * X * G⁻¹ * X := by
  unfold ncAt at h
  have hne := Nat.ne_of_beq_eq_false (bIf_ft h)
  intro hc
  apply hne
  have e := congrArg (fun g : Perm (Fin 9) => ((g ⟨p, hp⟩ : Fin 9) : Nat)) hc
  simp only [Perm.mul_apply] at e
  have e1 := pg15 hyi ⟨p, hp⟩
  have e2 := pg15 hX ⟨p, hp⟩
  simp only [Fin.val_mk] at e1 e2
  rw [e1, e2]
  simp only [pg15 hX, pg15 hy, pg15 hyi]
  exact e

theorem thRec_sound {T : Nat → Nat} {rm i : Nat} {Y YI : Nat → Nat}
    (h : thRec T rm Y YI i = true) :
    ∃ k < 3, ∃ p < 9, ncAt (Nat.land (rget T 0 0 0 rm i) 68719476735) (Y k) (YI k) p = true := by
  unfold thRec at h
  simp only [PK.bAnd_eq, Bool.and_eq_true, PK.strictB_eq, Nat.blt_eq] at h
  exact ⟨_, h.1, _, h.2.1, h.2.2⟩

theorem thRec_prep {T : Nat → Nat} {rm i : Nat} {Y YI : Nat → Nat} {X : Perm (Fin 9)}
    {gY : Nat → Perm (Fin 9)} (h : thRec T rm Y YI i = true)
    (hX : PRep 9 4 (Nat.land (rget T 0 0 0 rm i) 68719476735) X)
    (hY : ∀ k < 3, PRep 9 4 (Y k) (gY k) ∧ PRep 9 4 (YI k) (gY k)⁻¹) :
    ∃ k < 3, X * (gY k * X * (gY k)⁻¹) ≠ gY k * X * (gY k)⁻¹ * X := by
  obtain ⟨k, hk, p, hp, hc⟩ := thRec_sound h
  exact ⟨k, hk, ncAt_prep hc hp hX (hY k hk).1 (hY k hk).2⟩

theorem thRange_iff {T : Nat → Nat} {rm lo cnt : Nat} {Y YI : Nat → Nat} :
    thRange T rm Y YI lo cnt = true ↔ ∀ k < cnt, thRec T rm Y YI (lo + k) = true := by
  unfold thRange
  exact PK.allN_iff

@[expose] def rep1 : Perm (Fin 9) := swap 0 1

@[expose] def rep2 : Perm (Fin 9) := swap 0 1 * swap 2 3

@[expose] def rep3 : Perm (Fin 9) := swap 0 1 * swap 2 3 * swap 4 5

@[expose] def rep4 : Perm (Fin 9) := swap 0 1 * swap 2 3 * swap 4 5 * swap 6 7

theorem cycleType_swap {x y : Fin 9} (h : x ≠ y) : (swap x y).cycleType = {2} := by
  rw [(Perm.isCycle_swap h).cycleType, Perm.card_support_swap h]

theorem cycleType_mul_swap {f : Perm (Fin 9)} {x y : Fin 9} (h : x ≠ y)
    (hd : ∀ z, f z = z ∨ swap x y z = z) :
    (f * swap x y).cycleType = 2 ::ₘ f.cycleType := by
  rw [Perm.Disjoint.cycleType_mul hd, cycleType_swap h, Multiset.add_comm, Multiset.singleton_add]

theorem cycleType_rep1 : rep1.cycleType = Multiset.replicate 1 2 := cycleType_swap (by decide)

theorem cycleType_rep2 : rep2.cycleType = Multiset.replicate 2 2 := by
  rw [rep2, cycleType_mul_swap (by decide) (by decide), ← rep1, cycleType_rep1]
  rfl

theorem cycleType_rep3 : rep3.cycleType = Multiset.replicate 3 2 := by
  rw [rep3, cycleType_mul_swap (by decide) (by decide), ← rep2, cycleType_rep2]
  rfl

theorem cycleType_rep4 : rep4.cycleType = Multiset.replicate 4 2 := by
  rw [rep4, cycleType_mul_swap (by decide) (by decide), ← rep3, cycleType_rep3]
  rfl

theorem invol_isConj_rep {X : Perm (Fin 9)} (h2 : X * X = 1) (h1 : X ≠ 1) :
    IsConj X rep1 ∨ IsConj X rep2 ∨ IsConj X rep3 ∨ IsConj X rep4 := by
  have ho : orderOf X = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [pow_two]; exact h2) h1
  obtain ⟨n, hn⟩ := Perm.cycleType_prime_order (by rw [ho]; exact Nat.prime_two)
  rw [ho] at hn
  have hs := Perm.sum_cycleType_le X
  rw [hn, Multiset.sum_replicate, smul_eq_mul, Fintype.card_fin] at hs
  simp only [Perm.isConj_iff_cycleType_eq, hn, cycleType_rep1, cycleType_rep2, cycleType_rep3,
    cycleType_rep4]
  have hn3 : n ≤ 3 := by omega
  interval_cases n <;> simp

theorem closure_swap_finRotate :
    Subgroup.closure ({swap 0 1, finRotate 9} : Set (Perm (Fin 9))) = ⊤ := by
  have h := Perm.closure_cycle_adjacent_swap (isCycle_finRotate (n := 7)) support_finRotate 0
  have e : (finRotate (7 + 2)) 0 = 1 := by decide
  rw [e, Set.pair_comm] at h
  exact h

theorem mem_of_conj_closed {A : Type} [Group A] {a b : A} {nL : Nat} {U : Nat → A}
    (hUa : ∀ i < nL, ∃ j < nL, U j = a * U i * a⁻¹)
    (hUb : ∀ i < nL, ∃ j < nL, U j = b * U i * b⁻¹) {g : A}
    (hg : g ∈ Subgroup.closure ({a, b} : Set A)) {i : Nat} (hi : i < nL) :
    ∃ j < nL, U j = g * U i * g⁻¹ := by
  set O : Set A := Set.range (fun i : Fin nL => U i)
  have hOfin : O.Finite := Set.finite_range _
  have hOa : ∀ x ∈ O, a * x * a⁻¹ ∈ O := by
    rintro _ ⟨i, rfl⟩
    obtain ⟨j, hj, e⟩ := hUa i i.2
    exact ⟨⟨j, hj⟩, e⟩
  have hOb : ∀ x ∈ O, b * x * b⁻¹ ∈ O := by
    rintro _ ⟨i, rfl⟩
    obtain ⟨j, hj, e⟩ := hUb i i.2
    exact ⟨⟨j, hj⟩, e⟩
  have hO' : ∀ x ∈ List.ofFn (fun i : Fin nL => U i), ∀ g ∈ [a, b, a⁻¹, b⁻¹],
      g * x * g⁻¹ ∈ List.ofFn (fun i : Fin nL => U i) := by
    intro x hx g hg
    rw [List.mem_ofFn] at hx ⊢
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with h | h | h | h <;> rw [h]
    · exact hOa x hx
    · exact hOb x hx
    · exact conj_inv_mem_of_finite hOfin hOa x hx
    · exact conj_inv_mem_of_finite hOfin hOb x hx
  have h := zc_conj_mem_of_closure hO' g hg (U i) (List.mem_ofFn.2 ⟨⟨i, hi⟩, rfl⟩)
  obtain ⟨⟨j, hj⟩, e⟩ := List.mem_ofFn.1 h
  exact ⟨j, hj, e⟩

end CFSG.KC.ThI301Sound

end
