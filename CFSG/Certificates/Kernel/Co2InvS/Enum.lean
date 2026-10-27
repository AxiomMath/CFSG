module

public import CFSG.Certificates.Kernel.Co2InvS.Mat
public import CFSG.Certificates.Kernel.Co2InvS.BfsS

set_option exponentiation.threshold 600

public section

namespace CFSG.KC.Co2InvS

open CFSG.KC.Loop CFSG.KC.F2W CFSG.KC.Co1F2 CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co2Inv
  CFSG.KC.Bfs CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

section Rec

variable {CF G Y FW : Nat → Nat} {N : Nat}

theorem elemAt_lt (CF : Nat → Nat) (k : Nat) : elemAt CF k < 2 ^ 484 := by
  unfold elemAt elemOf
  exact Nat.and_lt_two_pow _ (by decide)

theorem fld19_lt (r o : Nat) : fld(r, o, nat_lit 524287) < 2 ^ 19 :=
  Nat.and_lt_two_pow _ (by decide)

theorem rec_spec {k : Nat} (h : recOK CF G Y FW N k = true) :
    (∀ j < 5, tOf (recAt CF k) j < N ∧ elemAt CF (tOf (recAt CF k) j) = mulV (elemAt CF k) (G j)) ∧
    k < mOf (recAt CF k) ∧
    rowK (mOf (recAt CF k)) (tOf (recAt CF k) 0) (tOf (recAt CF k) 1) (tOf (recAt CF k) 2)
      (tOf (recAt CF k) 3) (tOf (recAt CF k) 4) = nextM CF N k ∧
    sortK CF N k (sOf (recAt CF k)) = true ∧
    (involK (elemAt CF k) = true → fuseK Y (elemAt CF k) (fwAt FW k) = true) := by
  unfold recOK at h
  simp only [letB_eq, andK_eq, Bool.and_eq_true] at h
  obtain ⟨e0, e1, e2, e3, e4, hm, hr, hs, hf⟩ := h
  have edge : ∀ {g t : Nat}, edgeK CF N (elemAt CF k) g t = true → t < N ∧
      elemAt CF t = mulV (elemAt CF k) g := by
    intro g t e
    unfold edgeK at e
    rw [andK_eq, Bool.and_eq_true] at e
    exact ⟨blt_iff.1 e.1, Nat.eq_of_beq_eq_true e.2⟩
  refine ⟨fun j hj => ?_, blt_iff.1 hm, Nat.eq_of_beq_eq_true hr, hs, fun hi => ?_⟩
  · interval_cases j
    · exact edge e0
    · exact edge e1
    · exact edge e2
    · exact edge e3
    · exact edge e4
  · have hi' : involK (elemOf (recAt CF k)) = true := hi
    rwa [implK_eq, iteT hi'] at hf

end Rec

theorem sorted_inj {N : Nat} {σ f : Nat → Nat} (hs : ∀ i < N, σ i < N)
    (hlt : ∀ i, i + 1 < N → f (σ i) < f (σ (i + 1))) :
    ∀ a < N, ∀ b < N, f a = f b → a = b := by
  have mono : ∀ i j, i < j → j < N → f (σ i) < f (σ j) := by
    intro i j hij hj
    induction j with
    | zero => omega
    | succ j ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h | h
      · exact lt_trans (ih h (by omega)) (hlt j hj)
      · subst h
        exact hlt i hj
  have sinj : ∀ i < N, ∀ j < N, f (σ i) = f (σ j) → i = j := by
    intro i hi j hj e
    rcases lt_trichotomy i j with h | h | h
    · exact absurd e (ne_of_lt (mono i j h hj))
    · exact h
    · exact absurd e (ne_of_gt (mono j i h hi))
  have himg : (Finset.range N).image σ = Finset.range N := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hx
      exact Finset.mem_range.2 (hs i (Finset.mem_range.1 hi))
    · rw [Finset.card_image_of_injOn]
      intro i hi j hj e
      exact sinj i (Finset.mem_range.1 hi) j (Finset.mem_range.1 hj) (by rw [e])
  have surj : ∀ a < N, ∃ i < N, σ i = a := by
    intro a ha
    have : a ∈ (Finset.range N).image σ := by rw [himg]; exact Finset.mem_range.2 ha
    obtain ⟨i, hi, e⟩ := Finset.mem_image.1 this
    exact ⟨i, Finset.mem_range.1 hi, e⟩
  intro a ha b hb e
  obtain ⟨i, hi, rfl⟩ := surj a ha
  obtain ⟨j, hj, rfl⟩ := surj b hb
  rw [sinj i hi j hj e]

theorem stK_cases (t m : Nat) : stK t m = if t < m then m else if t = m then m + 1 else BAD := by
  unfold stK
  rw [selN_eq, selN_eq]
  by_cases h1 : t < m
  · rw [blt_iff.2 h1, iteT rfl, iteT h1]
  · rw [blt_false h1, iteF Bool.false_ne_true, iteF h1]
    by_cases h2 : t = m
    · rw [h2, Nat.beq_refl, iteT rfl, iteT rfl]
    · rw [beq_false h2, iteF Bool.false_ne_true, iteF h2]

theorem BAD_eq : BAD = 2 ^ 19 := rfl

theorem stK_step {E : Nat → Nat → Nat} {i j m : Nat} (ht : E i j < BAD) (hm : m ≤ BAD) :
    stK (E i j) m ≤ BAD ∧ (stK (E i j) m < BAD → rStep E i (some m) j = some (stK (E i j) m)) ∧
      (m = BAD → stK (E i j) m = BAD) := by
  rw [stK_cases]
  refine ⟨?_, fun h => ?_, fun h => ?_⟩
  · split_ifs <;> omega
  · simp only [rStep]
    split_ifs at h ⊢ <;> first | rfl | omega
  · subst h
    rw [iteT ht]

theorem rowK_rRow {E : Nat → Nat → Nat} {i m m' : Nat} (hE : ∀ j < 5, E i j < BAD) (hm : m < BAD)
    (h : rowK m (E i 0) (E i 1) (E i 2) (E i 3) (E i 4) = m') (hm' : m' < BAD) :
    rRow E 5 i m = some m' := by
  unfold rowK at h
  obtain ⟨a0, b0, c0⟩ := stK_step (E := E) (i := i) (j := 0) (hE 0 (by omega)) (le_of_lt hm)
  obtain ⟨a1, b1, c1⟩ := stK_step (E := E) (i := i) (j := 1) (hE 1 (by omega)) a0
  obtain ⟨a2, b2, c2⟩ := stK_step (E := E) (i := i) (j := 2) (hE 2 (by omega)) a1
  obtain ⟨a3, b3, c3⟩ := stK_step (E := E) (i := i) (j := 3) (hE 3 (by omega)) a2
  obtain ⟨a4, b4, c4⟩ := stK_step (E := E) (i := i) (j := 4) (hE 4 (by omega)) a3
  rw [h] at a4 b4 c4
  have l3 : stK (E i 3) (stK (E i 2) (stK (E i 1) (stK (E i 0) m))) < BAD := by
    rcases Nat.lt_or_eq_of_le a3 with h3 | h3
    · exact h3
    · have := c4 h3
      omega
  have l2 : stK (E i 2) (stK (E i 1) (stK (E i 0) m)) < BAD := by
    rcases Nat.lt_or_eq_of_le a2 with h2 | h2
    · exact h2
    · have := c3 h2
      omega
  have l1 : stK (E i 1) (stK (E i 0) m) < BAD := by
    rcases Nat.lt_or_eq_of_le a1 with h1 | h1
    · exact h1
    · have := c2 h1
      omega
  have l0 : stK (E i 0) m < BAD := by
    rcases Nat.lt_or_eq_of_le a0 with h0 | h0
    · exact h0
    · have := c1 h0
      omega
  unfold rRow
  simp only [List.range_succ, List.range_zero, List.nil_append, List.foldl_append, List.foldl_cons,
    List.foldl_nil]
  rw [b0 l0, b1 l1, b2 l2, b3 l3, b4 hm']

section Enum

variable {CF G Y FW : Nat → Nat} {N : Nat}

structure Recs (CF G Y FW : Nat → Nat) (N : Nat) : Prop where
  ok : ∀ k < N, recOK CF G Y FW N k = true
  zero : elemAt CF 0 = IDP
  one : mOf (recAt CF 0) = 1
  pos : 0 < N
  small : N < BAD
  gsize : co2InvGens.size = 5
  gens : ∀ j < 5, co2InvGens[j]! = unpackR 22 (G j)

@[expose] noncomputable def Lf (CF : Nat → Nat) (k : Nat) : Array Nat := unpackR 22 (elemAt CF k)

@[expose] noncomputable def Mf (CF : Nat → Nat) (N k : Nat) : Nat :=
  if k < N then mOf (recAt CF k) else N

theorem Lf_inj (hR : Recs CF G Y FW N) : ∀ a < N, ∀ b < N, Lf CF a = Lf CF b → a = b := by
  have hs : ∀ i < N, sOf (recAt CF i) < N := by
    intro i hi
    have h := (rec_spec (hR.ok i hi)).2.2.2.1
    unfold sortK at h
    rw [andK_eq, Bool.and_eq_true] at h
    exact blt_iff.1 h.1
  have hlt : ∀ i, i + 1 < N →
      elemAt CF (sOf (recAt CF i)) < elemAt CF (sOf (recAt CF (i + 1))) := by
    intro i hi
    have h := (rec_spec (hR.ok i (by omega))).2.2.2.1
    unfold sortK at h
    rw [andK_eq, Bool.and_eq_true, implK_eq, blt_iff.2 hi, iteT rfl] at h
    exact blt_iff.1 h.2
  have hinj := sorted_inj (f := elemAt CF) hs hlt
  intro a ha b hb e
  exact hinj a ha b hb (unpack_inj (elemAt_lt CF a) (elemAt_lt CF b) e)

theorem Lf_tbl (hR : Recs CF G Y FW N) : ∀ i < N, ∀ j < co2InvGens.size,
    tOf (recAt CF i) j < N ∧
      Lf CF (tOf (recAt CF i) j) = mulRows 22 (Lf CF i) co2InvGens[j]! := by
  intro i hi j hj
  rw [hR.gsize] at hj
  obtain ⟨h1, h2⟩ := (rec_spec (hR.ok i hi)).1 j hj
  refine ⟨h1, ?_⟩
  rw [Lf, Lf, h2, hR.gens j hj, mulRows_unpack]

theorem Mf_row (hR : Recs CF G Y FW N) : ∀ k < N, k < Mf CF N k ∧
    rRow (fun i j => tOf (recAt CF i) j) co2InvGens.size k (Mf CF N k) =
      some (Mf CF N (k + 1)) := by
  intro k hk
  obtain ⟨-, hm, hr, -, -⟩ := rec_spec (hR.ok k hk)
  have e1 : Mf CF N k = mOf (recAt CF k) := iteT hk
  have e2 : Mf CF N (k + 1) = nextM CF N k := by
    unfold Mf nextM
    rw [selN_eq]
    by_cases h : k + 1 < N
    · rw [iteT h, blt_iff.2 h, iteT rfl]
    · rw [iteF h, blt_false h, iteF Bool.false_ne_true]
  refine ⟨by rw [e1]; exact hm, ?_⟩
  rw [hR.gsize, e1, e2]
  refine rowK_rRow (fun j _ => fld19_lt _ _) (fld19_lt _ _) hr ?_
  unfold nextM
  rw [selN_eq]
  split
  · exact fld19_lt _ _
  · exact hR.small

theorem enum_facts (hR : Recs CF G Y FW N) :
    (bfsS co2InvGens N).elems.size = N ∧ (∀ k < N, (bfsS co2InvGens N).elems[k]! = Lf CF k) ∧
      (∀ k, 0 < k → k < N → (bfsS co2InvGens N).par[k]! < k ∧
        (bfsS co2InvGens N).lab[k]! < co2InvGens.size ∧
        (bfsS co2InvGens N).elems[k]! = mulRows 22 (bfsS co2InvGens N).elems[(bfsS co2InvGens N).par[k]!]!
          co2InvGens[(bfsS co2InvGens N).lab[k]!]!) ∧
      (∀ k < N, ∀ j < co2InvGens.size,
        ((bfsS co2InvGens N).tbl[k]!)[j]! = tOf (recAt CF k) j) ∧
      (∀ x i, (bfsS co2InvGens N).pos[x]? = some i ↔ i < N ∧ Lf CF i = x) := by
  refine bfsS_replay (Lf_inj hR) (Lf_tbl hR) ?_ (M := Mf CF N) ?_ ?_ (Mf_row hR)
  · rw [Lf, hR.zero, ← idRows_eq]
  · unfold Mf
    rw [iteT hR.pos, hR.one]
  · unfold Mf
    rw [iteF (Nat.lt_irrefl N)]

end Enum

end CFSG.KC.Co2InvS

end
