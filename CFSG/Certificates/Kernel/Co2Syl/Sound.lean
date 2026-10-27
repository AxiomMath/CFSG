module

public import Certificates.Data.Kernel.Co2Syl
public import CFSG.Certificates.Kernel.Co2InvS.Enum
public import CFSG.Certificates.Kernel.TabMatGrpSound

set_option exponentiation.threshold 600

public section

namespace CFSG.KC.Co2Syl

open CFSG.KC.Loop CFSG.KC.F2W CFSG.KC.Co2InvS CFSG.KC.TabMatGrp CFSG.KLie.CT CFSG.KC.M1F2
  CFSG.KC.Co1F2 CFSG.Sporadic.SmallF2.Native
open CFSG.Sporadic.SmallF2 (rowsMatrix rowsMatrix_apply rowsMatrix_idRows toVecD_apply)

@[expose] noncomputable def genMon (G : Nat → Nat) : Submonoid (Matrix (Fin 22) (Fin 22) (ZMod 2)) :=
  Submonoid.closure (Set.range fun j : Fin 5 => MatP 22 (G j))

theorem gen_mem (G : Nat → Nat) {j : Nat} (hj : j < 5) : MatP 22 (G j) ∈ genMon G :=
  Submonoid.subset_closure ⟨⟨j, hj⟩, rfl⟩

theorem MatP_mulV (A B : Nat) : MatP 22 (mulV A B) = MatP 22 A * MatP 22 B := by
  rw [mulV_eq_mulW, mulW_eq, MatP_mul]

theorem MatP_IDP : MatP 22 IDP = 1 := by
  unfold MatP
  rw [← idRows_eq, rowsMatrix_idRows]

theorem MatP_inj' {A B : Nat} (hA : A < 2 ^ 484) (hB : B < 2 ^ 484) (h : MatP 22 A = MatP 22 B) :
    A = B :=
  MatP_inj h hA hB

theorem beq_MatP {A B : Nat} (hA : A < 2 ^ 484) (hB : B < 2 ^ 484) :
    Nat.beq A B = true ↔ MatP 22 A = MatP 22 B :=
  ⟨fun h => by rw [Nat.eq_of_beq_eq_true h], fun h => by rw [MatP_inj' hA hB h, Nat.beq_refl]⟩

theorem involK_iff {X : Nat} (hX : X < 2 ^ 484) :
    involK X = true ↔ MatP 22 X * MatP 22 X = 1 ∧ MatP 22 X ≠ 1 := by
  have e1 := beq_MatP (mulV_lt X X) IDP_lt
  have e2 := beq_MatP hX IDP_lt
  rw [MatP_mulV, MatP_IDP] at e1
  rw [MatP_IDP] at e2
  rw [involK_eq, Bool.and_eq_true, ne_eq, ← e1, ← e2]
  cases Nat.beq X IDP <;> simp

theorem MatP_apply (U : Nat) (i j : Fin 22) :
    MatP 22 U i j = if U.testBit (i.val * 22 + j.val) then 1 else 0 := by
  have hr : (unpackR 22 U)[i.val]?.getD 0 = rowF 22 U i.val := by
    simp [unpackR, i.isLt, rowF_eq]
  unfold MatP
  rw [rowsMatrix_apply, hr, toVecD_apply, testBit_rowF 22 _ _ _ j.isLt]

section Tree

variable {CF G : Nat → Nat} {N : Nat}

theorem edgeT_spec {m X g t : Nat} (h : edgeT CF N m X g t = true) (hm : m ≤ t) :
    t < N ∧ elemAt CF t = mulV X g := by
  unfold edgeT at h
  rw [implK_eq, notK_eq, blt_false (Nat.not_lt.2 hm), Bool.not_false, if_pos rfl] at h
  unfold edgeK at h
  rw [andK_eq, Bool.and_eq_true] at h
  exact ⟨blt_iff.1 h.1, Nat.eq_of_beq_eq_true h.2⟩

theorem recT_spec {k : Nat} (h : recT CF G N k = true) :
    (∀ j < 5, mOf (recAt CF k) ≤ tOf (recAt CF k) j →
      tOf (recAt CF k) j < N ∧ elemAt CF (tOf (recAt CF k) j) = mulV (elemAt CF k) (G j)) ∧
    k < mOf (recAt CF k) ∧
    rowK (mOf (recAt CF k)) (tOf (recAt CF k) 0) (tOf (recAt CF k) 1) (tOf (recAt CF k) 2)
      (tOf (recAt CF k) 3) (tOf (recAt CF k) 4) = nextM CF N k ∧
    sortK CF N k (sOf (recAt CF k)) = true := by
  unfold recT at h
  simp only [letB_eq, andK_eq, Bool.and_eq_true] at h
  obtain ⟨e0, e1, e2, e3, e4, hm, hr, hs⟩ := h
  refine ⟨fun j hj hle => ?_, blt_iff.1 hm, Nat.eq_of_beq_eq_true hr, hs⟩
  interval_cases j
  · exact edgeT_spec e0 hle
  · exact edgeT_spec e1 hle
  · exact edgeT_spec e2 hle
  · exact edgeT_spec e3 hle
  · exact edgeT_spec e4 hle

theorem stK_cover {t m : Nat} (h : stK t m < BAD) :
    m ≤ stK t m ∧ ∀ s, m ≤ s → s < stK t m → s = t := by
  rw [stK_cases] at h ⊢
  by_cases h1 : t < m
  · rw [if_pos h1]
    exact ⟨le_refl _, fun s h2 h3 => absurd h3 (by omega)⟩
  · by_cases h2 : t = m
    · rw [if_neg h1, if_pos h2]
      exact ⟨by omega, fun s h3 h4 => by omega⟩
    · rw [if_neg h1, if_neg h2] at h
      exact absurd h (lt_irrefl _)

theorem rowK_cover {m t0 t1 t2 t3 t4 : Nat} (hb : rowK m t0 t1 t2 t3 t4 < BAD) :
    m ≤ rowK m t0 t1 t2 t3 t4 ∧ ∀ s, m ≤ s → s < rowK m t0 t1 t2 t3 t4 →
      s = t0 ∨ s = t1 ∨ s = t2 ∨ s = t3 ∨ s = t4 := by
  unfold rowK at hb ⊢
  obtain ⟨a4, b4⟩ := stK_cover hb
  have h3 := lt_of_le_of_lt a4 hb
  obtain ⟨a3, b3⟩ := stK_cover h3
  have h2 := lt_of_le_of_lt a3 h3
  obtain ⟨a2, b2⟩ := stK_cover h2
  have h1 := lt_of_le_of_lt a2 h2
  obtain ⟨a1, b1⟩ := stK_cover h1
  have h0 := lt_of_le_of_lt a1 h1
  obtain ⟨a0, b0⟩ := stK_cover h0
  refine ⟨le_trans a0 (le_trans a1 (le_trans a2 (le_trans a3 a4))), fun s hs1 hs2 => ?_⟩
  by_cases c0 : s < stK t0 m
  · exact Or.inl (b0 s hs1 c0)
  by_cases c1 : s < stK t1 (stK t0 m)
  · exact Or.inr (Or.inl (b1 s (Nat.not_lt.1 c0) c1))
  by_cases c2 : s < stK t2 (stK t1 (stK t0 m))
  · exact Or.inr (Or.inr (Or.inl (b2 s (Nat.not_lt.1 c1) c2)))
  by_cases c3 : s < stK t3 (stK t2 (stK t1 (stK t0 m)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (b3 s (Nat.not_lt.1 c2) c3))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (b4 s (Nat.not_lt.1 c3) hs2))))

structure TreeRecs (CF G : Nat → Nat) (N : Nat) : Prop where
  ok : ∀ k < N, recT CF G N k = true
  zero : elemAt CF 0 = IDP
  one : mOf (recAt CF 0) = 1
  small : N < BAD

theorem Mf_succ (k : Nat) : Mf CF N (k + 1) = nextM CF N k := by
  unfold Mf nextM
  rw [selN_eq]
  by_cases h : k + 1 < N
  · rw [iteT h, blt_iff.2 h, iteT rfl]
  · rw [iteF h, blt_false h, iteF Bool.false_ne_true]

theorem nextM_lt (hs : N < BAD) (k : Nat) : nextM CF N k < BAD := by
  unfold nextM
  rw [selN_eq]
  split
  · exact fld19_lt _ _
  · exact hs

theorem tree_mem (hR : TreeRecs CF G N) : ∀ t < N, MatP 22 (elemAt CF t) ∈ genMon G := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
  intro ht
  rcases Nat.eq_zero_or_pos t with h0 | h0
  · subst h0
    rw [hR.zero, MatP_IDP]
    exact (genMon G).one_mem
  have hP0 : Mf CF N 0 ≤ t := by
    unfold Mf
    rw [iteT (by omega : 0 < N), hR.one]
    omega
  have hkP : Mf CF N (Nat.findGreatest (fun k => Mf CF N k ≤ t) N) ≤ t :=
    Nat.findGreatest_spec (P := fun k => Mf CF N k ≤ t) (Nat.zero_le N) hP0
  have hkN := Nat.findGreatest_le (P := fun k => Mf CF N k ≤ t) N
  generalize hk : Nat.findGreatest (fun k => Mf CF N k ≤ t) N = k at hkP hkN
  have hkN' : k < N := by
    rcases Nat.lt_or_ge k N with h | h
    · exact h
    · have e : k = N := le_antisymm hkN h
      rw [e] at hkP
      unfold Mf at hkP
      rw [iteF (Nat.lt_irrefl N)] at hkP
      omega
  have hk1 : t < Mf CF N (k + 1) := by
    have := Nat.findGreatest_is_greatest (P := fun k => Mf CF N k ≤ t) (k := k + 1)
      (by rw [hk]; exact Nat.lt_succ_self k) (Nat.succ_le_of_lt hkN')
    exact Nat.lt_of_not_le this
  obtain ⟨hedge, hkm, hrow, -⟩ := recT_spec (hR.ok k hkN')
  have e1 : Mf CF N k = mOf (recAt CF k) := iteT hkN'
  rw [← Mf_succ] at hrow
  have hb : rowK (mOf (recAt CF k)) (tOf (recAt CF k) 0) (tOf (recAt CF k) 1) (tOf (recAt CF k) 2)
      (tOf (recAt CF k) 3) (tOf (recAt CF k) 4) < BAD := by
    rw [hrow, Mf_succ]
    exact nextM_lt hR.small k
  obtain ⟨-, hcov⟩ := rowK_cover hb
  rw [hrow] at hcov
  have hmt : mOf (recAt CF k) ≤ t := by
    rw [← e1]
    exact hkP
  obtain ⟨j, hj, hjt⟩ : ∃ j < 5, tOf (recAt CF k) j = t := by
    rcases hcov t hmt hk1 with e | e | e | e | e
    · exact ⟨0, by omega, e.symm⟩
    · exact ⟨1, by omega, e.symm⟩
    · exact ⟨2, by omega, e.symm⟩
    · exact ⟨3, by omega, e.symm⟩
    · exact ⟨4, by omega, e.symm⟩
  obtain ⟨-, he⟩ := hedge j hj (by rw [hjt]; exact hmt)
  rw [hjt] at he
  rw [he, MatP_mulV]
  exact (genMon G).mul_mem (ih k (by omega) hkN') (gen_mem G hj)

theorem tree_inj (hR : TreeRecs CF G N) :
    ∀ a < N, ∀ b < N, MatP 22 (elemAt CF a) = MatP 22 (elemAt CF b) → a = b := by
  have hs : ∀ i < N, sOf (recAt CF i) < N := by
    intro i hi
    have h := (recT_spec (hR.ok i hi)).2.2.2
    unfold sortK at h
    rw [andK_eq, Bool.and_eq_true] at h
    exact blt_iff.1 h.1
  have hlt : ∀ i, i + 1 < N →
      elemAt CF (sOf (recAt CF i)) < elemAt CF (sOf (recAt CF (i + 1))) := by
    intro i hi
    have h := (recT_spec (hR.ok i (by omega))).2.2.2
    unfold sortK at h
    rw [andK_eq, Bool.and_eq_true, implK_eq, blt_iff.2 hi, iteT rfl] at h
    exact blt_iff.1 h.2
  intro a ha b hb e
  exact sorted_inj (σ := fun i => sOf (recAt CF i)) (f := elemAt CF) hs hlt a ha b hb
    (MatP_inj' (elemAt_lt CF a) (elemAt_lt CF b) e)

noncomputable def entF (hR : TreeRecs CF G N) (k : Fin N) : genMon G :=
  ⟨MatP 22 (elemAt CF k), tree_mem hR k k.2⟩

theorem entF_inj (hR : TreeRecs CF G N) : Function.Injective (entF hR) :=
  fun a b e => Fin.ext (tree_inj hR a a.2 b b.2 (congrArg Subtype.val e))

theorem tree_card (hR : TreeRecs CF G N) : N ≤ Nat.card (genMon G) := by
  simpa using Nat.card_le_card_of_injective _ (entF_inj hR)

theorem entF_bij (hR : TreeRecs CF G N) (hc : Nat.card (genMon G) ≤ N) :
    Function.Bijective (entF hR) :=
  (entF_inj hR).bijective_of_nat_card_le (by simpa using hc)

theorem tree_surj (hR : TreeRecs CF G N) (hc : Nat.card (genMon G) ≤ N) :
    ∀ x ∈ genMon G, ∃ k < N, MatP 22 (elemAt CF k) = x := by
  intro x hx
  obtain ⟨k, hk⟩ := (entF_bij hR hc).2 ⟨x, hx⟩
  exact ⟨k, k.2, congrArg Subtype.val hk⟩

theorem recAll {p : Nat → Bool} : ∀ n, Nat.rec (motive := fun _ => Bool) true
    (fun i acc => andK (p i) acc) n = true → ∀ i < n, p i = true
  | 0, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | n + 1, h, i, hi => by
    have h' : andK (p n) (Nat.rec (motive := fun _ => Bool) true
        (fun i acc => andK (p i) acc) n) = true := h
    rw [andK_eq, Bool.and_eq_true] at h'
    replace h := h'
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | hi
    · exact recAll n h.2 i hi
    · rw [hi]
      exact h.1

theorem blkRecs_spec {b : Nat} (h : blkRecs CF G N b = true) :
    ∀ i < 64, 64 * b + i < N → recT CF G N (64 * b + i) = true := by
  intro i hi hN
  have := recAll (p := fun i => implK (Nat.blt (Nat.add (Nat.mul 64 b) i) N)
    (recT CF G N (Nat.add (Nat.mul 64 b) i))) 64 h i hi
  have hb : Nat.blt (Nat.add (Nat.mul 64 b) i) N = true := blt_iff.2 hN
  rw [implK_eq, hb, if_pos rfl] at this
  exact this

theorem blk_ok {A B : Nat} {CNT : Nat → Nat} {nb : Nat} (hN : N ≤ 64 * nb)
    (h : ∀ b < nb, blkT CF G A B CNT N b = true) : ∀ k < N, recT CF G N k = true := by
  intro k hk
  have hb := h (k / 64) (by omega)
  unfold blkT at hb
  rw [andK_eq, Bool.and_eq_true] at hb
  have := blkRecs_spec hb.1 (k % 64) (Nat.mod_lt _ (by norm_num)) (by omega)
  rwa [Nat.div_add_mod] at this

end Tree

@[expose] def SU (k : Nat) (M : Matrix (Fin 22) (Fin 22) (ZMod 2)) : Prop :=
  ∀ i j : Fin 22, j.val < i.val + k → M i j = 0

@[expose] def Tri (M : Matrix (Fin 22) (Fin 22) (ZMod 2)) : Prop := SU 1 (M - 1)

section Tri

variable {M M' : Matrix (Fin 22) (Fin 22) (ZMod 2)}

theorem SU_mul {a b : Nat} (h : SU a M) (h' : SU b M') : SU (a + b) (M * M') := by
  intro i j hij
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases hl : l.val < i.val + a
  · rw [h i l hl, zero_mul]
  · rw [h' l j (by omega), mul_zero]

theorem SU_add {a : Nat} (h : SU a M) (h' : SU a M') : SU a (M + M') := fun i j hij => by
  rw [Matrix.add_apply, h i j hij, h' i j hij, add_zero]

theorem SU_mono {a b : Nat} (hab : a ≤ b) (h : SU b M) : SU a M := fun i j hij =>
  h i j (by omega)

theorem SU_pow (h : SU 1 M) : ∀ k, SU k (M ^ k)
  | 0 => by
    rw [pow_zero]
    intro i j hij
    exact Matrix.one_apply_ne fun e => by rw [e] at hij; omega
  | k + 1 => by
    rw [pow_succ]
    exact SU_mul (SU_pow h k) h

theorem SU_22 (h : SU 22 M) : M = 0 := by
  ext i j
  rw [h i j (by have := j.isLt; omega), Matrix.zero_apply]

theorem sq_one_add (M : Matrix (Fin 22) (Fin 22) (ZMod 2)) : (1 + M) ^ 2 = 1 + M ^ 2 := by
  have hz : ∀ x : ZMod 2, x + x = 0 := by decide
  have h2 : M + M = 0 := by
    ext i j
    rw [Matrix.add_apply, Matrix.zero_apply]
    exact hz _
  calc (1 + M) ^ 2 = 1 + (M + M) + M ^ 2 := by noncomm_ring
    _ = 1 + M ^ 2 := by rw [h2, add_zero]

theorem Tri_pow (h : Tri M) : M ^ 32 = 1 := by
  have hN : (M - 1) ^ 22 = 0 := SU_22 (SU_pow h 22)
  have p2 : ∀ k : Nat, (1 + (M - 1)) ^ (2 ^ k) = 1 + (M - 1) ^ (2 ^ k) := by
    intro k
    induction k with
    | zero => rw [pow_zero, pow_one, pow_one]
    | succ k ih => rw [pow_succ, pow_mul, ih, sq_one_add, ← pow_mul]
  have e : M = 1 + (M - 1) := by abel
  have h32 : (M - 1) ^ (2 ^ 5) = 0 := by
    rw [(by norm_num : 2 ^ 5 = 22 + 10), pow_add, hN, zero_mul]
  have e32 : M ^ 32 = M ^ (2 ^ 5) := by norm_num
  rw [e32, e, p2 5, h32, add_zero]

theorem Tri_one : Tri (1 : Matrix (Fin 22) (Fin 22) (ZMod 2)) := by
  unfold Tri
  rw [sub_self]
  intro i j _
  rfl

theorem Tri_mul (h : Tri M) (h' : Tri M') : Tri (M * M') := by
  unfold Tri at *
  have e : M * M' - 1 = (M - 1) * (M' - 1) + (M - 1) + (M' - 1) := by noncomm_ring
  rw [e]
  exact SU_add (SU_add (SU_mono (by norm_num) (SU_mul h h')) h) h'

theorem lowm_bits : ∀ i j : Fin 22, j ≤ i → LOWM.testBit (i.val * 22 + j.val) = true := by
  decide +kernel

theorem idp_bits : ∀ i j : Fin 22, IDP.testBit (i.val * 22 + j.val) = decide (i = j) := by
  decide +kernel

theorem Tri_of_triK {U : Nat} (h : triK U = true) : Tri (MatP 22 U) := by
  have e : U &&& LOWM = IDP := Nat.eq_of_beq_eq_true h
  intro i j hij
  have hji : j ≤ i := Fin.le_iff_val_le_val.2 (by omega)
  have hb : U.testBit (i.val * 22 + j.val) = decide (i = j) := by
    rw [← idp_bits i j, ← e, Nat.testBit_and, lowm_bits i j hji, Bool.and_true]
  rw [Matrix.sub_apply, Matrix.one_apply, MatP_apply, hb]
  by_cases hij' : i = j
  · simp [hij']
  · simp [hij']

theorem conj_pow {B Bi U : Matrix (Fin 22) (Fin 22) (ZMod 2)} (h : Bi * B = 1) (h' : B * Bi = 1) :
    ∀ n : Nat, (B * U * Bi) ^ n = B * U ^ n * Bi
  | 0 => by rw [pow_zero, pow_zero, mul_one, h']
  | n + 1 => by
    rw [pow_succ, conj_pow h h' n, pow_succ]
    simp only [mul_assoc]
    rw [← mul_assoc Bi B, h, one_mul]

theorem utK_sound {G : Nat → Nat} {B Bi : Nat} (h : utK B Bi G = true) :
    ∀ x ∈ genMon G, x ^ 32 = 1 := by
  unfold utK at h
  simp only [andK_eq, Bool.and_eq_true] at h
  obtain ⟨hb, t0, t1, t2, t3, t4⟩ := h
  have hBB : MatP 22 B * MatP 22 Bi = 1 := by
    rw [← MatP_mulV, Nat.eq_of_beq_eq_true hb, MatP_IDP]
  have hBB' : MatP 22 Bi * MatP 22 B = 1 :=
    (mul_eq_one_comm (M := Matrix (Fin 22) (Fin 22) (ZMod 2))).mp hBB
  have hgen : ∀ j < 5, Tri (MatP 22 Bi * MatP 22 (G j) * MatP 22 B) := by
    intro j hj
    have tj : triK (mulV (mulV Bi (G j)) B) = true := by
      interval_cases j
      · exact t0
      · exact t1
      · exact t2
      · exact t3
      · exact t4
    have := Tri_of_triK tj
    rwa [MatP_mulV, MatP_mulV] at this
  intro x hx
  have hT : Tri (MatP 22 Bi * x * MatP 22 B) := by
    unfold genMon at hx
    induction hx using Submonoid.closure_induction with
    | mem y hy =>
      obtain ⟨⟨j, hj⟩, rfl⟩ := hy
      exact hgen j hj
    | one =>
      rw [mul_one, hBB']
      exact Tri_one
    | mul y z _ _ hy hz =>
      have e : MatP 22 Bi * (y * z) * MatP 22 B =
          (MatP 22 Bi * y * MatP 22 B) * (MatP 22 Bi * z * MatP 22 B) := by
        simp only [mul_assoc]
        rw [← mul_assoc (MatP 22 B) (MatP 22 Bi), hBB, one_mul]
      rw [e]
      exact Tri_mul hy hz
  have ex : x = MatP 22 B * (MatP 22 Bi * x * MatP 22 B) * MatP 22 Bi := by
    simp only [mul_assoc]
    rw [← mul_assoc (MatP 22 B) (MatP 22 Bi), hBB, one_mul, mul_one]
  rw [ex, conj_pow hBB' hBB 32, Tri_pow hT, mul_one, hBB]

end Tri

section Count

variable {CF G : Nat → Nat} {N : Nat}

@[expose] noncomputable def hit (CF : Nat → Nat) (A N k : Nat) : Nat :=
  if k < N ∧ mulV (elemAt CF k) (elemAt CF k) = A then 1 else 0

theorem hit_le_one (CF : Nat → Nat) (A N k : Nat) : hit CF A N k ≤ 1 := by
  unfold hit
  split <;> omega

theorem hit_ge {CF : Nat → Nat} {A N k : Nat} (hk : N ≤ k) : hit CF A N k = 0 := by
  unfold hit
  exact if_neg fun h => absurd h.1 (by omega)

theorem sqK_eq (A B k : Nat) : sqK CF A B N k = hit CF A N k + 256 * hit CF B N k := by
  unfold sqK sqC hit
  by_cases hk : k < N
  · simp only [selN_eq, blt_iff.2 hk, strictN_eq', Nat.beq_eq, hk, true_and, if_true]
    split_ifs <;> rfl
  · simp only [selN_eq, blt_false hk, hk, false_and, if_false]
    rfl

theorem recSum (F : Nat → Nat) : ∀ n, Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Nat.add acc (F i)) n = ∑ i ∈ Finset.range n, F i
  | 0 => by
    rw [Finset.sum_range_zero]
    rfl
  | n + 1 => by
    rw [Finset.sum_range_succ, ← recSum F n]
    rfl

theorem blkSq_eq (A B b : Nat) : blkSq CF A B N b =
    (∑ i ∈ Finset.range 64, hit CF A N (64 * b + i)) +
      256 * ∑ i ∈ Finset.range 64, hit CF B N (64 * b + i) := by
  unfold blkSq
  refine (recSum (fun i => sqK CF A B N (64 * b + i)) 64).trans ?_
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => sqK_eq A B _

theorem sumBelow_eq' (m hi : Nat) (f : Nat → Nat) (hm : m ≤ 64 * hi) :
    sumBelow m hi f = ∑ i ∈ Finset.range m, f i := by
  have rec_sum : ∀ (F : Nat → Nat) (k : Nat),
      Nat.rec (motive := fun _ => Nat) 0 (fun l ih2 => Nat.add (F l) ih2) k =
        ∑ l ∈ Finset.range k, F l := by
    intro F k
    induction k with
    | zero =>
      rw [Finset.sum_range_zero]
      rfl
    | succ k ih =>
      rw [Finset.sum_range_succ, ← ih]
      exact Nat.add_comm _ _
  have sel : ∀ (b : Bool) (x : Nat), Bool.rec (motive := fun _ => Nat) 0 x b =
      if b = true then x else 0 := by
    intro b x
    cases b <;> rfl
  have hgen : ∀ h, sumBelow m h f =
      ∑ i ∈ Finset.range (64 * h), if i < m then f i else 0 := by
    intro h
    induction h with
    | zero =>
      rw [Nat.mul_zero, Finset.sum_range_zero]
      rfl
    | succ h ih =>
      change Nat.rec (motive := fun _ => Nat) 0 (fun l ih2 =>
        Nat.add ((fun i => Bool.rec (motive := fun _ => Nat) 0 (f i) (Nat.blt i m))
          (Nat.add (Nat.shiftLeft h 6) l)) ih2) 64 + sumBelow m h f = _
      rw [rec_sum, ih, Nat.mul_succ, Finset.sum_range_add,
        Nat.add_comm (Finset.sum (Finset.range 64) _)]
      refine Nat.add_left_cancel_iff.2 (Finset.sum_congr rfl fun l _ => ?_)
      have e : Nat.add (Nat.shiftLeft h 6) l = 64 * h + l := by
        change h <<< 6 + l = 64 * h + l
        rw [Nat.shiftLeft_eq]
        omega
      simp only [e, sel, Nat.blt_eq]
  have hsplit : 64 * hi = m + (64 * hi - m) := by omega
  rw [hgen hi, hsplit, Finset.sum_range_add]
  rw [Finset.sum_eq_zero (s := Finset.range (64 * hi - m)) (fun i _ => ite_eq_right (by omega)),
    Nat.add_zero]
  exact Finset.sum_congr rfl fun i hi => ite_eq_left (Finset.mem_range.1 hi)

theorem sum_blocks (F : Nat → Nat) : ∀ m, ∑ b ∈ Finset.range m, ∑ i ∈ Finset.range 64,
    F (64 * b + i) = ∑ k ∈ Finset.range (64 * m), F k
  | 0 => by simp
  | m + 1 => by
    rw [Finset.sum_range_succ, sum_blocks F m, Nat.mul_succ, Finset.sum_range_add]

theorem fld_byte (c r : Nat) : fld(c, Nat.mul (nat_lit 8) r, nat_lit 255) = c / 2 ^ (8 * r) % 256 := by
  change (c >>> (8 * r)) &&& (2 ^ 8 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

theorem sq_total {A B : Nat} {CNT : Nat → Nat} {hi : Nat} (hN : N ≤ 4096 * hi)
    (h : ∀ b < 64 * hi, blkT CF G A B CNT N b = true) :
    cntTotal CNT 0 hi = ∑ k ∈ Finset.range N, hit CF A N k ∧
      cntTotal CNT 1 hi = ∑ k ∈ Finset.range N, hit CF B N k := by
  have hc : ∀ b < 64 * hi, cntAt CNT b = blkSq CF A B N b := by
    intro b hb
    have := h b hb
    unfold blkT at this
    rw [andK_eq, Bool.and_eq_true] at this
    exact (Nat.eq_of_beq_eq_true this.2).symm
  have hle : ∀ Y b, ∑ i ∈ Finset.range 64, hit CF Y N (64 * b + i) ≤ 64 := fun Y b =>
    (Finset.sum_le_sum fun i _ => hit_le_one CF Y N (64 * b + i)).trans (by simp)
  have tail : ∀ Y, ∑ k ∈ Finset.range (64 * (64 * hi)), hit CF Y N k =
      ∑ k ∈ Finset.range N, hit CF Y N k := by
    intro Y
    have hm : 64 * (64 * hi) = N + (64 * (64 * hi) - N) := by omega
    rw [hm, Finset.sum_range_add, Finset.sum_eq_zero (s := Finset.range (64 * (64 * hi) - N))
      (f := fun k => hit CF Y N (N + k)) (fun k _ => hit_ge (by omega)), add_zero]
  have key : ∀ r, cntTotal CNT r hi =
      ∑ b ∈ Finset.range (64 * hi), cntAt CNT b / 2 ^ (8 * r) % 256 := by
    intro r
    unfold cntTotal
    exact (sumBelow_eq' _ hi _ (le_refl (64 * hi))).trans
      (Finset.sum_congr rfl fun b _ => fld_byte _ _)
  constructor
  · rw [key 0, ← tail A, ← sum_blocks (hit CF A N) (64 * hi)]
    refine Finset.sum_congr rfl fun b hb => ?_
    rw [hc b (Finset.mem_range.1 hb), blkSq_eq]
    have := hle A b
    simp only [Nat.mul_zero, pow_zero, Nat.div_one]
    omega
  · rw [key 1, ← tail B, ← sum_blocks (hit CF B N) (64 * hi)]
    refine Finset.sum_congr rfl fun b hb => ?_
    rw [hc b (Finset.mem_range.1 hb), blkSq_eq, (by norm_num : (2 : Nat) ^ (8 * 1) = 256)]
    have := hle A b
    have := hle B b
    omega

theorem sq_card (hR : TreeRecs CF G N) (hc : Nat.card (genMon G) ≤ N) {A : Nat} (hA : A < 2 ^ 484) :
    Nat.card {x : genMon G // (x : Matrix (Fin 22) (Fin 22) (ZMod 2)) * x = MatP 22 A} =
      ∑ k ∈ Finset.range N, hit CF A N k := by
  let e := Equiv.ofBijective _ (entF_bij hR hc)
  have h1 : Nat.card {x : genMon G // (x : Matrix (Fin 22) (Fin 22) (ZMod 2)) * x = MatP 22 A} =
      Nat.card {k : Fin N // mulV (elemAt CF k) (elemAt CF k) = A} := by
    refine Nat.card_congr (e.subtypeEquiv fun k => ?_).symm
    change _ ↔ MatP 22 (elemAt CF k) * MatP 22 (elemAt CF k) = MatP 22 A
    rw [← MatP_mulV]
    exact ⟨fun h => by rw [h], fun h => MatP_inj' (mulV_lt _ _) hA h⟩
  rw [h1, Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter, Finset.sum_range]
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold hit
  simp [k.isLt]

theorem sq_count (hR : TreeRecs CF G N) (hc : Nat.card (genMon G) ≤ N) {A B : Nat}
    {CNT : Nat → Nat} {hi : Nat} (hA : A < 2 ^ 484) (hB : B < 2 ^ 484) (hN : N ≤ 4096 * hi)
    (h : ∀ b < 64 * hi, blkT CF G A B CNT N b = true) :
    Nat.card {x : genMon G // (x : Matrix (Fin 22) (Fin 22) (ZMod 2)) * x = MatP 22 A} =
        cntTotal CNT 0 hi ∧
      Nat.card {x : genMon G // (x : Matrix (Fin 22) (Fin 22) (ZMod 2)) * x = MatP 22 B} =
        cntTotal CNT 1 hi := by
  obtain ⟨t0, t1⟩ := sq_total (G := G) hN h
  exact ⟨(sq_card hR hc hA).trans t0.symm, (sq_card hR hc hB).trans t1.symm⟩

end Count

section Labels

variable {CF G LD : Nat → Nat} {N R : Nat}

theorem cjK_spec {X l g c : Nat} (h : cjK CF LD N X l g c = true) :
    c < N ∧ mulV (elemAt CF c) g = mulV g X ∧ labK0 LD c = l := by
  unfold cjK at h
  simp only [andK_eq, Bool.and_eq_true] at h
  exact ⟨blt_iff.1 h.1, Nat.eq_of_beq_eq_true h.2.1, Nat.eq_of_beq_eq_true h.2.2⟩

theorem dK_spec {l d Z : Nat} (h : dK CF LD N l d Z = true) :
    (d < N ∧ elemAt CF d = Z ∧ labK0 LD d ≠ l) ∨ (¬ d < N ∧ involK Z = false) := by
  unfold dK at h
  rw [bIf_eq'] at h
  by_cases hd : d < N
  · rw [blt_iff.2 hd, if_pos rfl, andK_eq, Bool.and_eq_true, notK_eq, Bool.not_eq_true'] at h
    exact Or.inl ⟨hd, Nat.eq_of_beq_eq_true h.1, Nat.ne_of_beq_eq_false h.2⟩
  · rw [blt_false hd, if_neg Bool.false_ne_true, notK_eq, Bool.not_eq_true'] at h
    exact Or.inr ⟨hd, h⟩

theorem labK_spec {k : Nat} (h : labK CF G LD R N k = true) (hi : involK (elemAt CF k) = true) :
    (∀ j < 5, cjOf (labAt LD k) j < N ∧
      mulV (elemAt CF (cjOf (labAt LD k) j)) (G j) = mulV (G j) (elemAt CF k) ∧
      labK0 LD (cjOf (labAt LD k) j) = labK0 LD k) ∧
    dK CF LD N (labK0 LD k) (dOf (labAt LD k)) (mulV (elemAt CF k) R) = true := by
  unfold labK at h
  simp only [letB_eq] at h
  rw [implK_eq, if_pos hi] at h
  simp only [letB_eq, andK_eq, Bool.and_eq_true] at h
  obtain ⟨c0, c1, c2, c3, c4, hd⟩ := h
  refine ⟨fun j hj => ?_, hd⟩
  interval_cases j
  · exact cjK_spec c0
  · exact cjK_spec c1
  · exact cjK_spec c2
  · exact cjK_spec c3
  · exact cjK_spec c4

theorem conj_invol {a b w v : Matrix (Fin 22) (Fin 22) (ZMod 2)} (hwv : w * v = 1) (hvw : v * w = 1)
    (h : a * w = w * b) (hb : b * b = 1) (hb1 : b ≠ 1) : a * a = 1 ∧ a ≠ 1 := by
  have ha : a = w * b * v := by
    calc a = a * (w * v) := by rw [hwv, mul_one]
      _ = w * b * v := by rw [← mul_assoc, h]
  refine ⟨?_, fun e => hb1 ?_⟩
  · rw [ha]
    simp only [mul_assoc]
    rw [← mul_assoc v w, hvw, one_mul, ← mul_assoc b b, hb, one_mul, hwv]
  · calc b = v * w * b := by rw [hvw, one_mul]
      _ = v * (w * b) := by rw [mul_assoc]
      _ = v * (1 * w) := by rw [← h, e]
      _ = 1 := by rw [one_mul, hvw]

theorem cancel_right {a b w v : Matrix (Fin 22) (Fin 22) (ZMod 2)} (hwv : w * v = 1)
    (h : a * w = b * w) : a = b := by
  calc a = a * w * v := by rw [mul_assoc, hwv, mul_one]
    _ = b := by rw [h, mul_assoc, hwv, mul_one]

theorem lab_conj (hpow : ∀ x ∈ genMon G, x ^ 32 = 1) (hL : ∀ k < N, labK CF G LD R N k = true) :
    ∀ w ∈ genMon G, ∀ k < N, involK (elemAt CF k) = true → ∃ k' < N,
      involK (elemAt CF k') = true ∧ MatP 22 (elemAt CF k') * w = w * MatP 22 (elemAt CF k) ∧
        labK0 LD k' = labK0 LD k := by
  intro w hw
  unfold genMon at hw
  induction hw using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨⟨j, hj⟩, rfl⟩ := hx
    intro k hk hi
    obtain ⟨c1, c2, c3⟩ := (labK_spec (hL k hk) hi).1 j hj
    have hg := hpow _ (gen_mem G hj)
    have hgv : MatP 22 (G j) * MatP 22 (G j) ^ 31 = 1 := by
      rw [← pow_succ']
      exact hg
    have hvg : MatP 22 (G j) ^ 31 * MatP 22 (G j) = 1 := by
      rw [← pow_succ]
      exact hg
    have e : MatP 22 (elemAt CF (cjOf (labAt LD k) j)) * MatP 22 (G j) =
        MatP 22 (G j) * MatP 22 (elemAt CF k) := by
      rw [← MatP_mulV, ← MatP_mulV, c2]
    obtain ⟨hb, hb1⟩ := (involK_iff (elemAt_lt CF k)).1 hi
    refine ⟨_, c1, (involK_iff (elemAt_lt CF _)).2 (conj_invol hgv hvg e hb hb1), e, c3⟩
  | one =>
    intro k hk hi
    exact ⟨k, hk, hi, by rw [mul_one, one_mul], rfl⟩
  | mul x y _ _ ihx ihy =>
    intro k hk hi
    obtain ⟨k2, hk2, hi2, e2, l2⟩ := ihy k hk hi
    obtain ⟨k1, hk1, hi1, e1, l1⟩ := ihx k2 hk2 hi2
    refine ⟨k1, hk1, hi1, ?_, l1.trans l2⟩
    rw [← mul_assoc, e1, mul_assoc, e2, ← mul_assoc]

theorem lab_sound (hR : TreeRecs CF G N) (hc : Nat.card (genMon G) ≤ N)
    (hpow : ∀ x ∈ genMon G, x ^ 32 = 1) (hL : ∀ k < N, labK CF G LD R N k = true) :
    ¬ ∃ u ∈ genMon G, ∃ w ∈ genMon G, u * u = 1 ∧ u ≠ 1 ∧ w * u = u * MatP 22 R * w := by
  rintro ⟨u, hu, w, hw, huu, hu1, hwu⟩
  obtain ⟨k, hk, rfl⟩ := tree_surj hR hc u hu
  have hi : involK (elemAt CF k) = true := (involK_iff (elemAt_lt CF k)).2 ⟨huu, hu1⟩
  obtain ⟨k', hk', hi', e', l'⟩ := lab_conj hpow hL w hw k hk hi
  have hwv : w * w ^ 31 = 1 := by
    rw [← pow_succ']
    exact hpow w hw
  have hZ : MatP 22 (elemAt CF k') = MatP 22 (mulV (elemAt CF k) R) := by
    rw [MatP_mulV]
    refine cancel_right hwv ?_
    rw [e', hwu]
  rcases dK_spec (labK_spec (hL k hk) hi).2 with ⟨hd1, hd2, hd3⟩ | ⟨-, hd2⟩
  · have hdk : dOf (labAt LD k) = k' := tree_inj hR _ hd1 _ hk' (by rw [hd2, hZ])
    rw [hdk, l'] at hd3
    exact hd3 rfl
  · have hinv := (involK_iff (elemAt_lt CF k')).1 hi'
    rw [hZ] at hinv
    rw [(involK_iff (mulV_lt _ _)).2 hinv] at hd2
    exact Bool.noConfusion hd2

theorem witK_sound (hR : TreeRecs CF G N) {a b : Nat} (h : witK CF R N a b = true) :
    ∃ u ∈ genMon G, ∃ w ∈ genMon G, u * u = 1 ∧ u ≠ 1 ∧ w * u = u * MatP 22 R * w := by
  unfold witK at h
  simp only [andK_eq, Bool.and_eq_true] at h
  obtain ⟨ha, hb, hi, he⟩ := h
  obtain ⟨h1, h2⟩ := (involK_iff (elemAt_lt CF a)).1 hi
  refine ⟨_, tree_mem hR a (blt_iff.1 ha), _, tree_mem hR b (blt_iff.1 hb), h1, h2, ?_⟩
  rw [← MatP_mulV, ← MatP_mulV, ← MatP_mulV, Nat.eq_of_beq_eq_true he]

end Labels

theorem memK_sound {CF G : Nat → Nat} {N : Nat} (hR : TreeRecs CF G N) {X k : Nat}
    (h : memK CF N X k = true) : MatP 22 X ∈ genMon G := by
  unfold memK at h
  rw [andK_eq, Bool.and_eq_true] at h
  rw [← Nat.eq_of_beq_eq_true h.2]
  exact tree_mem hR k (blt_iff.1 h.1)

theorem commK_sound {X Y : Nat} (h : commK X Y = true) :
    MatP 22 X * MatP 22 Y = MatP 22 Y * MatP 22 X := by
  rw [← MatP_mulV, ← MatP_mulV, Nat.eq_of_beq_eq_true h]

end CFSG.KC.Co2Syl

end
