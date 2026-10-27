module

public import CFSG.Certificates.Kernel.RankThree.F2Mat
public import CFSG.RankThree.Native.PermEnumeration

public section

namespace CFSG.RankThree.Native.F2

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

variable {d : ℕ}

variable (d) in
@[expose] def idM : ℕ := bs d (fun k => 2 ^ k % 2 ^ d) d

theorem row_idM (hd : 0 < d) {k : ℕ} (hk : k < d) : row d (idM d) k = 2 ^ k := by
  rw [idM, row_bs hd (fun k => Nat.mod_lt _ (Nat.two_pow_pos d)) hk,
    Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) hk)]

theorem vmul_idM (hd : 0 < d) {v : ℕ} (hv : v < 2 ^ d) : vmul d v (idM d) = v := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < d
  · apply bz_inj
    rw [bz_testBit_vmul, Finset.sum_eq_single j]
    · rw [row_idM hd hj, Nat.testBit_two_pow_self]
      simp [bz]
    · intro k hk hkj
      rw [row_idM hd (Finset.mem_range.1 hk), Nat.testBit_two_pow]
      simp [bz, hkj]
    · intro h
      exact absurd (Finset.mem_range.2 hj) h
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (vmul_lt _ _) (Nat.pow_le_pow_right (by norm_num)
      (Nat.le_of_not_lt hj))), Nat.testBit_lt_two_pow (lt_of_lt_of_le hv
      (Nat.pow_le_pow_right (by norm_num) (Nat.le_of_not_lt hj)))]

variable {V : Array ℕ}

theorem vidx_get (hV : V.toList.Nodup) {i : ℕ} (hi : i < V.size) : vidx V V[i]! = i := by
  rw [getElem!_pos V i hi, vidx, ← Array.getElem_toList]
  exact hV.idxOf_getElem i (by simpa using hi)

theorem mem_of_lt {i : ℕ} (hi : i < V.size) : V[i]! ∈ V := by
  rw [getElem!_pos V i hi]
  exact Array.getElem_mem hi

theorem eq_permOfMat (hV : V.toList.Nodup) {a : Array ℕ} {M : ℕ} (hs : a.size = V.size)
    (h : ∀ i < V.size, a[i]! < V.size ∧ V[a[i]!]! = vmul d V[i]! M) : a = permOfMat d V M := by
  apply Array.ext
  · rw [permOfMat_size, hs]
  · intro i h1 h2
    have hi : i < V.size := by rwa [hs] at h1
    rw [← getElem!_pos a i h1, ← getElem!_pos (permOfMat d V M) i h2, permOfMat_get hi,
      ← (h i hi).2, vidx_get hV (h i hi).1]

theorem permOfMat_idM (hd : 0 < d) (hV : V.toList.Nodup) (hVd : ∀ v ∈ V, v < 2 ^ d) :
    permOfMat d V (idM d) = idA V.size := by
  apply Array.ext
  · simp [permOfMat, idA]
  · intro i h1 h2
    have hi : i < V.size := by simpa [permOfMat] using h1
    rw [← getElem!_pos _ i h1, permOfMat_get hi, vmul_idM hd (hVd _ (mem_of_lt hi)),
      vidx_get hV hi, ← getElem!_pos _ i h2, idA_get hi]

@[expose] def Inv (d : ℕ) (V : Array ℕ) (M M' : ℕ) : Prop :=
  (∀ v ∈ V, vmul d v M ∈ V) ∧ (∀ v ∈ V, vmul d v M' ∈ V) ∧ mmul d M M' = idM d ∧
    mmul d M' M = idM d

theorem isInvA_permOfMat (hd : 0 < d) (hV : V.toList.Nodup) (hVd : ∀ v ∈ V, v < 2 ^ d)
    {M M' : ℕ} (h : Inv d V M M') : isInvA V.size (permOfMat d V M) (permOfMat d V M') = true := by
  rw [isInvA, allLt_iff]
  intro i hi
  have hm := h.1 _ (mem_of_lt hi)
  obtain ⟨hlt, hget⟩ := getElem_vidx hm
  rw [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, permOfMat_get hi]
  refine ⟨hlt, ?_⟩
  rw [permOfMat_get hlt, hget, ← vmul_mmul, h.2.2.1, vmul_idM hd (hVd _ (mem_of_lt hi)),
    vidx_get hV hi]

@[expose] noncomputable def sigma (d : ℕ) (V : Array ℕ) (M : ℕ) : Equiv.Perm (Fin V.size) :=
  permOfArr V.size (permOfMat d V M)

theorem rep_permOfMat (hd : 0 < d) (hV : V.toList.Nodup) (hVd : ∀ v ∈ V, v < 2 ^ d)
    {M M' : ℕ} (h : Inv d V M M') : Rep V.size (permOfMat d V M) (sigma d V M) :=
  (rep_permOfArr (isInvA_permOfMat hd hV hVd h)).1

theorem sigma_mmul (hd : 0 < d) (hV : V.toList.Nodup) (hVd : ∀ v ∈ V, v < 2 ^ d)
    {A A' B B' : ℕ} (hA : Inv d V A A') (hB : Inv d V B B') (hAB : Inv d V (mmul d A B) (mmul d B' A')) :
    sigma d V (mmul d A B) = sigma d V B * sigma d V A := by
  have h1 := rep_permOfMat hd hV hVd hAB
  rw [permOfMat_mmul hA.1] at h1
  exact h1.unique (rep_compA (rep_permOfMat hd hV hVd hB) (rep_permOfMat hd hV hVd hA))

theorem invCand_eq_foldl (n : ℕ) (t : Array ℕ) :
    invCand n t = (List.range n).foldl (fun r i => r.set! t[i]! i) (Array.replicate n 0) := by
  unfold invCand
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl,
    Std.Legacy.Range.size]
  simp only [Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, bind_pure, List.range_eq_range']
  rfl

theorem rep_invCand {n : ℕ} {t : Array ℕ} {g : Equiv.Perm (Fin n)} (ht : Rep n t g) :
    Rep n (invCand n t) g⁻¹ := by
  have key : ∀ k ≤ n, ((List.range k).foldl (fun r i => r.set! t[i]! i)
      (Array.replicate n 0)).size = n ∧ ∀ i < k, ((List.range k).foldl (fun r i => r.set! t[i]! i)
      (Array.replicate n 0))[t[i]!]! = i := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      obtain ⟨hs, hi⟩ := ih (by omega)
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      set r := (List.range k).foldl (fun r i => r.set! t[i]! i) (Array.replicate n 0)
      have htk : t[k]! < n := ht.lt (by omega)
      refine ⟨by rw [Array.size_set!, hs], fun i hik => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hik with hlt | rfl
      · have hne : t[i]! ≠ t[k]! := by
          intro e
          rw [ht.apply (by omega : i < n), ht.apply (by omega : k < n)] at e
          have := g.injective (Fin.ext e)
          simp at this
          omega
        rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hne)]
        exact hi i hlt
      · rw [Array.getElem!_set!_self _ _ _ (by rw [hs]; exact htk)]
  intro x
  obtain ⟨hs, hi⟩ := key n le_rfl
  rw [invCand_eq_foldl]
  have e : t[(g⁻¹ x : Fin n).val]! = x.val := by
    rw [ht.apply (g⁻¹ x).2]
    simp
  rw [← e, hi _ (g⁻¹ x).2]

theorem validA_of_rep {n : ℕ} {t : Array ℕ} {g : Equiv.Perm (Fin n)} (ht : Rep n t g) :
    CFSG.RankThree.Native.validA n t = true := by
  have hr := rep_invCand ht
  rw [CFSG.RankThree.Native.validA, isInvA, allLt_iff]
  intro i hi
  rw [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, ht.apply hi]
  refine ⟨(g _).2, ?_⟩
  rw [hr.apply (g _).2]
  simp

theorem validA_permOfMat (hd : 0 < d) (hV : V.toList.Nodup) (hVd : ∀ v ∈ V, v < 2 ^ d)
    {M M' : ℕ} (h : Inv d V M M') : CFSG.RankThree.Native.validA V.size (permOfMat d V M) = true :=
  validA_of_rep (rep_permOfMat hd hV hVd h)

@[expose] def Spans (d : ℕ) (V : Array ℕ) (l : ℕ → List ℕ) : Prop :=
  ∀ k < d, (∀ i ∈ l k, i < V.size) ∧ (l k).foldr (fun i acc => V[i]! ^^^ acc) 0 = 2 ^ k

theorem vmul_fold (M : ℕ) (L : List ℕ) :
    vmul d (L.foldr (fun i acc => V[i]! ^^^ acc) 0) M =
      L.foldr (fun i acc => vmul d V[i]! M ^^^ acc) 0 := by
  induction L with
  | nil => exact vmul_zero M
  | cons i l ih => rw [List.foldr_cons, List.foldr_cons, vmul_xor, ih]

theorem eqA_permOfMat {l : ℕ → List ℕ} (hs : Spans d V l) {A B : ℕ}
    (hA : ∀ v ∈ V, vmul d v A ∈ V) (hB : ∀ v ∈ V, vmul d v B ∈ V) (hAl : A < 2 ^ (d * d))
    (hBl : B < 2 ^ (d * d)) :
    eqA V.size (permOfMat d V A) (permOfMat d V B) = Nat.beq A B := by
  rw [Bool.eq_iff_iff, Nat.beq_eq]
  constructor
  · intro h
    rw [eqA, allLt_iff] at h
    have hv : ∀ i < V.size, vmul d V[i]! A = vmul d V[i]! B := by
      intro i hi
      have h1 := h i hi
      rw [beq_iff_eq, permOfMat_get hi, permOfMat_get hi] at h1
      rw [← (getElem_vidx (hA _ (mem_of_lt hi))).2, h1, (getElem_vidx (hB _ (mem_of_lt hi))).2]
    apply mat_ext hAl hBl
    intro k hk
    obtain ⟨hlk, hsum⟩ := hs k hk
    rw [← vmul_unit A hk, ← vmul_unit B hk, ← hsum, vmul_fold, vmul_fold]
    have : ∀ L : List ℕ, (∀ i ∈ L, i < V.size) →
        L.foldr (fun i acc => vmul d V[i]! A ^^^ acc) 0 =
          L.foldr (fun i acc => vmul d V[i]! B ^^^ acc) 0 := by
      intro L hL
      induction L with
      | nil => rfl
      | cons i l ih =>
        rw [List.foldr_cons, List.foldr_cons, hv i (hL i List.mem_cons_self),
          ih fun j hj => hL j (List.mem_cons_of_mem _ hj)]
    exact this _ hlk
  · rintro rfl
    rw [eqA, allLt_iff]
    intro i _
    exact beq_self_eq_true _

end CFSG.RankThree.Native.F2

end
