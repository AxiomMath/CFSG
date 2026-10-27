module

public import CFSG.Certificates.Kernel.SporSch.MatRep

public section

namespace CFSG.KS.MatInj

open CFSG.RankThree.Native.F2 CFSG.Monster.B.Co2.Native CFSG.KS.MatRep

variable {d : ℕ} {V : Array ℕ}

@[expose] def xorAt (V : Array ℕ) (l : List ℕ) : ℕ := l.foldr (fun i acc => V[i]! ^^^ acc) 0

@[expose] def Spans (d : ℕ) (V : Array ℕ) : Prop :=
  ∀ r < d, ∃ l : List ℕ, (∀ i ∈ l, i < V.size) ∧ xorAt V l = 2 ^ r

theorem vmul_xorAt (M : ℕ) (l : List ℕ) :
    vmul d (xorAt V l) M = l.foldr (fun i acc => vmul d V[i]! M ^^^ acc) 0 := by
  induction l with
  | nil => exact vmul_zero M
  | cons i l ih =>
    rw [xorAt, List.foldr_cons, vmul_xor, ← xorAt, ih, List.foldr_cons]

theorem eq_of_vmul (hS : Spans d V) {X Y : ℕ} (hX : X < 2 ^ (d * d)) (hY : Y < 2 ^ (d * d))
    (h : ∀ i < V.size, vmul d V[i]! X = vmul d V[i]! Y) : X = Y := by
  refine mat_ext hX hY fun r hr => ?_
  obtain ⟨l, hl, hx⟩ := hS r hr
  rw [← vmul_unit X hr, ← vmul_unit Y hr, ← hx, vmul_xorAt, vmul_xorAt]
  have : ∀ l' : List ℕ, (∀ i ∈ l', i < V.size) →
      l'.foldr (fun i acc => vmul d V[i]! X ^^^ acc) 0 =
        l'.foldr (fun i acc => vmul d V[i]! Y ^^^ acc) 0 := by
    intro l' hl'
    induction l' with
    | nil => rfl
    | cons i l' ih =>
      rw [List.foldr_cons, List.foldr_cons, h i (hl' i List.mem_cons_self),
        ih fun j hj => hl' j (List.mem_cons_of_mem _ hj)]
  exact this l hl

theorem eqA_refl (n : ℕ) (t : Array ℕ) : eqA n t t = true := by
  rw [eqA, CFSG.Monster.B.Co2.allLt_iff]
  intro i _
  exact beq_self_eq_true _

theorem eqA_permOfMat (hS : Spans d V) {X Y : ℕ} (hX : ∀ v ∈ V, vmul d v X ∈ V)
    (hY : ∀ v ∈ V, vmul d v Y ∈ V) (hXl : X < 2 ^ (d * d)) (hYl : Y < 2 ^ (d * d)) :
    eqA V.size (permOfMat d V X) (permOfMat d V Y) = Nat.beq X Y := by
  by_cases e : X = Y
  · rw [e, Nat.beq_refl]
    exact eqA_refl _ _
  · have hb : Nat.beq X Y = false := Bool.eq_false_iff.2 fun h => e (Nat.eq_of_beq_eq_true h)
    rw [hb]
    by_contra hne
    rw [Bool.not_eq_false, eqA, CFSG.Monster.B.Co2.allLt_iff] at hne
    refine e (eq_of_vmul hS hXl hYl fun i hi => ?_)
    have hv := beq_iff_eq.1 (hne i hi)
    rw [permOfMat_get hi, permOfMat_get hi] at hv
    rw [← (getElem_vidx (hX _ (mem_of_lt hi))).2, ← (getElem_vidx (hY _ (mem_of_lt hi))).2, hv]

theorem row_mod (M : ℕ) {k : ℕ} (hk : k < d) : row d (M % 2 ^ (d * d)) k = row d M k := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [testBit_row, testBit_row, Nat.testBit_mod_two_pow]
  by_cases hj : j < d
  · have : d * k + j < d * d := by
      have := Nat.mul_le_mul_left d (Nat.succ_le_of_lt hk)
      rw [Nat.mul_succ] at this
      omega
    simp [hj, this]
  · simp [hj]

theorem vmul_mod (v M : ℕ) : vmul d v (M % 2 ^ (d * d)) = vmul d v M := by
  unfold vmul
  have : ∀ L : List ℕ, (∀ k ∈ L, k < d) →
      L.foldr (fun k acc => if v.testBit k then row d (M % 2 ^ (d * d)) k ^^^ acc else acc) 0 =
        L.foldr (fun k acc => if v.testBit k then row d M k ^^^ acc else acc) 0 := by
    intro L hL
    induction L with
    | nil => rfl
    | cons k l ih =>
      rw [List.foldr_cons, List.foldr_cons, ih fun j hj => hL j (List.mem_cons_of_mem _ hj),
        row_mod M (hL k List.mem_cons_self)]
  exact this _ fun k hk => List.mem_range.1 hk

theorem eqA_permOfMat_mod (hS : Spans d V) {X Y : ℕ} (hX : ∀ v ∈ V, vmul d v X ∈ V)
    (hY : ∀ v ∈ V, vmul d v Y ∈ V) :
    eqA V.size (permOfMat d V X) (permOfMat d V Y) =
      Nat.beq (X % 2 ^ (d * d)) (Y % 2 ^ (d * d)) := by
  have e : ∀ Z : ℕ, permOfMat d V (Z % 2 ^ (d * d)) = permOfMat d V Z := fun Z => by
    unfold permOfMat
    simp only [vmul_mod]
  rw [← e X, ← e Y]
  refine eqA_permOfMat hS ?_ ?_ (Nat.mod_lt _ (Nat.two_pow_pos _)) (Nat.mod_lt _ (Nat.two_pow_pos _))
  · intro v hv
    rw [vmul_mod]
    exact hX v hv
  · intro v hv
    rw [vmul_mod]
    exact hY v hv

theorem rep_of_inv (hd : 0 < d) (hVd : ∀ v ∈ V, v < 2 ^ d) {a : Array ℕ} {M M' M'' : ℕ}
    (h : Rep d V a M M') (h1 : mmul d M M'' = idM d) (h2 : mmul d M'' M = idM d) :
    Rep d V a M M'' := by
  refine ⟨h.1, h.2.1, fun v hv => ?_, h1, h2⟩
  have hv' := hVd v hv
  have e : vmul d v M'' = vmul d v M' := by
    calc vmul d v M'' = vmul d (vmul d v (idM d)) M'' := by rw [vmul_idM hd hv']
      _ = vmul d (vmul d v (mmul d M' M)) M'' := by rw [h.2.2.2.2]
      _ = vmul d (vmul d (vmul d v M') M) M'' := by rw [vmul_mmul]
      _ = vmul d (vmul d v M') (mmul d M M'') := by rw [vmul_mmul]
      _ = vmul d (vmul d v M') (idM d) := by rw [h1]
      _ = vmul d v M' := vmul_idM hd (vmul_lt _ _)
  rw [e]
  exact h.2.2.1 v hv

end CFSG.KS.MatInj

end
