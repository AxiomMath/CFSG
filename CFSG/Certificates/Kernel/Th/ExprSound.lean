module

public import CFSG.Certificates.Kernel.Th.Expr
public import CFSG.Certificates.Kernel.Th.Max3S.Regs
public import CFSG.Sporadic.Th.Max3.AllConjInputs

public section

namespace CFSG.KC.Th.Expr

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Max3 CFSG.KC.Th.Spec
open CFSG.Sporadic.Th.Native (V4 idRows rowsOf seedA seedB)

@[expose] def TE.rows : TE → Array V4
  | .one => idRows
  | .a => rowsA
  | .b => rowsB
  | .x => rowsX
  | .y => rowsY
  | .z => rowsZ
  | .q i => rowsQ i
  | .nf j => rowsNfAt j
  | .nfE s e => rowsNf s e
  | .word w => wordRows rowsX rowsY w
  | .ab w => AllConj.abRows w
  | .prodFn _ f => prodRows (List.ofFn fun j => (f j).rows)
  | .mul e f => Native.mulRows e.rows f.rows
  | .pow e n => powRows e.rows n

@[expose] def TE.Facts : List (TE × TE × Bool) → Prop
  | [] => True
  | [t] => Native.eqRows t.1.rows t.2.1.rows = t.2.2
  | t :: l => Native.eqRows t.1.rows t.2.1.rows = t.2.2 ∧ TE.Facts l

@[expose] def kOf (D : CFSG.KC.Th.Gen.Max3Data) : K :=
  ⟨D.ThM3_RB, D.ThS_c, D.ThS_rm, D.ThS_ONE, D.ThSeed_SA, D.ThSeed_SB⟩

section Pinned

local notation "A₀" => rowsOf seedA
local notation "B₀" => rowsOf seedB

theorem eq_t3 : Max3S.t3 A₀ B₀ = Slp.rowsT3 := rfl
theorem eq_t4 : Max3S.t4 A₀ B₀ = Slp.rowsT4 := by rw [Max3S.t4, eq_t3]; rfl
theorem eq_t5 : Max3S.t5 A₀ B₀ = Slp.rowsT5 := by rw [Max3S.t5, eq_t3, eq_t4]; rfl
theorem eq_t6 : Max3S.t6 A₀ B₀ = Slp.rowsT6 := by rw [Max3S.t6, eq_t3, eq_t5]; rfl
theorem eq_t7 : Max3S.t7 A₀ B₀ = Slp.rowsT7 := by rw [Max3S.t7, eq_t6]; rfl
theorem eq_t8 : Max3S.t8 A₀ B₀ = Slp.rowsT8 := by rw [Max3S.t8, eq_t6]; rfl
theorem eq_u : Max3S.u A₀ B₀ = Slp.rowsU := by rw [Max3S.u, eq_t8, eq_t7]; rfl
theorem eq_s8 : Max3S.s8 A₀ B₀ = Slp.rowsS8 := by rw [Max3S.s8, eq_t6, eq_t5]; rfl
theorem eq_s9 : Max3S.s9 A₀ B₀ = Slp.rowsS9 := by rw [Max3S.s9, eq_t3, eq_s8]; rfl
theorem eq_s10 : Max3S.s10 A₀ B₀ = Slp.rowsS10 := by rw [Max3S.s10, eq_s9, eq_t4]; rfl
theorem eq_s7 : Max3S.s7 A₀ B₀ = Slp.rowsS7 := by rw [Max3S.s7, eq_s10]; rfl
theorem eq_s8' : Max3S.s8' A₀ B₀ = Slp.rowsS8' := by rw [Max3S.s8', eq_s10]; rfl
theorem eq_v : Max3S.v A₀ B₀ = Slp.rowsV := by rw [Max3S.v, eq_s8', eq_s7]; rfl
theorem eq_x : Max3S.x A₀ B₀ = rowsX := by rw [Max3S.x, eq_v]; rfl
theorem eq_y : Max3S.y A₀ B₀ = rowsY := by rw [Max3S.y, eq_t7, eq_u]; rfl
theorem eq_z : Max3S.z A₀ B₀ = rowsZ := by rw [Max3S.z, eq_x, eq_y]; rfl

theorem eq_q (i : Fin 8) : Max3S.q A₀ B₀ i = rowsQ i := by
  simp only [Max3S.q, Max3S.qs, rowsQ, rowsQs, Array.getElem_ofFn, eq_x, eq_y]

theorem eq_nf (s : ℕ) (e : Fin 8 → ℕ) : Max3S.nf A₀ B₀ s e = rowsNf s e := by
  simp only [Max3S.nf, rowsNf, eq_z, eq_q]

theorem eq_nfAt (j : Fin 512) : Max3S.nfAt A₀ B₀ j = rowsNfAt j := by
  simp only [Max3S.nfAt, Max3S.nfTab, rowsNfAt, rowsNfTab, Array.getElem_ofFn, eq_nf]

end Pinned

structure Ctx (k : K) : Prop where
  mul : ∀ P Q, pkMat (k.mul P Q) = pkMat P * pkMat Q
  lay : ∀ P Q, InLayout (k.mul P Q)
  one : pkMat k.ONE = 1
  layOne : InLayout k.ONE
  sa : pkMat k.SA = rowsMatrix rowsA
  sb : pkMat k.SB = rowsMatrix rowsB
  x : pkMat (k.R 13) = rowsMatrix rowsX
  y : pkMat (k.R 14) = rowsMatrix rowsY
  z : pkMat (k.R 16) = rowsMatrix rowsZ
  q : ∀ i : Fin 8, pkMat (k.R (17 + i.val)) = rowsMatrix (rowsQ i)
  nf : ∀ j : Fin 512, pkMat (k.R (25 + j.val)) = rowsMatrix (rowsNfAt j)

theorem ctx_of (D : CFSG.KC.Th.Gen.Max3Data) (h : CFSG.KC.Th.Gen.max3Chk D = true)
    (hA : seedA = String.ofList D.ThSeed_LA) (hB : seedB = String.ofList D.ThSeed_LB) :
    Ctx (kOf D) := by
  have hk := Max3S.consts_leaf h
  have hR := Max3S.regOK_of D h
  have hSA : pkMat D.ThSeed_SA = rowsMatrix (rowsOf (String.ofList D.ThSeed_LA)) :=
    (decOK_sound (Max3S.decA_leaf h)).2
  have hSB : pkMat D.ThSeed_SB = rowsMatrix (rowsOf (String.ofList D.ThSeed_LB)) :=
    (decOK_sound (Max3S.segPre_true h 2 (by rw [Max3S.segPre_length]; decide) :
      CFSG.KC.Th.SeedS.decOK D.ThSeed_SB D.ThSeed_LB = true)).2
  rw [← hA, ← hB] at hR
  rw [← hA] at hSA
  rw [← hB] at hSB
  refine ⟨fun P Q => pkMat_mulB hk P Q, fun P Q => inLayout_mulB hk P Q, pkMat_one hk,
    inLayout_one hk, hSA, hSB, ?_, ?_, ?_, fun i => ?_, fun j => ?_⟩
  · rw [← eq_x]; exact hR.x
  · rw [← eq_y]; exact hR.y
  · rw [← eq_z]; exact hR.z
  · rw [← eq_q]; exact hR.q i
  · rw [← eq_nfAt]; exact hR.nf j

variable {k : K}

theorem pk_reg (c : Ctx k) (r : Nat) : pkMat (k.reg r) = pkMat (k.R r) := by
  rw [K.reg, c.mul, c.one, one_mul]

theorem pk_pow (c : Ctx k) {P : Nat} {X : Array V4} (h : pkMat P = rowsMatrix X) :
    ∀ n, pkMat (k.pow P n) = rowsMatrix (powRows X n)
  | 0 => by rw [K.pow, c.one, rowsMatrix_powRows, pow_zero]
  | 1 => by rw [K.pow, h, rowsMatrix_powRows, pow_one]
  | n + 2 => by
    rw [K.pow, c.mul, pk_pow c h (n + 1), h, rowsMatrix_powRows, rowsMatrix_powRows]
    exact (pow_succ _ _).symm

theorem lay_pow (c : Ctx k) {P : Nat} (h : InLayout P) : ∀ n, InLayout (k.pow P n)
  | 0 => c.layOne
  | 1 => h
  | _ + 2 => c.lay _ _

theorem pk_foldr (c : Ctx k) (l : List Nat) :
    pkMat (l.foldr k.mul k.ONE) = (l.map pkMat).prod := by
  induction l with
  | nil => exact c.one
  | cons P l ih => rw [List.foldr_cons, c.mul, ih, List.map_cons, List.prod_cons]

theorem lay_foldr (c : Ctx k) (l : List Nat) : InLayout (l.foldr k.mul k.ONE) := by
  cases l with
  | nil => exact c.layOne
  | cons P l => exact c.lay _ _

theorem pk_sound (c : Ctx k) : ∀ e : TE, pkMat (e.pk k) = rowsMatrix e.rows
  | .one => c.one.trans rowsMatrix_idRows.symm
  | .a => by rw [TE.pk, c.mul, c.one, one_mul, c.sa]; rfl
  | .b => by rw [TE.pk, c.mul, c.one, one_mul, c.sb]; rfl
  | .x => by rw [TE.pk, pk_reg c, c.x]; rfl
  | .y => by rw [TE.pk, pk_reg c, c.y]; rfl
  | .z => by rw [TE.pk, pk_reg c, c.z]; rfl
  | .q i => by rw [TE.pk, pk_reg c, c.q]; rfl
  | .nf j => by rw [TE.pk, pk_reg c, c.nf]; rfl
  | .nfE s e => by
    have hz : pkMat (k.reg 16) = rowsMatrix rowsZ := by rw [pk_reg c, c.z]
    have hq : ∀ i : Fin 8, pkMat (k.reg (17 + i.val)) = rowsMatrix (rowsQ i) := fun i => by
      rw [pk_reg c, c.q]
    rw [TE.pk, TE.rows, rowsNf, rowsMatrix_mulRows, rowsMatrix_prodRows, c.mul, pk_pow c hz,
      pk_foldr c, List.map_ofFn, List.map_ofFn]
    congr 2
    exact congrArg List.ofFn (funext fun i => pk_pow c (hq i) (e i))
  | .word w => by
    rw [TE.pk, pk_foldr c, TE.rows, rowsMatrix_wordRows, List.map_map]
    congr 1
    refine List.map_congr_left fun g _ => ?_
    cases g
    · exact (pk_reg c 13).trans c.x
    · exact (pk_reg c 14).trans c.y
  | .ab w => by
    rw [TE.pk, pk_foldr c, TE.rows, AllConj.abRows, rowsMatrix_prodRows, List.map_map,
      List.map_map]
    congr 1
    refine List.map_congr_left fun l _ => ?_
    simp only [Function.comp_apply, AllConj.abLetterRows]
    split_ifs
    · rw [c.mul, c.one, one_mul, c.sa]
    · rw [c.mul, c.one, one_mul, c.sb]
  | .prodFn _ f => by
    rw [TE.pk, pk_foldr c, TE.rows, rowsMatrix_prodRows, List.map_ofFn, List.map_ofFn]
    exact congrArg (fun l => List.prod l) (congrArg List.ofFn (funext fun j => pk_sound c (f j)))
  | .mul e f => by rw [TE.pk, c.mul, pk_sound c e, pk_sound c f, TE.rows, rowsMatrix_mulRows]
  | .pow e n => pk_pow c (pk_sound c e) n

theorem lay_pk (c : Ctx k) : ∀ e : TE, InLayout (e.pk k)
  | .one => c.layOne
  | .a => c.lay _ _
  | .b => c.lay _ _
  | .x => c.lay _ _
  | .y => c.lay _ _
  | .z => c.lay _ _
  | .q _ => c.lay _ _
  | .nf _ => c.lay _ _
  | .nfE _ _ => c.lay _ _
  | .word _ => lay_foldr c _
  | .ab _ => lay_foldr c _
  | .prodFn _ _ => lay_foldr c _
  | .mul _ _ => c.lay _ _
  | .pow e n => lay_pow c (lay_pk c e) n

theorem wf_A : WfRows rowsA := wfRows_rowsOf _
theorem wf_B : WfRows rowsB := wfRows_rowsOf _

theorem wf_rows : ∀ e : TE, WfRows e.rows
  | .one => wfRows_idRows
  | .a => wf_A
  | .b => wf_B
  | .x => by rw [TE.rows, ← eq_x]; exact Max3S.wf_x wf_A wf_B
  | .y => by rw [TE.rows, ← eq_y]; exact Max3S.wf_y wf_A wf_B
  | .z => by rw [TE.rows, ← eq_z]; exact Max3S.wf_z wf_A wf_B
  | .q i => by rw [TE.rows, ← eq_q]; exact Max3S.wf_q wf_A wf_B i
  | .nf j => by rw [TE.rows, ← eq_nfAt]; exact Max3S.wf_nfAt wf_A wf_B j
  | .nfE s e => by rw [TE.rows, ← eq_nf]; exact Max3S.wf_nf wf_A wf_B s e
  | .word w => by
    rw [TE.rows]
    exact wfRows_wordRows (eq_x ▸ Max3S.wf_x wf_A wf_B) (eq_y ▸ Max3S.wf_y wf_A wf_B) w
  | .ab w => wfRows_prodRows fun X hX => by
    obtain ⟨l, -, rfl⟩ := List.mem_map.1 hX
    unfold AllConj.abLetterRows
    split_ifs
    · exact wf_A
    · exact wf_B
  | .prodFn _ f => by
    rw [TE.rows]
    refine wfRows_prodRows fun X hX => ?_
    obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hX
    exact wf_rows (f j)
  | .mul e f => by rw [TE.rows]; exact (wf_rows e).mulRows (wf_rows f)
  | .pow e n => by rw [TE.rows]; exact (wf_rows e).powRows n

theorem eqRows_eq_beq (c : Ctx k) (e f : TE) :
    Native.eqRows e.rows f.rows = Nat.beq (e.pk k) (f.pk k) := by
  cases h : Nat.beq (e.pk k) (f.pk k)
  · exact Max3S.eqRows_false_of_pk (lay_pk c e) (lay_pk c f) (pk_sound c e) (pk_sound c f)
      (Nat.ne_of_beq_eq_false h)
  · exact Max3S.eqRows_true_of_pk (wf_rows e) (wf_rows f) (pk_sound c e) (pk_sound c f)
      (Nat.eq_of_beq_eq_true h)

theorem eqRows_true_of (c : Ctx k) {e f : TE} (h : Nat.beq (e.pk k) (f.pk k) = true) :
    Native.eqRows e.rows f.rows = true :=
  (eqRows_eq_beq c e f).trans h

theorem eqRows_false_of (c : Ctx k) {e f : TE}
    (h : BigS.notB (Nat.beq (e.pk k) (f.pk k)) = true) : Native.eqRows e.rows f.rows = false := by
  rw [eqRows_eq_beq c]
  cases hb : Nat.beq (e.pk k) (f.pk k)
  · rfl
  · rw [hb] at h
    exact absurd h (by decide)

theorem beqB_eq {x b : Bool} (h : beqB x b = true) : x = b := by
  cases x <;> cases b <;> first | rfl | exact absurd h (by decide)

theorem facts_of (c : Ctx k) : ∀ L : List (TE × TE × Bool), pairsOK k L = true → TE.Facts L
  | [], _ => trivial
  | [t], h => by
    have h' := (Max3S.andB_eq_true h).1
    rw [TE.Facts, eqRows_eq_beq c]
    exact beqB_eq h'
  | t :: u :: l, h => by
    obtain ⟨h1, h2⟩ := Max3S.andB_eq_true h
    refine ⟨?_, facts_of c (u :: l) h2⟩
    rw [eqRows_eq_beq c]
    exact beqB_eq h1

end CFSG.KC.Th.Expr

end
