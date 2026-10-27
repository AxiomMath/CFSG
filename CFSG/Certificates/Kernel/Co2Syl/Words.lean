module

public import CFSG.RankThree.Co2.SylFacts
public import CFSG.Certificates.Kernel.Co2Syl.Sound
public import CFSG.Certificates.CosetTableShort
public import CFSG.GroupTheory.LocalCores.Fitting

public section

namespace CFSG.KC.Co2Syl

open CFSG.KC.TabMatGrp CFSG.KC.Co2InvS CFSG.RankThree.Co2

local notation "M22" => Matrix (Fin 22) (Fin 22) (ZMod 2)

@[expose] def bitZ (x j : ℕ) : ZMod 2 := if x.testBit j then 1 else 0

theorem bitZ_xor (x y j : ℕ) : bitZ (x ^^^ y) j = bitZ x j + bitZ y j := by
  unfold bitZ
  rw [Nat.testBit_xor]
  cases x.testBit j <;> cases y.testBit j <;> decide

theorem actGo_bitZ (rows : Array ℕ) (v j : ℕ) : ∀ m acc,
    bitZ (CFSG.Monster.VisCert.Native.actGo rows v m acc) j =
      bitZ acc j + ∑ i ∈ Finset.range m, bitZ v i * bitZ rows[i]! j
  | 0, acc => by simp [CFSG.Monster.VisCert.Native.actGo]
  | m + 1, acc => by
    rw [CFSG.Monster.VisCert.Native.actGo, actGo_bitZ rows v j m, Finset.sum_range_succ]
    by_cases h : v.testBit m
    · rw [if_pos h, bitZ_xor]
      simp only [bitZ, h, if_true, one_mul]
      abel
    · rw [if_neg h]
      simp only [bitZ, h]
      simp

theorem rowsMat_apply (R : Array ℕ) (t j : Fin 22) : rowsMat R t j = bitZ R[t.val]! j.val := rfl

theorem rowsMat_rowsMul (A B : Array ℕ) :
    rowsMat (CFSG.Monster.B.TwoA.Co2Inv.rowsMul A B) = rowsMat A * rowsMat B := by
  ext t k
  rw [rowsMat_apply, CFSG.Monster.B.TwoA.Co2Inv.rowsMul_getElem _ _ t.isLt,
    CFSG.Monster.B.Co2.Native.actD, actGo_bitZ, Matrix.mul_apply, bitZ, Nat.zero_testBit, if_neg
    Bool.false_ne_true, zero_add, ← Fin.sum_univ_eq_sum_range (fun i => bitZ A[t.val]! i *
      bitZ B[i]! k.val)]
  rfl

theorem rowsMat_idRows : rowsMat CFSG.Monster.B.TwoA.Co2Inv.idRows = 1 := by
  ext t j
  rw [rowsMat_apply, CFSG.Monster.B.TwoA.Co2Inv.idRows, getElem!_pos _ _ (by simp), Matrix.one_apply]
  simp only [List.getElem_toArray, List.getElem_map, List.getElem_range, bitZ, Nat.one_shiftLeft,
    Nat.testBit_two_pow]
  by_cases h : t = j
  · subst h
    simp
  · have h' : t.val ≠ j.val := fun e => h (Fin.ext e)
    simp [h, h']

theorem rowsMat_foldl : ∀ (w : List ℕ) (A : Array ℕ),
    rowsMat (w.foldl (fun A j => CFSG.Monster.B.TwoA.Co2Inv.rowsMul A (letterRows j)) A) =
      rowsMat A * (w.map fun l => rowsMat (letterRows l)).prod
  | [], A => by simp
  | l :: w, A => by
    rw [List.foldl_cons, rowsMat_foldl w, rowsMat_rowsMul, List.map_cons, List.prod_cons, mul_assoc]

theorem wordMat_eq_prod (w : List ℕ) : wordMat w = (w.map fun l => rowsMat (letterRows l)).prod := by
  rw [wordMat, wordRows, rowsMat_foldl, rowsMat_idRows, one_mul]

theorem rowsMat_eq_MatP {R : Array ℕ} {U : ℕ} (h : ∀ t < 22, R[t]! = U / 2 ^ (22 * t) % 2 ^ 22) :
    rowsMat R = MatP 22 U := by
  ext t j
  rw [rowsMat_apply, MatP_apply, h t t.isLt, bitZ, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow,
    decide_eq_true j.isLt, Bool.true_and, Nat.add_comm, Nat.mul_comm]

@[expose] noncomputable def foldR (f : ℕ → ℕ) (w : List ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ) IDP (fun l _ acc => mulV (f l) acc) w

theorem MatP_foldR (f : ℕ → ℕ) : ∀ w : List ℕ,
    MatP 22 (foldR f w) = (w.map fun l => MatP 22 (f l)).prod
  | [] => MatP_IDP
  | l :: w => by
    change MatP 22 (mulV (f l) (foldR f w)) = _
    rw [MatP_mulV, MatP_foldR f w, List.map_cons, List.prod_cons]

theorem MatP_foldR_eq {f : ℕ → ℕ} {w : List ℕ}
    (h : ∀ l ∈ w, MatP 22 (f l) = rowsMat (letterRows l)) : MatP 22 (foldR f w) = wordMat w := by
  rw [MatP_foldR, wordMat_eq_prod, List.map_congr_left h]

theorem genMon_eq_matGrp {G : ℕ → ℕ} {ws : Array (List ℕ)}
    (h1 : ∀ j < 5, ∃ k < ws.size, MatP 22 (G j) = wordMat ws[k]!)
    (h2 : ∀ k < ws.size, ∃ j < 5, MatP 22 (G j) = wordMat ws[k]!) : genMon G = matGrp ws := by
  unfold genMon matGrp
  congr 1
  ext x
  constructor
  · rintro ⟨⟨j, hj⟩, rfl⟩
    obtain ⟨k, hk, e⟩ := h1 j hj
    refine ⟨⟨k, hk⟩, ?_⟩
    change wordMat ws[k] = MatP 22 (G j)
    rw [e, getElem!_pos ws k hk]
  · rintro ⟨⟨k, hk⟩, rfl⟩
    obtain ⟨j, hj, e⟩ := h2 k hk
    refine ⟨⟨j, hj⟩, ?_⟩
    change MatP 22 (G j) = wordMat ws[k]
    rw [e, getElem!_pos ws k hk]

theorem comm_genMon {G : ℕ → ℕ} {Y : M22} (h : ∀ j < 5, MatP 22 (G j) * Y = Y * MatP 22 (G j)) :
    ∀ x ∈ genMon G, x * Y = Y * x := by
  intro x hx
  unfold genMon at hx
  induction hx using Submonoid.closure_induction with
  | mem y hy =>
    obtain ⟨⟨j, hj⟩, rfl⟩ := hy
    exact h j hj
  | one => rw [one_mul, mul_one]
  | mul y z _ _ hy hz => rw [mul_assoc, hz, ← mul_assoc, hy, mul_assoc]

variable {CF G : ℕ → ℕ} {N : ℕ} {ws : Array (List ℕ)}

theorem sylGrp_of {B Bi : ℕ} {cls : List ℕ} {Rp : ℕ → ℕ} (hR : TreeRecs CF G N)
    (hG : genMon G = matGrp ws) (hut : utK B Bi G = true)
    (hrep : ∀ j ∈ cls, repMat j = MatP 22 (Rp j))
    (hmem : ∀ j ∈ cls, ∃ k, memK CF N (Rp j) k = true)
    (hcomm : ∀ j ∈ cls, ∀ g < 5, commK (G g) (Rp j) = true) : SylGrp ws N cls := by
  refine ⟨?_, ?_, fun j hj => ?_, fun j hj => ?_⟩ <;> rw [← hG]
  · exact utK_sound hut
  · exact tree_card hR
  · obtain ⟨k, hk⟩ := hmem j hj
    rw [hrep j hj]
    exact memK_sound hR hk
  · rw [hrep j hj]
    exact comm_genMon fun g hg => commK_sound (hcomm j hj g hg)

theorem sqCounts_of {A B : ℕ} {CNT : ℕ → ℕ} {hi i : ℕ} (hR : TreeRecs CF G N)
    (hG : genMon G = matGrp ws) (hA : A < 2 ^ 484) (hB : B < 2 ^ 484)
    (hrA : repMat i = MatP 22 A) (hrB : repMat 0 = MatP 22 B) (hN : N ≤ 4096 * hi)
    (h : ∀ b < 64 * hi, blkT CF G A B CNT N b = true) :
    SqCount ws N i (cntTotal CNT 0 hi) ∧ SqCount ws N 0 (cntTotal CNT 1 hi) := by
  unfold SqCount
  rw [← hG, hrA, hrB]
  exact ⟨fun hc => (sq_count hR hc hA hB hN h).1, fun hc => (sq_count hR hc hA hB hN h).2⟩

theorem conjMul_of {R a b : ℕ} (hR : TreeRecs CF G N) (hG : genMon G = matGrp ws)
    (hr : repMat 0 = MatP 22 R) (h : witK CF R N a b = true) : ConjMul ws (repMat 0) := by
  unfold ConjMul
  rw [← hG, hr]
  exact witK_sound hR h

theorem not_conjMul_of {B Bi R i : ℕ} {LD : ℕ → ℕ} (hR : TreeRecs CF G N)
    (hG : genMon G = matGrp ws) (hut : utK B Bi G = true) (hr : repMat i = MatP 22 R)
    (hL : ∀ k < N, labK CF G LD R N k = true) :
    Nat.card (matGrp ws) ≤ N → ¬ ConjMul ws (repMat i) := by
  unfold ConjMul
  rw [← hG, hr]
  exact fun hc => lab_sound hR hc (utK_sound hut) hL

end CFSG.KC.Co2Syl

end
