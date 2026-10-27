
module

public import CFSG.Certificates.Kernel.Th.Spec.TsLeaves
public import CFSG.Certificates.Kernel.Th.Spec.MirrorBase
public import CFSG.Certificates.Kernel.Th.Spec.Vec

@[expose] public section

namespace CFSG.KC.Th.Spec

open CFSG.KC.Th CFSG.KC.Th.Gen CFSG.KC.Th.BigS CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.Th.Max3 CFSG.Sporadic.ThSchreier CFSG.KC.Th.Spec.Mir

theorem getD_map_range {f : ℕ → ℕ} {n i : ℕ} (hi : i < n) :
    ((List.range n).map f).getD i 0 = f i := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range, hi]

theorem getElem!_toArray_map_range {f : ℕ → ℕ} {n i : ℕ} (hi : i < n) :
    (((List.range n).map f).toArray)[i]! = f i := by
  simp [hi]

theorem blt_true {a b : ℕ} (h : Nat.blt a b = true) : a < b := Nat.blt_eq.mp h

theorem permOK_spec {ROWS PX PY : ℕ → ℕ} {rm LX LY2 n i : ℕ}
    (h : TsS.permOK ROWS PX PY rm LX LY2 n i = true) :
    PX i < n ∧ PY i < n ∧ vecB rm (ROWS i) LX = ROWS (PX i) ∧
      vecB rm (ROWS i) LY2 = ROWS (PY i) := by
  unfold TsS.permOK at h
  have h1 := andB_left h
  have h2 := andB_left (andB_right h)
  have h3 := andB_left (andB_right (andB_right h))
  have h4 := andB_right (andB_right (andB_right h))
  exact ⟨blt_true h1, blt_true h2, Nat.eq_of_beq_eq_true h3, Nat.eq_of_beq_eq_true h4⟩

theorem invOK_spec {TP INV : ℕ → ℕ} {n i : ℕ} (h : TsS.invOK TP INV n i = true) :
    INV i < n ∧ TP (INV i) = i := by
  unfold TsS.invOK at h
  exact ⟨blt_true (andB_left h), Nat.eq_of_beq_eq_true (andB_right h)⟩

theorem treeOK_spec {TP TPar TLab PX PY : ℕ → ℕ} {n k : ℕ}
    (h : TsS.treeOK TP TPar TLab PX PY n k = true) :
    TP k < n ∧ (k = 0 ∨ (TPar k < k ∧ ((TLab k = 1 ∧ PX (TP (TPar k)) = TP k) ∨
      (TLab k = 2 ∧ PY (TP (TPar k)) = TP k)))) := by
  unfold TsS.treeOK at h
  refine ⟨blt_true (andB_left h), ?_⟩
  have h2 := andB_right h
  by_cases hk : k = 0
  · exact Or.inl hk
  · right
    have e : Nat.beq k 0 = false := Bool.eq_false_iff.2 fun h' => hk (Nat.eq_of_beq_eq_true h')
    rw [e] at h2
    have h3 := andB_left h2
    have h4 := andB_right h2
    refine ⟨blt_true h3, ?_⟩
    unfold orB at h4
    cases hx : andB (Nat.beq (TLab k) 1) (Nat.beq (PX (TP (TPar k))) (TP k))
    · rw [hx] at h4
      right
      exact ⟨Nat.eq_of_beq_eq_true (andB_left h4), Nat.eq_of_beq_eq_true (andB_right h4)⟩
    · left
      exact ⟨Nat.eq_of_beq_eq_true (andB_left hx), Nat.eq_of_beq_eq_true (andB_right hx)⟩

theorem keyNat_wKeyRow : keyNat wKeyRow = canon2
    327208660843949311569856638931134950366718123578765707520623978699011294545
    53118203310247861616881865655955129280624587562044029180903589568007838922 := by
  unfold wKeyRow
  rw [keyNat_canon, v4OfNat_toNat_of_lt (by norm_num), v4OfNat_toNat_of_lt (by norm_num)]

section Consts

variable {c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE : ℕ}
  (K : constsOK c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE = true)

include K in
theorem imageKey_wKeyRow {X : Array V4} (hX : WfRows X) {M : ℕ} (hM : rowsMatrix X = pkMat M)
    (h : canon2 (vecB rm (Nat.land (canon2
        327208660843949311569856638931134950366718123578765707520623978699011294545
        53118203310247861616881865655955129280624587562044029180903589568007838922)
        115792089237316195423570985008687907853269984665640564039457584007913129639935) M)
      (vecB rm (Nat.shiftRight (canon2
        327208660843949311569856638931134950366718123578765707520623978699011294545
        53118203310247861616881865655955129280624587562044029180903589568007838922) 256) M) =
      canon2 327208660843949311569856638931134950366718123578765707520623978699011294545
        53118203310247861616881865655955129280624587562044029180903589568007838922) :
    imageKey (frTable X) wKeyRow = wKeyRow := by
  refine imageKey_eq_self K hX hM wKeyRow ?_
  rw [keyNat_wKeyRow, show (2 ^ 256 - 1 : ℕ) =
    115792089237316195423570985008687907853269984665640564039457584007913129639935 by norm_num]
  exact h

end Consts

section Ts

variable {D : TsData} (L : TsLeaves D) {RA RB : Array V4} (hA : WfRows RA) (hB : WfRows RB)
  (hSA : pkMat D.ThSeed_SA = rowsMatrix RA) (hSB : pkMat D.ThSeed_SB = rowsMatrix RB)

end Ts

end CFSG.KC.Th.Spec

end
