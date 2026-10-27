
module

public import CFSG.Certificates.Kernel.Th.Spec.SurjCheckBase

public import CFSG.Certificates.Kernel.Th.Spec.Gj

public section

namespace CFSG.KC.Th.Spec

open CFSG.KC.Th CFSG.KC.Th.BigS CFSG.KC.Th.SurjS CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.Bridge.Th

private theorem scInvRows {M : Array V4} (hM : WfRows M) {A B : ℕ} (hA : rowsMatrix M = pkMat A)
    (hAB : pkMat A * pkMat B = 1) :
    WfRows (invRows M) ∧ rowsMatrix (invRows M) = pkMat B := by
  have hY : rowsMatrix M * pkMat B = 1 := by rw [hA]; exact hAB
  obtain ⟨hs, hw, -, -⟩ := invRows_spec M hM.1 hM.2 ⟨pkMat B, hY⟩
  exact ⟨⟨hs, hw⟩, rowsMatrix_invRows_eq M hM.1 hM.2 hY⟩

private theorem scLetterRows {RB : ℕ → ℕ} {I : Array (Array V4)} (hsz : I.size = 8)
    (hmat : ∀ g < 8, WfRows (I[g]?.getD (idRows ())) ∧
      rowsMatrix (I[g]?.getD (idRows ())) = pkMat (RB (g + 1)))
    (hinv : ∀ g < 8, pkMat (RB (g + 1)) * pkMat (RB (g + 9)) = 1) {l : ℕ × Bool} (hl : l.1 < 8) :
    WfRows (letterRows I (I.map invRows) l) ∧
      rowsMatrix (letterRows I (I.map invRows) l) = regMat RB l := by
  have hg : l.1 < I.size := by omega
  have hget : I[l.1]? = some I[l.1] := Array.getElem?_eq_getElem hg
  obtain ⟨hw, hm⟩ := hmat l.1 hl
  rw [hget, Option.getD_some] at hw hm
  unfold letterRows regMat
  cases hb : l.2
  · simp only [Bool.false_eq_true, ↓reduceIte, Array.getElem?_map, hget, Option.map_some,
      Option.getD_some]
    exact scInvRows hw hm (hinv l.1 hl)
  · simp only [↓reduceIte, hget, Option.getD_some]
    exact ⟨hw, hm⟩

private theorem scWordRows {RB : ℕ → ℕ} {I : Array (Array V4)} (hsz : I.size = 8)
    (hmat : ∀ g < 8, WfRows (I[g]?.getD (idRows ())) ∧
      rowsMatrix (I[g]?.getD (idRows ())) = pkMat (RB (g + 1)))
    (hinv : ∀ g < 8, pkMat (RB (g + 1)) * pkMat (RB (g + 9)) = 1) :
    ∀ (w : List (ℕ × Bool)) (A : Array V4), (∀ l ∈ w, l.1 < 8) → WfRows A →
      WfRows (w.foldl (fun acc l => Native.mulRows acc (letterRows I (I.map invRows) l)) A) ∧
        rowsMatrix (w.foldl (fun acc l => Native.mulRows acc (letterRows I (I.map invRows) l)) A) =
          wordMatFrom RB (rowsMatrix A) w
  | [], A, _, hA => ⟨hA, rfl⟩
  | l :: w, A, hw, hA => by
    obtain ⟨h1, h2⟩ := scLetterRows hsz hmat hinv (hw l (by simp))
    have hA' : WfRows (Native.mulRows A (letterRows I (I.map invRows) l)) := wfRows_mulRows hA h1
    obtain ⟨h3, h4⟩ := scWordRows hsz hmat hinv w _ (fun m hm => hw m (by simp [hm])) hA'
    refine ⟨h3, ?_⟩
    rw [List.foldl_cons, h4, rowsMatrix_mulRows, h2]
    simp only [wordMatFrom, List.foldl_cons]

theorem thCheck_of_spec {RB : ℕ → ℕ} {rels : List (List (ℕ × Bool))} (hsz : imgMats.size = 8)
    (hmat : ∀ g < 8, WfRows (imgMats[g]?.getD (idRows ())) ∧
      rowsMatrix (imgMats[g]?.getD (idRows ())) = pkMat (RB (g + 1)))
    (hinv : ∀ g < 8, pkMat (RB (g + 1)) * pkMat (RB (g + 9)) = 1)
    (hrels : ∀ r ∈ rels, (∀ l ∈ r, l.1 < 8) ∧ wordMat RB r = 1)
    {w0 w1 : List (ℕ × Bool)} (hstd : stdWords = [w0, w1])
    (hw0 : ∀ l ∈ w0, l.1 < 8) (hw1 : ∀ l ∈ w1, l.1 < 8)
    (hs0 : wordMat RB w0 = rowsMatrix (rowsOf seedA))
    (hs1 : wordMat RB w1 = rowsMatrix (rowsOf seedB)) : thCheck rels = true := by
  have hone : ∀ w : List (ℕ × Bool), (∀ l ∈ w, l.1 < 8) →
      WfRows (wordRows imgMats (imgMats.map invRows) w) ∧
        rowsMatrix (wordRows imgMats (imgMats.map invRows) w) = wordMat RB w := by
    intro w hw
    have h := scWordRows hsz hmat hinv w (idRows ()) hw wfRows_idRows
    rw [rowsMatrix_idRows] at h
    exact h
  have hinvs : invsOK imgMats (imgMats.map invRows) = true := by
    unfold invsOK
    rw [Bool.and_eq_true, beq_iff_eq, List.all_eq_true]
    refine ⟨by simp, fun k hk => ?_⟩
    have hk' : k < 8 := by rw [List.mem_range] at hk; omega
    have hg : k < imgMats.size := by omega
    have hget : imgMats[k]? = some imgMats[k] := Array.getElem?_eq_getElem hg
    obtain ⟨hw, hm⟩ := hmat k hk'
    rw [hget, Option.getD_some] at hw hm
    obtain ⟨hw', hm'⟩ := scInvRows hw hm (hinv k hk')
    simp only [Array.getElem?_map, hget, Option.map_some, Option.getD_some]
    refine eqRows_of_rowsMatrix_eq (wfRows_mulRows hw hw') wfRows_idRows ?_
    rw [rowsMatrix_mulRows, hm, hm', rowsMatrix_idRows]
    exact hinv k hk'
  have hrelsAll : rels.all (fun r => eqRows (wordRows imgMats (imgMats.map invRows) r) idRows) =
      true := by
    rw [List.all_eq_true]
    intro r hr
    obtain ⟨hl, h1⟩ := hrels r hr
    obtain ⟨hwf, hm⟩ := hone r hl
    exact eqRows_of_rowsMatrix_eq hwf wfRows_idRows (by rw [hm, h1, rowsMatrix_idRows])
  have hstd0 : eqRows (wordRows imgMats (imgMats.map invRows) (stdWords[0]?.getD []))
      (rowsOf seedA) = true := by
    have e0 : stdWords[0]?.getD [] = w0 := by rw [hstd]; rfl
    rw [e0]
    obtain ⟨hwf, hm⟩ := hone w0 hw0
    exact eqRows_of_rowsMatrix_eq hwf (wfRows_rowsOf _) (by rw [hm, hs0])
  have hstd1 : eqRows (wordRows imgMats (imgMats.map invRows) (stdWords[1]?.getD []))
      (rowsOf seedB) = true := by
    have e1 : stdWords[1]?.getD [] = w1 := by rw [hstd]; rfl
    rw [e1]
    obtain ⟨hwf, hm⟩ := hone w1 hw1
    exact eqRows_of_rowsMatrix_eq hwf (wfRows_rowsOf _) (by rw [hm, hs1])
  unfold thCheck inverseChecks imageChecks
  simp only [Bool.and_eq_true, beq_iff_eq]
  exact ⟨⟨⟨⟨hsz, hinvs⟩, hrelsAll⟩, hstd0⟩, hstd1⟩

end CFSG.KC.Th.Spec

end
