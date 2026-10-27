module

public import Certificates.Data.Kernel.GHarrisFus.Defs
public import Certificates.Data.Kernel.GHarrisFus.GoodDefs
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisFusSound
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisFusDataA

public section

open CFSG.ComponentClassification.GHarris.SCert CFSG.KC.Enum

namespace CFSG.KC.GHFus.Good

theorem strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

theorem strictN_eq (y : Nat) (k : Nat → Nat) : strictN y k = k y := by cases y <;> rfl

theorem and'_eq (a b : Bool) : Bool.and' a b = (a && b) := by cases a <;> cases b <;> rfl

theorem or'_eq (a b : Bool) : Bool.or' a b = (a || b) := by cases a <;> cases b <;> rfl

theorem recOr_any (P : Nat → Bool) (l : List Nat) :
    List.rec (motive := fun _ => Bool) false (fun s _ ih => P s || ih) l = l.any P := by
  induction l with
  | nil => rfl
  | cons s l ih => rw [List.any_cons, ← ih]

theorem enc_inj {a b : SE} (h : a.enc = b.enc) : a = b := by
  rw [← SE.dec_enc a, ← SE.dec_enc b, h]

variable {dm mv CT Q : Nat} {q : Array SE}

theorem evalFrom_cons (acc i : Nat) (w : List Nat) :
    evalFrom dm mv Q acc (i :: w) =
      evalFrom dm mv Q (mulK dm mv acc (Nat.land (Nat.shiftRight Q i) 511)) w := by
  unfold evalFrom
  exact strictN_eq _ _

theorem evalFrom_enc (hmul : ∀ a b : SE, mulK dm mv a.enc b.enc = (a * b).enc)
    (hQ : ∀ i < 4, Nat.land (Nat.shiftRight Q (9 * i)) 511 = (q.getD i 1).enc)
    (w : List Nat) (hw : ∀ i ∈ w, i < 4) (acc : SE) :
    evalFrom dm mv Q acc.enc (w.map (9 * ·)) = (w.foldl (fun a i => a * q.getD i 1) acc).enc := by
  induction w generalizing acc with
  | nil => rfl
  | cons i w ih =>
    simp only [List.map_cons, List.foldl_cons]
    rw [evalFrom_cons, hQ i (hw i (by simp)), hmul]
    exact ih (fun j hj => hw j (by simp [hj])) _

theorem evalWK_enc (hmul : ∀ a b : SE, mulK dm mv a.enc b.enc = (a * b).enc)
    (hQ : ∀ i < 4, Nat.land (Nat.shiftRight Q (9 * i)) 511 = (q.getD i 1).enc)
    (w : List Nat) (hw : ∀ i ∈ w, i < 4) :
    evalWK dm mv Q (w.map (9 * ·)) = (Fus.evalW (· * ·) q w).enc :=
  evalFrom_enc hmul hQ w hw 1

theorem mul_eq_of (hmul : ∀ a b : SE, mulK dm mv a.enc b.enc = (a * b).enc) {a b c d : SE}
    (h : Nat.beq (mulK dm mv a.enc b.enc) (mulK dm mv c.enc d.enc) = true) : a * b = c * d := by
  have e := Nat.eq_of_beq_eq_true h
  rw [hmul, hmul] at e
  exact enc_inj e

theorem hasEdgeK_true {i9 j : Nat} {IK : List (Nat × List Nat)}
    (h : hasEdgeK dm mv CT Q i9 j IK = true) :
    ∃ r ∈ IK, r.1 = i9 ∧ clsK CT (evalWK dm mv Q r.2) = j := by
  induction IK with
  | nil => exact absurd h Bool.false_ne_true
  | cons r IK ih =>
    obtain ⟨c9, w⟩ := r
    have e : hasEdgeK dm mv CT Q i9 j ((c9, w) :: IK) =
        (Bool.and' (Nat.beq c9 i9) (Nat.beq (clsK CT (evalWK dm mv Q w)) j) ||
          hasEdgeK dm mv CT Q i9 j IK) := or'_eq _ _
    rw [e, Bool.or_eq_true, and'_eq, Bool.and_eq_true] at h
    rcases h with ⟨h1, h2⟩ | h
    · exact ⟨(c9, w), by simp, Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2⟩
    · obtain ⟨r', hr', h'⟩ := ih h
      exact ⟨r', List.mem_cons_of_mem _ hr', h'⟩

theorem hasEdge_of (hmul : ∀ a b : SE, mulK dm mv a.enc b.enc = (a * b).enc)
    (hcls : ∀ s : SE, clsK CT s.enc = SE.clsTab s)
    (hQ : ∀ i < 4, Nat.land (Nat.shiftRight Q (9 * i)) 511 = (q.getD i 1).enc) {A : Fus.Data}
    {IK : List (Nat × List Nat)} (hIK : ikB A IK = true)
    (hw : ∀ k < 32, ∀ i ∈ A.words.getD k [], i < 4) (i j : Nat)
    (h : hasEdgeK dm mv CT Q (9 * i) j IK = true) : A.hasEdge (· * ·) q i j = true := by
  obtain ⟨r, hr, h1, h2⟩ := hasEdgeK_true h
  unfold ikB at hIK
  rw [List.all_eq_true] at hIK
  obtain ⟨k, hk, hk'⟩ := List.any_eq_true.mp (hIK r hr)
  rw [Bool.and_eq_true, beq_iff_eq] at hk'
  obtain ⟨rfl, hinv⟩ := hk'
  have hk32 := List.mem_range.mp hk
  dsimp only at h1 h2
  rw [evalWK_enc hmul hQ _ (hw k hk32), hcls] at h2
  unfold Fus.Data.hasEdge
  rw [List.any_eq_true]
  refine ⟨k, hk, ?_⟩
  simp only [Bool.and_eq_true, beq_iff_eq]
  exact ⟨⟨hinv, by omega⟩, h2⟩

theorem goodFixZ_of (hmul : ∀ a b : SE, mulK dm mv a.enc b.enc = (a * b).enc)
    (hQ : ∀ i < 4, Nat.land (Nat.shiftRight Q (9 * i)) 511 = (q.getD i 1).enc)
    (h : goodFixZK dm mv Q = true) : (Fus.evalW (· * ·) q [1, 2, 1, 2] == SE.gen 0) = true := by
  have e : evalWK dm mv Q [9, 18, 9, 18] = _ := evalWK_enc hmul hQ [1, 2, 1, 2] (by decide)
  have h' : evalWK dm mv Q [9, 18, 9, 18] = 32 := Nat.eq_of_beq_eq_true h
  have c : (SE.gen 0).enc = 32 := by decide
  rw [e, ← c] at h'
  exact beq_iff_eq.mpr (enc_inj h')

theorem goodClsT_of (hmul : ∀ a b : SE, mulK dm mv a.enc b.enc = (a * b).enc)
    (hcls : ∀ s : SE, clsK CT s.enc = SE.clsTab s)
    (hQ : ∀ i < 4, Nat.land (Nat.shiftRight Q (9 * i)) 511 = (q.getD i 1).enc)
    (h : goodClsTK dm mv CT Q = true) :
    (SE.clsTab (Fus.evalW (· * ·) q [1, 2, 1, 2]) == 1) = true := by
  have e : evalWK dm mv Q [9, 18, 9, 18] = _ := evalWK_enc hmul hQ [1, 2, 1, 2] (by decide)
  have h' : clsK CT (evalWK dm mv Q [9, 18, 9, 18]) = 1 := Nat.eq_of_beq_eq_true h
  rw [e, hcls] at h'
  exact beq_iff_eq.mpr h'

theorem img_enc (hmul : ∀ a b : SE, mulK dm mv a.enc b.enc = (a * b).enc)
    (hQ : ∀ i < 4, Nat.land (Nat.shiftRight Q (9 * i)) 511 = (q.getD i 1).enc) {A : Fus.Data}
    (hw : ∀ k < 32, ∀ i ∈ A.words.getD k [], i < 4) {k : Nat} (hk : k < 32) {w : List Nat}
    (e : w = (A.words.getD k []).map (9 * ·)) : evalWK dm mv Q w = (A.img (· * ·) q k).enc := by
  rw [e]
  exact evalWK_enc hmul hQ _ (hw k hk)

theorem wordsB_three {A : Fus.Data} {k₁ k₂ k₃ : Nat} {w₁ w₂ w₃ : List Nat}
    (h : wordsB A [k₁, k₂, k₃] [w₁, w₂, w₃] = true) :
    w₁ = (A.words.getD k₁ []).map (9 * ·) ∧ w₂ = (A.words.getD k₂ []).map (9 * ·) ∧
      w₃ = (A.words.getD k₃ []).map (9 * ·) := by
  unfold wordsB at h
  have h' := beq_iff_eq.mp h
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at h'
  exact h'

theorem wordsB_four {A : Fus.Data} {k₁ k₂ k₃ k₄ : Nat} {w₁ w₂ w₃ w₄ : List Nat}
    (h : wordsB A [k₁, k₂, k₃, k₄] [w₁, w₂, w₃, w₄] = true) :
    w₁ = (A.words.getD k₁ []).map (9 * ·) ∧ w₂ = (A.words.getD k₂ []).map (9 * ·) ∧
      w₃ = (A.words.getD k₃ []).map (9 * ·) ∧ w₄ = (A.words.getD k₄ []).map (9 * ·) := by
  unfold wordsB at h
  have h' := beq_iff_eq.mp h
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at h'
  exact h'

theorem codesB_mem {cs : List Nat} (h : codesB cs = true) {c : Nat} (hc : c ∈ cs) :
    (SE.dec c).enc = c := by
  unfold codesB at h
  exact beq_iff_eq.mp (List.all_eq_true.mp h c hc)

theorem goodAZ_of (hmul : ∀ a b : SE, mulK dm mv a.enc b.enc = (a * b).enc)
    (hcls : ∀ s : SE, clsK CT s.enc = SE.clsTab s)
    (hQ : ∀ i < 4, Nat.land (Nat.shiftRight Q (9 * i)) 511 = (q.getD i 1).enc)
    {IK : List (Nat × List Nat)} {w26 w4 w2 wit : List Nat}
    (hIK : ikB Fus.aZBase IK = true) (hw : ∀ k < 32, ∀ i ∈ Fus.aZBase.words.getD k [], i < 4)
    (hx : wordsB Fus.aZBase [26, 4, 2] [w26, w4, w2] = true) (hwit : codesB wit = true)
    (h : goodAZK dm mv CT IK (w26, w4, w2) wit Q = true) : Fus.goodAZ (· * ·) q = true := by
  obtain ⟨e26, e4, e2⟩ := wordsB_three hx
  have ea := img_enc hmul hQ hw (by norm_num) e26
  have eb := img_enc hmul hQ hw (by norm_num) e4
  have ec := img_enc hmul hQ hw (by norm_num) e2
  unfold goodAZK at h
  simp only [and'_eq, or'_eq, strictB_eq, recOr_any, Bool.and_eq_true, Bool.or_eq_true,
    List.any_eq_true] at h
  obtain ⟨h1, h2, h3, s, hs, hs1, hs2⟩ := h
  have es := codesB_mem hwit hs
  have c8 : (SE.invRep 1).enc = 8 := by decide
  have c68 : (SE.gen 6).enc = 68 := by decide
  have c100 : (SE.gen 6 * SE.gen 0).enc = 100 := by decide
  have k1 : Fus.aZBase.img (· * ·) q 26 * SE.dec s = SE.dec s * SE.invRep 1 := by
    refine mul_eq_of hmul ?_
    rw [← ea, es, c8]
    exact hs1
  have k2 : Fus.aZBase.img (· * ·) q 4 * SE.dec s = SE.dec s * SE.gen 6 ∨
      Fus.aZBase.img (· * ·) q 4 * Fus.aZBase.img (· * ·) q 2 * SE.dec s =
        SE.dec s * (SE.gen 6 * SE.gen 0) := by
    rcases hs2 with hs2 | hs2
    · refine Or.inl (mul_eq_of hmul ?_)
      rw [← eb, es, c68]
      exact hs2
    · refine Or.inr (mul_eq_of hmul ?_)
      rw [← hmul (Fus.aZBase.img (· * ·) q 4) (Fus.aZBase.img (· * ·) q 2), ← eb, ← ec, es, c100]
      exact hs2
  unfold Fus.goodAZ
  simp only [Bool.and_eq_true, Bool.or_eq_true, List.any_eq_true, beq_iff_eq, and_assoc]
  exact ⟨hasEdge_of hmul hcls hQ hIK hw 1 7 h1, hasEdge_of hmul hcls hQ hIK hw 7 3 h2,
    hasEdge_of hmul hcls hQ hIK hw 5 8 h3, SE.dec s, SE.mem_allList _, k1, k2⟩

theorem goodA34_of (hmul : ∀ a b : SE, mulK dm mv a.enc b.enc = (a * b).enc)
    (hcls : ∀ s : SE, clsK CT s.enc = SE.clsTab s)
    (hQ : ∀ i < 4, Nat.land (Nat.shiftRight Q (9 * i)) 511 = (q.getD i 1).enc)
    {IK : List (Nat × List Nat)} {w26 w2 w3 w4 wit : List Nat}
    (hIK : ikB Fus.aA34Base IK = true)
    (hw : ∀ k < 32, ∀ i ∈ Fus.aA34Base.words.getD k [], i < 4)
    (hx : wordsB Fus.aA34Base [26, 2, 3, 4] [w26, w2, w3, w4] = true) (hwit : codesB wit = true)
    (ha1 : (Fus.A1list.map SE.enc == a1K) = true)
    (h : goodA34K dm mv CT IK (w26, w2, w3, w4) wit Q = true) : Fus.goodA34 (· * ·) q = true := by
  obtain ⟨e26, e2, e3, e4⟩ := wordsB_four hx
  have ea := img_enc hmul hQ hw (by norm_num) e26
  have eb := img_enc hmul hQ hw (by norm_num) e2
  have ec := img_enc hmul hQ hw (by norm_num) e3
  have ed := img_enc hmul hQ hw (by norm_num) e4
  have ha1' := (beq_iff_eq.mp ha1).symm
  unfold goodA34K at h
  simp only [and'_eq, or'_eq, strictB_eq, recOr_any, Bool.and_eq_true, Bool.or_eq_true,
    List.any_eq_true] at h
  obtain ⟨h1, h2, h3, s, hs, hs1, hs2, hs3, w, hw', hs4⟩ := h
  have es := codesB_mem hwit hs
  have c64 : (SE.invRep 3).enc = 64 := by decide
  have c32 : (SE.gen 0).enc = 32 := by decide
  have c8 : (SE.invRep 1).enc = 8 := by decide
  have c40 : (SE.invRep 1 * SE.gen 0).enc = 40 := by decide
  rw [ha1', List.mem_map] at hw'
  obtain ⟨w', hw'', rfl⟩ := hw'
  have k1 : SE.dec s * SE.invRep 3 = SE.invRep 3 * SE.dec s := by
    refine mul_eq_of hmul ?_
    rw [es, c64]
    exact hs1
  have k2 : Fus.aA34Base.img (· * ·) q 26 * SE.dec s = SE.dec s * SE.gen 0 := by
    refine mul_eq_of hmul ?_
    rw [← ea, es, c32]
    exact hs2
  have k3 : Fus.aA34Base.img (· * ·) q 2 * SE.dec s = SE.dec s * SE.invRep 1 ∨
      Fus.aA34Base.img (· * ·) q 2 * SE.dec s = SE.dec s * (SE.invRep 1 * SE.gen 0) := by
    rcases hs3 with hs3 | hs3
    · refine Or.inl (mul_eq_of hmul ?_)
      rw [← eb, es, c8]
      exact hs3
    · refine Or.inr (mul_eq_of hmul ?_)
      rw [← eb, es, c40]
      exact hs3
  have k4 : Fus.aA34Base.img (· * ·) q 3 * SE.dec s = SE.dec s * w' := by
    refine mul_eq_of hmul ?_
    rw [← ec, es]
    exact hs4
  have k5 : SE.clsTab (Fus.aA34Base.img (· * ·) q 4) = 8 := by
    rw [← hcls, ← ed]
    exact Nat.eq_of_beq_eq_true h3
  unfold Fus.goodA34
  simp only [Bool.and_eq_true, Bool.or_eq_true, List.any_eq_true, beq_iff_eq, and_assoc]
  exact ⟨h1.imp (hasEdge_of hmul hcls hQ hIK hw 1 0) (hasEdge_of hmul hcls hQ hIK hw 0 1),
    h2.imp (hasEdge_of hmul hcls hQ hIK hw 5 8) (hasEdge_of hmul hcls hQ hIK hw 8 5), k5,
    SE.dec s, SE.mem_allList _, k1, k2, k3, w', hw'', k4⟩

theorem checkList_of {A : Fus.Data} (h : A.checkM (· * ·) = true) : Fus.checkList [A] = true := by
  have hf : SE.fmul SE.mulArr = (· * ·) := funext fun a => funext fun b => SE.fmul_mulArr a b
  unfold Fus.checkList
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [hf]
  exact h

end CFSG.KC.GHFus.Good
