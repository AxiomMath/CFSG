module

public import CFSG.RankThree.Native.F2Enum
public import CFSG.RankThree.Native.F2Bind
public import CFSG.Sporadic.Co2Schreier.Arrays

public section

namespace CFSG.KS.MatRep

open CFSG.RankThree.Native.F2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

variable {d : ℕ} {V : Array ℕ}

structure Good (d : ℕ) (V : Array ℕ) : Prop where
  hd : 0 < d
  nodup : V.toList.Nodup
  lt : ∀ v ∈ V, v < 2 ^ d

@[expose] def Rep (d : ℕ) (V : Array ℕ) (a : Array ℕ) (M M' : ℕ) : Prop :=
  a = permOfMat d V M ∧ Inv d V M M'

theorem rep_idA (G : Good d V) : Rep d V (idA V.size) (idM d) (idM d) :=
  ⟨(permOfMat_idM G.hd G.nodup G.lt).symm, inv_idM G.hd G.lt⟩

theorem rep_compA (G : Good d V) {a b : Array ℕ} {A A' B B' : ℕ} (ha : Rep d V a A A')
    (hb : Rep d V b B B') : Rep d V (compA V.size a b) (mmul d B A) (mmul d A' B') := by
  refine ⟨?_, Inv.mul G.hd hb.2 ha.2⟩
  rw [ha.1, hb.1, compA_permOfMat hb.2.1]

theorem rep_invCand (G : Good d V) {a : Array ℕ} {A A' : ℕ} (ha : Rep d V a A A') :
    Rep d V (invCand V.size a) A' A := by
  refine ⟨?_, Inv.symm ha.2⟩
  rw [ha.1, invCand_permOfMat G.hd G.nodup G.lt ha.2]

@[expose] noncomputable def mpowI (mm : ℕ → ℕ → ℕ) (I A' e : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) I (fun _ acc => mm A' acc) e

theorem rep_powArr (G : Good d V) {mm : ℕ → ℕ → ℕ} (hmm : ∀ A B, mm A B = mmul d A B) {I : ℕ}
    (hI : I = idM d) {a : Array ℕ} {A A' : ℕ} (ha : Rep d V a A A') :
    ∀ e, Rep d V (CFSG.Monster.B.Mathieu.powArr V.size a e) (mpowW mm I A e) (mpowI mm I A' e)
  | 0 => by
    rw [hI]
    exact rep_idA G
  | e + 1 => by
    have h := rep_compA G ha (rep_powArr G hmm hI ha e)
    change Rep d V (compA V.size a (CFSG.Monster.B.Mathieu.powArr V.size a e))
      (mm (mpowW mm I A e) A) (mm A' (mpowI mm I A' e))
    rw [hmm, hmm]
    exact h

@[expose] noncomputable def wordMI (mm : ℕ → ℕ → ℕ) (I : ℕ) (LMI : ℤ → ℕ) : List ℤ → ℕ
  | [] => I
  | l :: w => mm (LMI l) (wordMI mm I LMI w)

theorem rep_wordA (G : Good d V) {mm : ℕ → ℕ → ℕ} (hmm : ∀ A B, mm A B = mmul d A B) {I : ℕ}
    (hI : I = idM d) {A : Array (Array ℕ)} {CS CSI : ℕ → ℕ} {j : ℕ} (hj : j ≤ A.size)
    (hA : ∀ h < j, Rep d V A[h]! (CS h) (CSI h)) :
    ∀ w : List ℤ, lettersOK j w = true →
      Rep d V (wordA V.size A (rawInvs V.size A) w) (wordM mm I (letterM CS CSI) w)
        (wordMI mm I (letterM CSI CS) w)
  | [], _ => by
    rw [wordM, wordMI, wordA, hI]
    exact rep_idA G
  | l :: w, hw => by
    simp only [lettersOK, List.all_cons, Bool.and_eq_true, bne_iff_ne, ne_eq,
      decide_eq_true_eq] at hw
    obtain ⟨⟨hl0, hlj⟩, hw⟩ := hw
    have hw' : lettersOK j w = true := by
      simpa [lettersOK, List.all_eq_true] using hw
    have ih := rep_wordA G hmm hI hj hA w hw'
    have hL : Rep d V (letterA A (rawInvs V.size A) l) (letterM CS CSI l) (letterM CSI CS l) := by
      unfold letterA letterM
      by_cases hpos : 0 < l
      · rw [ite_eq_left hpos, decide_eq_true hpos, Bool.cond_true, Bool.cond_true]
        exact hA _ (by omega)
      · rw [ite_eq_right hpos, decide_eq_false hpos, Bool.cond_false, Bool.cond_false]
        have hk : (-l).toNat - 1 < A.size := by omega
        have e : (rawInvs V.size A)[(-l).toNat - 1]! = invCand V.size A[(-l).toNat - 1]! := by
          rw [rawInvs, getElem!_pos _ _ (by simpa using hk), Array.getElem_map,
            getElem!_pos A _ hk]
        rw [e]
        exact rep_invCand G (hA _ (by omega))
    rw [wordA, wordM, wordMI, hmm, hmm]
    exact rep_compA G hL ih

@[expose] def RepT (d : ℕ) (V : Array ℕ) (A : Array (Array ℕ)) (T : List (ℕ × ℕ)) : Prop :=
  A.size = T.length ∧ ∀ k < T.length, Rep d V A[k]! (T.getD k (0, 0)).1 (T.getD k (0, 0)).2

@[expose] noncomputable def wordP (mm : ℕ → ℕ → ℕ) (I : ℕ) (T : List (ℕ × ℕ)) (w : List ℤ) :
    ℕ × ℕ :=
  (wordM mm I (letterM (fun h => (T.getD h (0, 0)).1) (fun h => (T.getD h (0, 0)).2)) w,
    wordMI mm I (letterM (fun h => (T.getD h (0, 0)).2) (fun h => (T.getD h (0, 0)).1)) w)

theorem rep_word (G : Good d V) {mm : ℕ → ℕ → ℕ} (hmm : ∀ A B, mm A B = mmul d A B) {I : ℕ}
    (hI : I = idM d) {A : Array (Array ℕ)} {T : List (ℕ × ℕ)} (hT : RepT d V A T)
    {w : List ℤ} (hw : lettersOK T.length w = true) :
    Rep d V (wordA V.size A (rawInvs V.size A) w) (wordP mm I T w).1 (wordP mm I T w).2 :=
  rep_wordA G hmm hI (by rw [hT.1]) hT.2 w hw

theorem rep_wordArr (G : Good d V) (hV : V.size = 2300) {mm : ℕ → ℕ → ℕ}
    (hmm : ∀ A B, mm A B = mmul d A B) {I : ℕ} (hI : I = idM d) {A : Array (Array ℕ)}
    {T : List (ℕ × ℕ)} (hT : RepT d V A T) {w : List ℤ} (hw : lettersOK T.length w = true) :
    Rep d V (CFSG.Sporadic.Co2Schreier.wordArr A w) (wordP mm I T w).1 (wordP mm I T w).2 := by
  unfold CFSG.Sporadic.Co2Schreier.wordArr
  rw [← hV]
  exact rep_word G hmm hI hT hw

theorem repT_map {A : Array (Array ℕ)} {T : List (ℕ × ℕ)} (hT : RepT d V A T)
    {f : Array ℕ → Array ℕ} {F : ℕ × ℕ → ℕ × ℕ}
    (hf : ∀ a p, Rep d V a p.1 p.2 → Rep d V (f a) (F p).1 (F p).2) :
    RepT d V (A.map f) (T.map F) := by
  refine ⟨by simp [hT.1], fun k hk => ?_⟩
  rw [List.length_map] at hk
  have hkA : k < A.size := by rw [hT.1]; exact hk
  have e1 : (A.map f)[k]! = f A[k]! := by
    rw [getElem!_pos _ k (by simpa using hkA), Array.getElem_map, getElem!_pos A k hkA]
  have e2 : (T.map F).getD k (0, 0) = F (T.getD k (0, 0)) := by
    rw [List.getD_eq_getElem _ _ (by simpa using hk), List.getD_eq_getElem _ _ hk,
      List.getElem_map]
  rw [e1, e2]
  exact hf _ _ (hT.2 k hk)

@[expose] def wordsOK (j : ℕ) (ws : List (List ℤ)) : Bool := ws.all (lettersOK j)

theorem repT_words (G : Good d V) (hV : V.size = 2300) {mm : ℕ → ℕ → ℕ}
    (hmm : ∀ A B, mm A B = mmul d A B) {I : ℕ} (hI : I = idM d) {A : Array (Array ℕ)}
    {T : List (ℕ × ℕ)} (hT : RepT d V A T) {ws : List (List ℤ)}
    (hw : wordsOK T.length ws = true) :
    RepT d V (ws.map (CFSG.Sporadic.Co2Schreier.wordArr A)).toArray (ws.map (wordP mm I T)) := by
  refine ⟨by simp, fun k hk => ?_⟩
  rw [List.length_map] at hk
  have hwk : lettersOK T.length ws[k] = true :=
    List.all_eq_true.1 hw _ (List.getElem_mem hk)
  rw [getElem!_pos _ k (by simpa using hk), List.getD_eq_getElem _ _ (by simpa using hk)]
  simp only [List.getElem_toArray, List.getElem_map]
  unfold CFSG.Sporadic.Co2Schreier.wordArr
  rw [← hV]
  exact rep_word G hmm hI hT hwk

@[expose] noncomputable def extP (mm : ℕ → ℕ → ℕ) (I : ℕ) (T : List (ℕ × ℕ))
    (ds : List (List ℤ)) : List (ℕ × ℕ) :=
  ds.foldl (fun acc w => acc ++ [wordP mm I acc w]) T

@[expose] def extOK : ℕ → List (List ℤ) → Bool
  | _, [] => true
  | j, w :: ds => lettersOK j w && extOK (j + 1) ds

theorem repT_push {A : Array (Array ℕ)} {T : List (ℕ × ℕ)} (hT : RepT d V A T) {a : Array ℕ}
    {M M' : ℕ} (ha : Rep d V a M M') : RepT d V (A.push a) (T ++ [(M, M')]) := by
  refine ⟨by simp [hT.1], fun k hk => ?_⟩
  simp only [List.length_append, List.length_singleton] at hk
  rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hlt | rfl
  · have hkA : k < A.size := by rw [hT.1]; exact hlt
    have e1 : (A.push a)[k]! = A[k]! := by
      rw [getElem!_pos _ k (by simp; omega), getElem!_pos A k hkA]
      exact Array.getElem_push_lt hkA
    have e2 : (T ++ [(M, M')]).getD k (0, 0) = T.getD k (0, 0) := by
      rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ hlt,
        List.getElem_append_left hlt]
    rw [e1, e2]
    exact hT.2 k hlt
  · have e1 : (A.push a)[T.length]! = a := by
      have hs : A.size = T.length := hT.1
      have e : (A.push a)[A.size]! = a := by
        rw [getElem!_pos _ _ (by simp)]
        exact Array.getElem_push_eq
      rwa [hs] at e
    have e2 : (T ++ [(M, M')]).getD T.length (0, 0) = (M, M') := by
      rw [List.getD_eq_getElem _ _ (by simp)]
      simp
    rw [e1, e2]
    exact ha

theorem repT_extend (G : Good d V) (hV : V.size = 2300) {mm : ℕ → ℕ → ℕ}
    (hmm : ∀ A B, mm A B = mmul d A B) {I : ℕ} (hI : I = idM d) :
    ∀ (ds : List (List ℤ)) {A : Array (Array ℕ)} {T : List (ℕ × ℕ)}, RepT d V A T →
      extOK T.length ds = true →
      RepT d V (CFSG.Sporadic.Co2Schreier.extendArrs A ds) (extP mm I T ds)
  | [], _, _, hT, _ => hT
  | w :: ds, A, T, hT, hw => by
    simp only [extOK, Bool.and_eq_true] at hw
    have hr : Rep d V (CFSG.Sporadic.Co2Schreier.wordArr A w) (wordP mm I T w).1
        (wordP mm I T w).2 := by
      unfold CFSG.Sporadic.Co2Schreier.wordArr
      rw [← hV]
      exact rep_word G hmm hI hT hw.1
    have hT' := repT_push hT hr
    rw [Prod.mk.eta] at hT'
    have hlen : (T ++ [wordP mm I T w]).length = T.length + 1 := by simp
    have := repT_extend G hV hmm hI ds hT' (by rw [hlen]; exact hw.2)
    unfold CFSG.Sporadic.Co2Schreier.extendArrs extP
    rw [List.foldl_cons, List.foldl_cons]
    unfold CFSG.Sporadic.Co2Schreier.extendArrs extP at this
    exact this

theorem repT_append {A B : Array (Array ℕ)} {S T : List (ℕ × ℕ)} (hA : RepT d V A S)
    (hB : RepT d V B T) : RepT d V (A ++ B) (S ++ T) := by
  refine ⟨by simp [hA.1, hB.1], fun k hk => ?_⟩
  simp only [List.length_append] at hk
  by_cases hlt : k < S.length
  · have e1 : (A ++ B)[k]! = A[k]! := by
      rw [getElem!_pos _ k (by simp [hA.1]; omega), getElem!_pos A k (by rw [hA.1]; exact hlt)]
      exact Array.getElem_append_left (by rw [hA.1]; exact hlt)
    rw [e1, List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_left hlt,
      ← List.getD_eq_getElem _ (0, 0) hlt]
    exact hA.2 k hlt
  · have hk2 : k - S.length < T.length := by omega
    have e1 : (A ++ B)[k]! = B[k - S.length]! := by
      rw [getElem!_pos _ k (by simp [hA.1, hB.1]; omega),
        getElem!_pos B _ (by rw [hB.1]; exact hk2)]
      rw [Array.getElem_append_right (by rw [hA.1]; omega)]
      simp [hA.1]
    rw [e1, List.getD_eq_getElem _ _ (by simp; omega),
      List.getElem_append_right (by omega), ← List.getD_eq_getElem _ (0, 0) hk2]
    exact hB.2 _ hk2

theorem repT_get {A : Array (Array ℕ)} {T : List (ℕ × ℕ)} (hT : RepT d V A T) {k : ℕ}
    (hk : k < T.length) : Rep d V A[k]! (T.getD k (0, 0)).1 (T.getD k (0, 0)).2 :=
  hT.2 k hk

theorem get_rep {a : Array ℕ} {M M' : ℕ} (ha : Rep d V a M M') {i : ℕ} (hi : i < V.size) :
    a[i]! < V.size ∧ V[a[i]!]! = vmul d V[i]! M := by
  rw [ha.1, permOfMat_get hi]
  exact getElem_vidx (ha.2.1 _ (mem_of_lt hi))

end CFSG.KS.MatRep

end
