module

public import Certificates.Data.Kernel.SporLatDc
public import CFSG.Certificates.Kernel.E64FSound
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatPt

public section

namespace CFSG.KC.SLDc

open CFSG.QuasithinUnique.Ch1.SporLat CFSG.KC.E64F

theorem lexLt_iff_lt : ∀ a b : List ℕ, lexLt a b = true ↔ a < b
  | [], [] => by simp [lexLt]
  | [], _ :: _ => by simp [lexLt]
  | _ :: _, [] => by simp [lexLt]
  | x :: l, y :: m => by
    rw [lexLt, Bool.or_eq_true, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq,
      lexLt_iff_lt l m, List.cons_lt_cons_iff]

theorem lexLt_irrefl (l : List ℕ) : lexLt l l = false := by
  rw [Bool.eq_false_iff]
  intro h
  rw [lexLt_iff_lt] at h
  exact lt_irrefl l h

private theorem lexLt_ne {a b : List ℕ} (h : lexLt a b = true) : a ≠ b := by
  rintro rfl
  rw [lexLt_irrefl] at h
  exact Bool.false_ne_true h

theorem lexLt_trans {a b c : List ℕ} (h1 : lexLt a b = true) (h2 : lexLt b c = true) :
    lexLt a c = true := by
  rw [lexLt_iff_lt] at *
  exact h1.trans h2

private theorem lexLt_trichotomy (a b : List ℕ) : lexLt a b = true ∨ a = b ∨ lexLt b a = true := by
  rcases lt_trichotomy a b with h | h | h
  · exact Or.inl ((lexLt_iff_lt a b).2 h)
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ((lexLt_iff_lt b a).2 h))

theorem sortedLt_iff_pairwise (l : List (List ℕ)) :
    sortedLt l = true ↔ l.Pairwise (· < ·) := by
  induction l with
  | nil => simp [sortedLt]
  | cons a l ih =>
    rcases l with _ | ⟨b, m⟩
    · simp [sortedLt]
    · have h1 : sortedLt (a :: b :: m) = (lexLt a b && sortedLt (b :: m)) := rfl
      rw [h1, Bool.and_eq_true, ih, lexLt_iff_lt]
      conv_rhs => rw [List.pairwise_cons]
      constructor
      · rintro ⟨hab, h2⟩
        refine ⟨fun x hx => ?_, h2⟩
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hab
        · exact hab.trans ((List.pairwise_cons.mp h2).1 x hx)
      · rintro ⟨h1, h2⟩
        exact ⟨h1 b (by simp), h2⟩

theorem sortedLt_nodup {l : List (List ℕ)} (h : sortedLt l = true) : l.Nodup := by
  rw [List.nodup_iff_pairwise_ne]
  exact List.Pairwise.imp (fun hab => ne_of_lt hab) ((sortedLt_iff_pairwise l).1 h)

theorem headL_min {l : List (List ℕ)} (h : sortedLt l = true) {x : List ℕ} (hx : x ∈ l) :
    x = headL l ∨ lexLt (headL l) x = true := by
  rcases l with _ | ⟨a, l⟩
  · exact absurd hx (by simp)
  · rcases List.mem_cons.mp hx with rfl | hx
    · exact Or.inl rfl
    · refine Or.inr ?_
      rw [lexLt_iff_lt]
      exact (List.pairwise_cons.mp ((sortedLt_iff_pairwise (a :: l)).1 h)).1 x hx

theorem lastL_max : ∀ (l : List (List ℕ)), sortedLt l = true →
    ∀ x ∈ l, x = lastL l ∨ lexLt x (lastL l) = true := by
  intro l
  induction l with
  | nil => intro _ x hx; exact absurd hx (by simp)
  | cons a l ih =>
    rcases l with _ | ⟨b, m⟩
    · intro _ x hx
      rw [List.mem_singleton.mp hx]
      exact Or.inl rfl
    · intro h x hx
      have h' : sortedLt (b :: m) = true := by
        have hh := h
        rw [show a :: b :: m = a :: (b :: m) from rfl, sortedLt, Bool.and_eq_true] at hh
        exact hh.2
      have hab : a < b := by
        have hh := h
        rw [show a :: b :: m = a :: (b :: m) from rfl, sortedLt, Bool.and_eq_true,
          lexLt_iff_lt] at hh
        exact hh.1
      have hlast : lastL (a :: b :: m) = lastL (b :: m) := rfl
      rw [hlast]
      rcases List.mem_cons.mp hx with hx' | hx
      · rw [hx']
        have hlt : a < lastL (b :: m) := by
          rcases ih h' b (by simp) with hb' | hb'
          · rw [← hb']; exact hab
          · exact hab.trans ((lexLt_iff_lt b (lastL (b :: m))).1 hb')
        exact Or.inr ((lexLt_iff_lt a (lastL (b :: m))).2 hlt)
      · exact ih h' x hx

private theorem insU_cons (a b : List ℕ) (l : List (List ℕ)) :
    insU a (b :: l) = (bif lexLt a b then a :: b :: l else
      bif a == b then b :: l else b :: insU a l) := rfl

private theorem mem_insU (a : List ℕ) : ∀ (l : List (List ℕ)) (x : List ℕ),
    x ∈ insU a l ↔ x = a ∨ x ∈ l := by
  intro l
  induction l with
  | nil => intro x; simp [insU]
  | cons b l ih =>
    intro x
    rw [insU_cons]
    cases h : lexLt a b with
    | false =>
      cases h2 : (a == b) with
      | false =>
        simp only [h, h2, cond_false, List.mem_cons, ih x]
        tauto
      | true =>
        have hab : a = b := by simpa using h2
        simp only [h, h2, cond_false, cond_true, List.mem_cons, hab]
        tauto
    | true =>
      simp only [h, cond_true, List.mem_cons]

private theorem sortedLt_cons_iff (b : List ℕ) (m : List (List ℕ)) :
    sortedLt (b :: m) = true ↔ sortedLt m = true ∧ ∀ c ∈ m, lexLt b c = true := by
  rw [sortedLt_iff_pairwise, sortedLt_iff_pairwise, List.pairwise_cons]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h2, fun c hc => (lexLt_iff_lt b c).2 (h1 c hc)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun c hc => (lexLt_iff_lt b c).1 (h2 c hc), h1⟩

private theorem sortedLt_insU (a : List ℕ) : ∀ (l : List (List ℕ)), sortedLt l = true →
    sortedLt (insU a l) = true := by
  intro l
  induction l with
  | nil => intro _; exact rfl
  | cons b l ih =>
    intro h
    obtain ⟨hs, hall⟩ := (sortedLt_cons_iff b l).1 h
    rw [insU_cons]
    cases hlt : lexLt a b with
    | true =>
      simp only [hlt, cond_true]
      exact (sortedLt_cons_iff a (b :: l)).2 ⟨h, fun c hc => by
        rcases List.mem_cons.mp hc with rfl | hc
        · exact hlt
        · exact lexLt_trans hlt (hall c hc)⟩
    | false =>
      cases heq : (a == b) with
      | true =>
        simpa only [hlt, heq, cond_false, cond_true] using h
      | false =>
        simp only [hlt, heq, cond_false]
        refine (sortedLt_cons_iff b (insU a l)).2 ⟨ih hs, fun c hc => ?_⟩
        have hba : lexLt b a = true := by
          rcases lexLt_trichotomy a b with hab | hab | hba
          · rw [hlt] at hab
            exact (Bool.false_ne_true hab).elim
          · rw [hab] at heq
            simp at heq
          · exact hba
        rcases (mem_insU a l c).1 hc with hc' | hc
        · rw [hc']
          exact hba
        · exact hall c hc

private theorem insU_toFinset (a : List ℕ) : ∀ l : List (List ℕ),
    (insU a l).toFinset = insert a l.toFinset := by
  intro l
  induction l with
  | nil => simp [insU]
  | cons b l ih =>
    rw [insU_cons]
    cases hlt : lexLt a b with
    | true =>
      simp only [hlt, cond_true, List.toFinset_cons]
    | false =>
      cases heq : (a == b) with
      | true =>
        have hab : a = b := by simpa using heq
        subst hab
        simp only [hlt, heq, cond_false, cond_true, List.toFinset_cons]
        simp
      | false =>
        simp only [hlt, heq, cond_false, List.toFinset_cons, ih]
        rw [Finset.insert_comm]

theorem cntB_eq_length_filter {α : Type} (f : α → Bool) :
    ∀ l : List α, cntB f l = (l.filter f).length
  | [] => rfl
  | a :: l => by
    rw [cntB, List.filter_cons]
    cases h : f a with
    | false =>
      rw [cond_false, if_neg (by simp)]
      exact cntB_eq_length_filter f l
    | true =>
      rw [cond_true, if_pos rfl, List.length_cons, cntB_eq_length_filter f l]

theorem sortN_toFinset (l : List ℕ) : (sortN l).toFinset = l.toFinset := by
  ext a
  rw [List.mem_toFinset, List.mem_toFinset, mem_sortN]

theorem insK_toFinset (C : DcCtx) (ks : List (List ℕ)) (y : List ℕ) :
    ∀ U : List (List ℕ), (insK C ks y U).toFinset =
      U.toFinset ∪ ks.toFinset.image (fun k => labF (wordF C.L k) y) := by
  intro U
  induction ks generalizing U with
  | nil => simp [insK]
  | cons k ks ih =>
    show (insK C ks y (insU (labF (wordF C.L k) y) U)).toFinset
      = U.toFinset ∪ (k :: ks).toFinset.image (fun k => labF (wordF C.L k) y)
    rw [ih, insU_toFinset, List.toFinset_cons, Finset.image_insert, Finset.insert_union,
      Finset.union_insert]

theorem sortedLt_insK (C : DcCtx) (ks : List (List ℕ)) (y : List ℕ) :
    ∀ U : List (List ℕ), sortedLt U = true → sortedLt (insK C ks y U) = true := by
  intro U hU
  induction ks generalizing U with
  | nil => exact hU
  | cons k ks ih =>
    show sortedLt (insK C ks y (insU (labF (wordF C.L k) y) U)) = true
    exact ih _ (sortedLt_insU _ U hU)

end CFSG.KC.SLDc

end
