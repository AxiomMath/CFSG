module

public import Certificates.Data.Kernel.SporLatDcP
public import Certificates.Data.Kernel.SporLatDcL
public import CFSG.Certificates.Kernel.SporLatDcSortSound

public section

namespace CFSG.KC.SLDc

open CFSG.QuasithinUnique.Ch1.SporLat CFSG.KC.E64F

theorem slotDc_packDc (w : Nat) : ∀ (xs : List Nat), (∀ a ∈ xs, a < 2 ^ w) →
    ∀ i, slotDc w (packDc w xs) i = xs.getD i 0
  | [], _, i => by
    change (0 >>> (w * i)) % 2 ^ w = _
    simp
  | a :: l, h, i => by
    have ha : a < 2 ^ w := h a (by simp)
    have e : packDc w (a :: l) = a + 2 ^ w * packDc w l := rfl
    change ((packDc w (a :: l)) >>> (w * i)) % 2 ^ w = _
    rw [e]
    rcases i with _ | i
    · simp [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]
    · have e2 : w * (i + 1) = w + w * i := by rw [Nat.mul_succ, Nat.add_comm]
      rw [e2, Nat.shiftRight_add, Nat.shiftRight_eq_div_pow (a + _) w,
        Nat.add_mul_div_left _ _ (Nat.two_pow_pos w), Nat.div_eq_of_lt ha, Nat.zero_add]
      exact slotDc_packDc w l (fun b hb => h b (by simp [hb])) i

theorem encSetDc_cons (n a : Nat) (l : List Nat) :
    encodeSet n (a :: l) = (a + 1) + (n + 1) * encodeSet n l := rfl

theorem encodeSet_inj (n : Nat) : ∀ xs ys : List Nat, (∀ a ∈ xs, a < n) → (∀ a ∈ ys, a < n) →
    encodeSet n xs = encodeSet n ys → xs = ys
  | [], [], _, _, _ => rfl
  | [], b :: m, _, _, h => by
    rw [encSetDc_cons] at h
    change 0 = _ at h
    omega
  | a :: l, [], _, _, h => by
    rw [encSetDc_cons] at h
    change _ = 0 at h
    omega
  | a :: l, b :: m, hx, hy, h => by
    rw [encSetDc_cons, encSetDc_cons] at h
    have ha : a < n := hx a (by simp)
    have hb : b < n := hy b (by simp)
    have hm := congrArg (· % (n + 1)) h
    simp only [Nat.add_mul_mod_self_left] at hm
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hm
    have hab : a = b := by omega
    subst hab
    have h2 := Nat.eq_of_mul_eq_mul_left (Nat.succ_pos n) (Nat.add_left_cancel h)
    rw [encodeSet_inj n l m (fun c hc => hx c (by simp [hc])) (fun c hc => hy c (by simp [hc])) h2]

theorem incDc_pairwise : ∀ l : List Nat, incDc l = true → l.Pairwise (· < ·)
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: l, h => by
    have h' : (Nat.blt a b && incDc (b :: l)) = true := h
    rw [Bool.and_eq_true, Nat.blt_eq] at h'
    have ih := incDc_pairwise (b :: l) h'.2
    refine List.pairwise_cons.2 ⟨fun x hx => ?_, ih⟩
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h'.1
    · exact Nat.lt_trans h'.1 ((List.pairwise_cons.1 ih).1 x hx)

theorem zipAllDc {α β : Type} {r : List α} {L : List β} {f : α × β → Prop} {d : α} {e : β}
    (h : ∀ x ∈ List.zip r L, f x) (hl : r.length = L.length) :
    ∀ i < L.length, f (r.getD i d, L.getD i e) := by
  intro i hi
  have hi' : i < (List.zip r L).length := by simp [hl, hi]
  have hm := h _ (List.getElem_mem hi')
  rw [List.getElem_zip] at hm
  rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ hi]
  exact hm

theorem omPK_sound {actF : Nat → List Nat → List Nat} {x0 : List Nat} {nl M w n : Nat}
    {lbl rows : List (List Nat)} {par via : List Nat}
    (h : omPK actF x0 nl M w n lbl rows par via (packDc w (lbl.map (encodeSet M)))
      (rows.map (packDc w)) = true) :
    lbl.getD 0 [] = x0 ∧ 0 < lbl.length ∧
    (∀ l < nl, ∀ i < lbl.length, (rows.getD l []).getD i 0 < lbl.length ∧
      lbl.getD ((rows.getD l []).getD i 0) [] = actF l (lbl.getD i [])) ∧
    (∀ i < lbl.length, i = 0 ∨ (par.getD i 0 < i ∧ via.getD i 0 < nl ∧
      (rows.getD (via.getD i 0) []).getD (par.getD i 0) 0 = i)) ∧
    lbl.Nodup := by
  unfold omPK at h
  simp only [Bool.and_eq_true, beq_iff_eq, Nat.blt_eq, Nat.beq_eq, List.all_eq_true,
    List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h0, hn⟩, hlen⟩, hw⟩, hlb⟩, hrow⟩, hpl⟩, hvl⟩, htree⟩, hinc⟩ := h
  subst hlen
  have hK : ∀ p < lbl.length, slotDc w (packDc w (lbl.map (encodeSet M))) p =
      encodeSet M (lbl.getD p []) := by
    intro p hp
    rw [slotDc_packDc w _ (fun a ha => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ha
      exact (hlb x hx).2) p]
    rw [List.getD_eq_getElem _ _ (by simpa using hp), List.getD_eq_getElem _ _ hp,
      List.getElem_map]
  have hmemL : ∀ p < lbl.length, ∀ a ∈ lbl.getD p [], a < M := by
    intro p hp a ha
    rw [List.getD_eq_getElem _ _ hp] at ha
    exact (hlb _ (List.getElem_mem hp)).1 a ha
  have hact : ∀ l < nl, ∀ i < lbl.length, (rows.getD l []).getD i 0 < lbl.length ∧
      lbl.getD ((rows.getD l []).getD i 0) [] = actF l (lbl.getD i []) := by
    intro l hl i hi
    obtain ⟨hrl, hz⟩ := hrow l hl
    have e := zipAllDc (d := 0) (e := []) hz hrl i hi
    beta_reduce at e
    simp only [Bool.and_eq_true, Nat.blt_eq, imgDc, Nat.beq_eq, List.all_eq_true] at e
    obtain ⟨hp, hy, hs⟩ := e
    refine ⟨hp, encodeSet_inj M _ _ (hmemL _ hp) hy ?_⟩
    rw [← hK _ hp, hs]
  have hrowB : ∀ l < nl, ∀ a ∈ rows.getD l [], a < 2 ^ w := by
    intro l hl a ha
    obtain ⟨hrl, hz⟩ := hrow l hl
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 ha
    have e := zipAllDc (d := 0) (e := []) hz hrl i (by omega)
    beta_reduce at e
    rw [List.getD_eq_getElem _ _ hi] at e
    exact Nat.lt_trans e.1 hw
  refine ⟨?_, hn, hact, ?_, ?_⟩
  · rw [List.getD_eq_getElem _ _ hn, ← h0]
    cases lbl with
    | nil => simp at hn
    | cons a l => rfl
  · intro i hi
    have hzl : (List.zip par via).length = lbl.length := by simp [hpl, hvl]
    have e := (allIdx_iff _ 0 _).1 htree i (by omega)
    rw [List.getElem_zip, Nat.zero_add] at e
    simp only [Bool.or_eq_true, Nat.beq_eq, Bool.and_eq_true, Nat.blt_eq] at e
    rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]
    rcases e with e | ⟨⟨e1, e2⟩, e3⟩
    · exact Or.inl e
    · refine Or.inr ⟨e1, e2, ?_⟩
      have eR : (rows.map (packDc w)).getD via[i] 0 = packDc w (rows.getD via[i] []) := by
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
        cases rows[via[i]]? <;> rfl
      rw [eR, slotDc_packDc w _ (hrowB _ e2)] at e3
      exact e3
  · have hp := incDc_pairwise _ hinc
    rw [insN_eq] at hp
    exact List.Nodup.of_map _
      ((List.perm_insertionSort _ _).nodup_iff.1 (List.Pairwise.imp (fun h => Nat.ne_of_lt h) hp))

theorem omOKP_omOKG {actF : Nat → List Nat → List Nat} {x0 : List Nat} {nl M w : Nat}
    {O : OmegaData (List Nat)} (h : omOKP actF x0 nl M w O = true) :
    omOKG actF x0 nl O = true := by
  obtain ⟨h0, hn, hact, htree, hnd⟩ := omPK_sound h
  have eR : ∀ l, ((O.pn.toList.map Array.toList).getD l []) =
      (O.pn.toList.getD l default).toList := by
    intro l
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
    cases O.pn.toList[l]? <;> rfl
  simp only [eR] at hact htree
  rw [← omOKL_eq]
  unfold omOKL
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨h0, hn⟩, fun l hl i hi => ⟨(hact l hl i hi).1, (hact l hl i hi).2⟩⟩,
    fun i hi => ?_⟩, hnd⟩
  rcases htree i hi with e | ⟨e1, e2, e3⟩
  · exact Or.inl e
  · exact Or.inr ⟨⟨e1, e2⟩, e3⟩

theorem omCodeP_sound {m M w : ℕ} {ts : Array (Array ℕ)} {x0 : List ℕ} {O : OmegaData (List ℕ)}
    (h : omOKP (fun l x => codeSetT m (ts.getD l #[]) x) x0 ts.size M w O = true) :
    OmegaSpec (codeSetAct m) ts x0 O :=
  omCode_sound (omOKP_omOKG h)

end CFSG.KC.SLDc

end
