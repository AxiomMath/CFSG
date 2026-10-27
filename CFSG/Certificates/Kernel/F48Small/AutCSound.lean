module

public import Certificates.Data.Kernel.F48Small.AutC
public import CFSG.Certificates.Kernel.F48Small.Sp43cSound

public section

namespace CFSG.KC.F48S

open CFSG.KC.Ord CFSG.KC.LQT.L CFSG.Quasithin CFSG.ASVolI

theorem autcSplit_eq (c : Char) : ∀ (l acc : List Char),
    autcSplit c l acc = List.splitOnPPrepend (· == c) l acc
  | [], acc => by rw [List.splitOnPPrepend_nil]; rfl
  | a :: t, acc => by
    change Bool.rec (motive := fun _ => List (List Char)) (autcSplit c t (a :: acc))
      (acc.reverse :: autcSplit c t []) (a == c) = _
    cases h : (a == c)
    · rw [List.splitOnPPrepend_cons_neg (p := (· == c)) (by simp [h]), autcSplit_eq c t]
    · rw [List.splitOnPPrepend_cons_pos (p := (· == c)) h, autcSplit_eq c t [],
        List.splitOnPPrepend_nil_right]

theorem autcSplit_nil (c : Char) (l : List Char) : autcSplit c l [] = l.splitOn c := by
  rw [autcSplit_eq, List.splitOn_eq_splitOnP, List.splitOnP_eq_splitOnPPrepend]

theorem autc_evL_eq (gl gli : List (List ℕ)) :
    burnsideF48s_autc_evL gl gli = burnsideF48s_eEvL 45 gl gli := by
  funext w
  simp only [burnsideF48s_autc_evL, burnsideF48s_eEvL]
  congr 1
  funext acc l
  congr 1
  obtain ⟨k, b⟩ := l
  cases b <;> rfl

theorem autc_letOK {gl gli : List (List ℕ)} (h : autcLetOK gl gli = true) : LetOK 45 5 gl gli := by
  simp only [autcLetOK, Bool.and_eq_true, Nat.ble_eq, List.all_eq_true, beq_iff_eq,
    Nat.blt_eq] at h
  exact ⟨by norm_num, h.1.1, h.1.2, fun l hl => ⟨(h.2 l hl).1, (h.2 l hl).2⟩⟩

theorem autc_groupB_of {gl gli : List (List ℕ)} (h : LetOK 45 5 gl gli) {idx : List (Fin 5)}
    {W : List (List (Fin 5 × Bool))} {n : ℕ} (hh : autcHead W idx n = true)
    (hk : groupK 45 (W.map (evK 45 (gl.map encL) (gli.map encL)))
      ((idx.map Fin.val).map (getK (gl.map encL))) = true) :
    burnsideF48s_autc_groupB gl gli idx W n = true := by
  change CFSG.KC.Ord.andB _ _ = true at hk
  rw [andB_eq, Bool.and_eq_true] at hk
  obtain ⟨hnd, hcl⟩ := hk
  simp only [autcHead, Bool.and_eq_true] at hh
  obtain ⟨⟨hn, h0⟩, hl⟩ := hh
  have hev : (fun w => encL (burnsideF48s_eEvL 45 gl gli w)) =
      evK 45 (gl.map encL) (gli.map encL) := funext (encL_ev h)
  have hg : ∀ g ∈ idx.map Fin.val, g < 5 := by
    intro g hg
    obtain ⟨a, -, rfl⟩ := List.mem_map.1 hg
    exact a.2
  have hcl' := (eClosed_ev h W (idx.map Fin.val) hg).trans hcl
  rw [burnsideF48s_autc_groupB, autc_evL_eq]
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨hn, h0⟩, ?_⟩, hl⟩, ?_⟩
  · rw [decide_eq_true_eq]
    refine List.Nodup.of_map encL ?_
    rw [List.map_map, Function.comp_def, hev]
    exact (nodupT_sound _ NT.lf trivial hnd).2
  · simpa only [burnsideF48s_eClosed, List.all_map, Function.comp_def] using hcl'

theorem autc_inf_of {gl gli : List (List ℕ)} (h : LetOK 45 5 gl gli)
    (W1 W2 WB : List (List (Fin 5 × Bool)))
    (hk : autcInfK (W1.map (evK 45 (gl.map encL) (gli.map encL)))
      (setT (W2.map (evK 45 (gl.map encL) (gli.map encL))))
      (setT (WB.map (evK 45 (gl.map encL) (gli.map encL)))) = true) :
    ((W1.map (burnsideF48s_autc_evL gl gli)).all fun x =>
      !((W2.map (burnsideF48s_autc_evL gl gli)).contains x) ||
        (WB.map (burnsideF48s_autc_evL gl gli)).contains x) = true := by
  rw [autc_evL_eq]
  simp only [autcInfK, allA_eq, orB_eq, notB_eq, List.all_map, Function.comp_def] at hk
  simpa only [List.all_map, Function.comp_def, contains_ev h] using hk

end CFSG.KC.F48S
