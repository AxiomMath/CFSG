module

public import Certificates.Data.Kernel.SporLatDcSort
public import CFSG.Certificates.Kernel.SporLatDcPair
import CFSG.Quasithin.EmptyFaithful.GoldschmidtThreeDLocKer
import CFSG.Certificates.Kernel.SporLatDcLists

public section

namespace CFSG.KC.SLDc

open CFSG.QuasithinUnique.Ch1.SporLat

theorem allIdx_iff {α : Type} (f : Nat → α → Bool) : ∀ (c : Nat) (l : List α),
    allIdx f c l = true ↔ ∀ i (h : i < l.length), f (c + i) l[i] = true
  | _, [] => by simp [allIdx]
  | c, a :: l => by
    rw [allIdx, Bool.and_eq_true, allIdx_iff f (Nat.succ c) l]
    constructor
    · rintro ⟨h0, h⟩ i hi
      rcases i with _ | i
      · simpa using h0
      · have := h i (by simpa using hi)
        rw [show c + (i + 1) = Nat.succ c + i by omega]
        simpa using this
    · intro h
      have h0 := h 0 (by simp)
      rw [Nat.add_zero, List.getElem_cons_zero] at h0
      refine ⟨h0, fun i hi => ?_⟩
      have := h (i + 1) (by simpa using hi)
      rw [show Nat.succ c + i = c + (i + 1) by omega]
      simpa using this

theorem chunksOK_pos {B : Nat} : ∀ {C : List (List (List Nat))}, chunksOK B C = true →
    0 < B ∧ 0 < C.flatten.length
  | [], h => by simp [chunksOK] at h
  | [c], h => by
    simp only [chunksOK, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq] at h
    simp only [List.flatten_cons, List.flatten_nil, List.append_nil]
    omega
  | c :: d :: l, h => by
    simp only [chunksOK, Bool.and_eq_true, Nat.beq_eq] at h
    have := chunksOK_pos h.2
    simp only [List.flatten_cons, List.length_append] at this ⊢
    omega

theorem lookC_eq {B : Nat} : ∀ {C : List (List (List Nat))}, chunksOK B C = true →
    ∀ k < C.flatten.length, lookC B C k = C.flatten.getD k []
  | [], h, _, _ => by simp [chunksOK] at h
  | [c], h, k, hk => by
    simp only [chunksOK, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq] at h
    simp only [List.flatten_cons, List.flatten_nil, List.append_nil] at hk ⊢
    have hkB : k < B := by omega
    have e1 : Nat.div k B = 0 := Nat.div_eq_of_lt hkB
    have e2 : Nat.mod k B = k := Nat.mod_eq_of_lt hkB
    unfold lookC
    rw [e1, e2]
    rfl
  | c :: d :: l, h, k, hk => by
    have h' := h
    simp only [chunksOK, Bool.and_eq_true, Nat.beq_eq] at h'
    obtain ⟨hc, hr⟩ := h'
    have hB := (chunksOK_pos h).1
    have hkf := hk
    simp only [List.flatten_cons, List.length_append] at hk
    rcases Nat.lt_or_ge k B with hkB | hkB
    · have hkc : k < c.length := by omega
      have e1 : Nat.div k B = 0 := Nat.div_eq_of_lt hkB
      have e2 : Nat.mod k B = k := Nat.mod_eq_of_lt hkB
      unfold lookC
      rw [e1, e2, List.getD_cons_zero, List.getD_eq_getElem _ _ hkc,
        List.getD_eq_getElem _ _ hkf]
      simp only [List.flatten_cons]
      rw [List.getElem_append_left hkc]
    · have hk' : k - B < (d :: l).flatten.length := by
        simp only [List.flatten_cons, List.length_append]; omega
      have ih := lookC_eq hr (k - B) hk'
      have e1 : Nat.div k B = Nat.div (k - B) B + 1 := by
        change k / B = (k - B) / B + 1
        rw [← Nat.sub_add_cancel hkB, Nat.add_div_right _ hB, Nat.add_sub_cancel]
      have e2 : Nat.mod k B = Nat.mod (k - B) B := by
        change k % B = (k - B) % B
        conv_lhs => rw [← Nat.sub_add_cancel hkB]
        exact Nat.add_mod_right _ _
      unfold lookC at ih ⊢
      rw [e1, e2, List.getD_cons_succ, ih, List.getD_eq_getElem _ _ hk',
        List.getD_eq_getElem _ _ hkf]
      simp only [List.flatten_cons]
      rw [List.getElem_append_right (as := c) (by omega)]
      congr 1
      omega

theorem omC_sound {act : Array Nat → List Nat → List Nat} {letters : Array (Array Nat)}
    {actF : Nat → List Nat → List Nat} {x0 : List Nat} {B : Nat} {C : List (List (List Nat))}
    {rows : List (List Nat)} {par via ord : List Nat}
    (hP : ∀ l < letters.size, ∀ x, act letters[l]! x = actF l x)
    (h : omC actF x0 letters.size B C rows par via ord = true) :
    OmegaSpec act letters x0 (omOf C rows par via) := by
  unfold omC at h
  simp only [Bool.and_eq_true, beq_iff_eq, Nat.beq_eq, List.all_eq_true, Nat.blt_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hC, h0⟩, hrl⟩, hrows⟩, hpl⟩, hvl⟩, htree⟩, hol⟩, hoi⟩, hs⟩ := h
  set F := C.flatten with hF
  have hpos := (chunksOK_pos hC).2
  have hlk : ∀ k < F.length, lookC B C k = F.getD k [] := lookC_eq hC
  have hget : ∀ k < F.length, (omOf C rows par via).lbl[k]! = F.getD k [] := by
    intro k hk
    simp [omOf, ← hF, Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
      List.getD_eq_getElem?_getD]
    try rfl
  have hsz : (omOf C rows par via).lbl.size = F.length := by simp [omOf, ← hF]
  have hnd : F.Nodup := by
    have hnd' := sortedLt_nodup hs
    have hsub : ord.map (lookC B C) ⊆ F := by
      intro x hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
      rw [hlk i (hoi i hi), List.getD_eq_getElem _ _ (hoi i hi)]
      exact List.getElem_mem _
    have hp := (List.subperm_of_subset hnd' hsub).perm_of_length_le (by simp [hol])
    exact hp.nodup_iff.1 hnd'
  have hrow := (allIdx_iff _ 0 rows).1 hrows
  have hrowi : ∀ l < letters.size, ∀ i < F.length,
      (rows.getD l []).getD i 0 < F.length ∧
        lookC B C ((rows.getD l []).getD i 0) = actF l (F.getD i []) := by
    intro l hl i hi
    have hl' : l < rows.length := by omega
    have e := hrow l hl'
    rw [Nat.zero_add, Bool.and_eq_true, Nat.beq_eq, List.all_eq_true] at e
    have hi' : i < (rows[l]).length := by omega
    have hiz : i < (List.zip rows[l] F).length := by simp; omega
    have := e.2 ((rows[l])[i], F[i]) (List.mem_iff_getElem.2 ⟨i, hiz, by simp [List.getElem_zip]⟩)
    simp only [Bool.and_eq_true, Nat.blt_eq, beq_iff_eq] at this
    rw [List.getD_eq_getElem _ _ hl', List.getD_eq_getElem _ _ hi', List.getD_eq_getElem _ _ hi]
    exact this
  have hpn : ∀ l < letters.size, ∀ i < F.length,
      ((omOf C rows par via).pn[l]!)[i]! = (rows.getD l []).getD i 0 := by
    intro l hl i hi
    simp [omOf, Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]
    try rfl
  have himg : ∀ l < letters.size, ∀ i < F.length,
      ((omOf C rows par via).pn[l]!)[i]! < F.length ∧
        (omOf C rows par via).lbl[((omOf C rows par via).pn[l]!)[i]!]! =
          act letters[l]! (omOf C rows par via).lbl[i]! := by
    intro l hl i hi
    obtain ⟨h1, h2⟩ := hrowi l hl i hi
    rw [hpn l hl i hi, hget _ h1, hget i hi, hP l hl, ← hlk _ h1]
    exact ⟨h1, h2⟩
  refine ⟨?_, by rw [hsz]; exact hpos, fun l hl i hi => himg l hl i (by rwa [hsz] at hi), ?_,
    CFSG.Quasithin.GoldD3.distinctB_of_nodup (by simpa [omOf, ← hF] using hnd)⟩
  · have hpos' : 0 < F.length := hpos
    rw [hget 0 hpos', ← h0]
    obtain ⟨a, t, hat⟩ := List.exists_cons_of_length_pos hpos'
    rw [hat]
    rfl
  · intro i hi hi0
    rw [hsz] at hi
    have ht := (allIdx_iff _ 0 _).1 htree i (by simp; omega)
    simp only [Nat.zero_add, Bool.or_eq_true, Nat.beq_eq, Bool.and_eq_true, Nat.blt_eq,
      beq_iff_eq] at ht
    rcases ht with ht | ⟨⟨hp, hv⟩, he⟩
    · omega
    · simp only [List.getElem_zip] at hp hv he
      have hpar : (omOf C rows par via).par[i]! = par[i]'(by omega) := by
        simp [omOf, Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, List.getElem?_eq_getElem
          (show i < par.length by omega)]
      have hvia : (omOf C rows par via).via[i]! = via[i]'(by omega) := by
        simp [omOf, Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, List.getElem?_eq_getElem
          (show i < via.length by omega)]
      rw [hpar, hvia]
      refine ⟨hp, hv, ?_⟩
      have hpF : par[i]'(by omega) < F.length := by omega
      obtain ⟨h1, h2⟩ := hrowi _ hv _ hpF
      rw [hpn _ hv _ hpF]
      have e1 : F.getD ((rows.getD (via[i]'(by omega)) []).getD (par[i]'(by omega)) 0) [] =
          F.getD i [] := by
        rw [← hlk _ h1, h2, ← hlk _ hpF, he, List.getD_eq_getElem _ _ hi]
      rw [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ hi] at e1
      exact (List.Nodup.getElem_inj_iff hnd).1 e1

theorem omCodeC_sound {m : ℕ} {ts : Array (Array ℕ)} {x0 : List ℕ} {B : Nat}
    {C : List (List (List Nat))} {rows : List (List Nat)} {par via ord : List Nat}
    (h : omCodeC m ts x0 B C rows par via ord = true) :
    OmegaSpec (codeSetAct m) ts x0 (omOf C rows par via) :=
  omC_sound (fun l _ x => by rw [codeSetAct_eq, Array.getElem!_eq_getD]; rfl) h

end CFSG.KC.SLDc

end
