module

public import Certificates.Data.Kernel.F4Three.Defs
public import CFSG.Certificates.Kernel.U6ThreeSound

public section

namespace CFSG.KC.F4Three

open CFSG.RankThree.PartOne.F106 CFSG.LieType.Simplicity.TitsBits CFSG.KC.U6Three CFSG.KTabPack

theorem getN_eq (L : List ℕ) (n : ℕ) : getN L n = L.getD n 0 := by
  induction L generalizing n with
  | nil => rfl
  | cons a L ih =>
    cases n with
    | zero => rfl
    | succ m => exact ih m

theorem getL_eq (L : List (List ℕ)) (n : ℕ) : getL L n = L.getD n [] := by
  induction L generalizing n with
  | nil => rfl
  | cons a L ih =>
    cases n with
    | zero => rfl
    | succ m => exact ih m

theorem look_eq (TT : List (List ℕ)) (h : ∀ l ∈ TT, l.length = 27) (j : ℕ) :
    look TT j = TT.flatten.getD j 0 := by
  induction TT generalizing j with
  | nil => simp [look, getN_eq, getL_eq]
  | cons l TT ih =>
    have hl : l.length = 27 := h l List.mem_cons_self
    rw [List.flatten_cons]
    by_cases hj : j < 27
    · rw [List.getD_append _ _ _ _ (by omega), look, getL_eq, getN_eq,
        Nat.div_eq_of_lt hj, Nat.mod_eq_of_lt hj]
      rfl
    · rw [List.getD_append_right _ _ _ _ (by omega), hl, ← ih (fun l' hl' => h l'
        (List.mem_cons_of_mem _ hl')) (j - 27), look, look, getL_eq, getL_eq,
        show j / 27 = (j - 27) / 27 + 1 by omega, show j % 27 = (j - 27) % 27 by omega]
      rfl

private theorem getD_lt' {α : Type} {l : List α} {i : Nat} {a : α} (h : i < l.length) :
    l.getD i a = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

theorem witOK_eq (c : F4SylowCert) (T : List ℕ) (tl : ℕ → ℕ) (h : ∀ j, T.getD j 0 = tl j)
    (i : ℕ) (w : Wit) : c.witOK T i w = witL c.zl c.inv tl i w := by
  have hc : ∀ u, c.conjBits T i u = conjL c.inv tl i u := fun u => by
    rw [F4SylowCert.conjBits, conjL, F4SylowCert.invv, h, h, h]
  have hm : ∀ a b, F4SylowCert.commB T a b = commL tl a b := fun a b => by
    rw [F4SylowCert.commB, commL, h, h]
  cases w with
  | exc => rfl
  | conj4 u₀ u₁ u₂ u₃ =>
    simp only [F4SylowCert.witOK, witL, List.map_cons, List.map_nil, hc]
  | pair z x y => simp only [F4SylowCert.witOK, witL, hm]
  | cube z x => simp only [F4SylowCert.witOK, witL, hm, h]

set_option maxRecDepth 4000 in
theorem check_of (c : F4SylowCert) (GB : List ℕ) (TT : List (List ℕ))
    (hS : (decide (c.paths.length = 729) && decide (c.paths.getD 0 [] = []) &&
      (c.paths.all fun p => p.all fun k => decide (k < 6)) &&
      decide (c.zl.length < 243)) = true)
    (hL : (c.rt.length == 4374 && c.inv.length == 729 && c.wit.length == 729) = true)
    (hG : (GB == c.gbList) = true) (hT : chkTab c GB TT = true) (hN : chkNod TT = true)
    (hR : chkRt GB TT c.rt = true) (hI : chkInv TT c.inv = true)
    (hW : chkWit TT c.zl c.inv c.wit = true) : c.check = true := by
  simp only [Bool.and_eq_true, beq_iff_eq] at hS hL hG
  obtain ⟨⟨⟨hA, hB⟩, hC⟩, hZ⟩ := hS
  obtain ⟨⟨hLr, hLi⟩, hLw⟩ := hL
  simp only [chkTab, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hT
  obtain ⟨⟨-, hlen⟩, hflat⟩ := hT
  have hlook : ∀ j, (c.tabList GB).getD j 0 = look TT j := fun j => by
    rw [← hflat, look_eq TT hlen]
  rw [F4SylowCert.check]
  change c.checkWith c.gbList (c.tabList c.gbList) = true
  rw [← hG, F4SylowCert.checkWith]
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨hA, hB⟩, hC⟩, ?_⟩, ?_⟩, ?_⟩, hZ⟩, ?_⟩
  · rw [← hflat]
    exact decide_eq_true ((nodupN_eq _).mp hN)
  · simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true]
    intro i hi g hg
    have hn : 6 * i + g < c.rt.length := by omega
    have h := allIdx_spec _ _ _ hR _ hn
    rw [Nat.zero_add, Bool.and_eq_true, show (6 * i + g) / 6 = i by omega,
      show (6 * i + g) % 6 = g by omega] at h
    have hr : c.rtv i g = c.rt[6 * i + g] := getD_lt' hn
    rw [hr, hlook, hlook]
    exact ⟨decide_eq_true (by simpa using h.1), decide_eq_true (Nat.eq_of_beq_eq_true h.2)⟩
  · simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true]
    intro i hi
    have hn : i < c.inv.length := by omega
    have h := allIdx_spec _ _ _ hI _ hn
    rw [Nat.zero_add, Bool.and_eq_true] at h
    have hv : c.invv i = c.inv[i] := getD_lt' hn
    rw [hv, hlook, hlook]
    exact ⟨decide_eq_true (by simpa using h.1), decide_eq_true (Nat.eq_of_beq_eq_true h.2)⟩
  · simp only [List.all_eq_true, List.mem_range]
    intro i hi
    have hn : i < c.wit.length := by omega
    have hw : c.wit.getD i .exc = c.wit[i] := getD_lt' hn
    rw [hw, witOK_eq c _ (look TT) hlook]
    have := allIdx_spec _ _ _ hW _ hn
    rwa [Nat.zero_add] at this

end CFSG.KC.F4Three
