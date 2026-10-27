module

public import Certificates.Data.Kernel.SmithL6KU
public import CFSG.Certificates.Kernel.SmithL6KOSound

public section

namespace CFSG.SmithL6.K

open CFSG.SmithL6 CFSG.SmithL6.Kernel

theorem parT_testBit : ∀ x < 64, parT.testBit x = par x := by decide +kernel

theorem conjF_eq (p q : Nat) : conjF p q = conjC p q := by
  have h1 : p % 64 &&& q / 64 < 64 := Nat.lt_of_le_of_lt Nat.and_le_left (Nat.mod_lt _ (by decide))
  have h2 : q % 64 &&& p / 64 < 64 := Nat.lt_of_le_of_lt Nat.and_le_left (Nat.mod_lt _ (by decide))
  unfold conjF conjC form
  rw [parT_testBit _ h1, parT_testBit _ h2]

theorem conjF_code {j a : Nat} (hj : j < 1953) (ha : a < 1953) :
    conjF (codeOf (tvPair j)) (codeOf (tvPair a)) = codeOf (tvPair (tvImg j a)) := by
  rw [conjF_eq, conjC_codeOf (tvP_tvPair hj) (tvP_tvPair ha), tvPair_tvImg hj ha]

theorem uaWC_cons (g : Nat) (G : List Nat) (a c : Nat) :
    uaWC (g :: G) a c = bif a.testBit 0 then conjF g (uaWC G (a / 2) c) else uaWC G (a / 2) c :=
  rfl

theorem uaWC_range' {T : List Nat} (hT : ∀ k < 1953, T.getD k 0 = codeOf (tvPair k)) (a : Nat) :
    ∀ n s, (∀ j, s ≤ j → j < s + n → ugens[j]! < 1953) → ∀ x < 1953,
      uaWC ((List.range' s n).map fun j => T.getD ugens[j]! 0) (a / 2 ^ s) (codeOf (tvPair x)) =
        codeOf (tvPair ((List.range' s n).foldr
          (fun j y => if a.testBit j then tvTab[ugens[j]!]![y]! else y) x)) ∧
      (List.range' s n).foldr (fun j y => if a.testBit j then tvTab[ugens[j]!]![y]! else y) x
        < 1953 := by
  intro n
  induction n with
  | zero => exact fun _ _ x hx => ⟨rfl, hx⟩
  | succ n ih =>
    intro s hs x hx
    obtain ⟨e, hlt⟩ := ih (s + 1) (fun j h1 h2 => hs j (by omega) (by omega)) x hx
    have hg := hs s (Nat.le_refl s) (by omega)
    have hdiv : a / 2 ^ s / 2 = a / 2 ^ (s + 1) := by
      rw [Nat.div_div_eq_div_mul, Nat.pow_succ]
    have hb : (a / 2 ^ s).testBit 0 = a.testBit s := by
      rw [Nat.testBit_div_two_pow, Nat.zero_add]
    rw [List.range'_succ, List.map_cons, List.foldr_cons, uaWC_cons, hb, hdiv, e]
    cases a.testBit s
    · exact ⟨rfl, hlt⟩
    · rw [cond_true, if_pos rfl, hT _ hg, conjF_code hg hlt, tvTab_get hg hlt]
      exact ⟨rfl, tvImg_lt hg hlt⟩

theorem ugens_toList : ugens.toList = (List.range' 0 9).map (ugens[·]!) := by decide +kernel

theorem uaWC_code {T : List Nat} (hT : ∀ k < 1953, T.getD k 0 = codeOf (tvPair k)) (a : Nat)
    {x : Nat} (hx : x < 1953) :
    uaWC (ugC T) a (codeOf (tvPair x)) = codeOf (tvPair (uaWord a x)) ∧ uaWord a x < 1953 := by
  have h := uaWC_range' hT a 9 0 (fun j _ h2 => ugens_lt j (by omega)) x hx
  rw [Nat.pow_zero, Nat.div_one] at h
  unfold ugC uaWord
  rw [ugens_toList, List.map_map, List.range_eq_range']
  exact h

theorem code_mem {T : List Nat} (hl : T.length = 1953)
    (hT : ∀ k < 1953, T.getD k 0 = codeOf (tvPair k)) {x : Nat} (hx : x < 1953) :
    codeOf (tvPair x) ∈ T := by
  rw [← hT x hx, getD_of_lt (by rw [hl]; exact hx)]
  exact List.getElem_mem _

theorem uaRowsC_sound {T : List Nat} (hl : T.length = 1953)
    (hT : ∀ k < 1953, T.getD k 0 = codeOf (tvPair k)) {R : List (Nat × Nat)}
    (h : uaRowsC (ugC T) T R = true) {u p : Nat} (hr : (u, codeOf (tvPair p)) ∈ R)
    (hp : p < 1953) {x : Nat} (hx : x < 1953) : uaWord u x = tvImg p x := by
  have h1 := List.all_eq_true.mp h _ hr
  have h2 := beq_iff_eq.mp (List.all_eq_true.mp h1 _ (code_mem hl hT hx))
  obtain ⟨e, hlt⟩ := uaWC_code hT u hx
  dsimp only at h2
  rw [e, conjF_code hp hx] at h2
  exact codeOf_tvPair_inj hlt (tvImg_lt hp hx) h2

theorem uaFixC_sound {T P : List Nat} (hT : ∀ k < 1953, T.getD k 0 = codeOf (tvPair k))
    (h : uaFixC T P = true) (hP : ∀ p ∈ P, p < 1953) {p q : Nat} (hp : p ∈ P) (hq : q ∈ P) :
    tvImg p q = q := by
  unfold uaFixC at h
  have h1 := List.all_eq_true.mp h _ (List.mem_map.mpr ⟨p, hp, rfl⟩)
  have h2 := beq_iff_eq.mp (List.all_eq_true.mp h1 _ (List.mem_map.mpr ⟨q, hq, rfl⟩))
  have hp' := hP p hp
  have hq' := hP q hq
  rw [hT p hp', hT q hq', conjF_code hp' hq'] at h2
  exact codeOf_tvPair_inj (tvImg_lt hp' hq') hq' h2

theorem uaMoveC_sound {T : List Nat} (hl : T.length = 1953)
    (hT : ∀ k < 1953, T.getD k 0 = codeOf (tvPair k)) (h : uaMoveC (ugC T) T = true) {a : Nat}
    (ha : a < 512) : a = 0 ∨ ∃ x < 1953, uaWord a x ≠ x := by
  have h1 := List.all_eq_true.mp h a (List.mem_range.mpr ha)
  rw [Bool.or_eq_true, beq_iff_eq] at h1
  rcases h1 with h1 | h1
  · exact Or.inl h1
  obtain ⟨c, hc, hne⟩ := List.any_eq_true.mp h1
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
  have hi' : i < 1953 := by rw [hl] at hi; exact hi
  rw [← getD_of_lt (d := 0) hi, hT i hi', (uaWC_code hT a hi').1, bne_iff_ne] at hne
  exact Or.inr ⟨i, hi', fun e => hne (by rw [e])⟩

theorem uaCommC_sound {T P : List Nat} (hl : T.length = 1953)
    (hT : ∀ k < 1953, T.getD k 0 = codeOf (tvPair k)) (h : uaCommC T P = true)
    (hP : ∀ p ∈ P, p < 1953) {q : Nat} (hq : q < 1953) (hfix : ∀ p ∈ P, tvImg p q = q) :
    q ∈ P := by
  unfold uaCommC at h
  have hq' : q < T.zipIdx.length := by rw [List.length_zipIdx, hl]; exact hq
  have hm := List.getElem_mem hq'
  rw [List.getElem_zipIdx] at hm
  have h1 := List.all_eq_true.mp h _ hm
  have ec : T[q]'(by rw [hl]; exact hq) = codeOf (tvPair q) := by
    rw [← getD_of_lt (d := 0) (by rw [hl]; exact hq), hT q hq]
  dsimp only at h1
  rw [Nat.zero_add, ec, Bool.or_eq_true, Bool.not_eq_true', List.contains_iff_mem] at h1
  rcases h1 with h1 | h1
  · have hall : ((P.map (T.getD · 0)).all fun p => conjF p (codeOf (tvPair q)) == codeOf (tvPair q))
        = true := by
      refine List.all_eq_true.mpr fun c hc => ?_
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hc
      rw [hT p (hP p hp), conjF_code (hP p hp) hq, hfix p hp]
      exact beq_self_eq_true _
    rw [hall] at h1
    exact absurd h1 (by decide)
  · exact h1

end CFSG.SmithL6.K
