module

public import CFSG.Certificates.Kernel.Spor.PK.RawSim
public import CFSG.Certificates.Kernel.Spor.PK.RawTransfer
public import CFSG.Sporadic.Schreier.Enumeration

public section

namespace CFSG.KS.PK

open CFSG.Certificates CFSG.Sporadic.Schreier

variable {n : Nat}

theorem certificate_strong_toList (hn : 1 ≤ n) (gens : List (Equiv.Perm (Fin n)))
    (words : List (List Int)) {k : Nat} (base : Vector (Fin n) k) (hbase : base.toList.Nodup) :
    (certificate hn gens words base hbase).strong.toList = buildStrong gens words := by
  simp [certificate]

private theorem buildStrong_prefix (S : List (Equiv.Perm (Fin n))) (ws : List (List Int)) :
    ∃ T, buildStrong S ws = S ++ T := by
  induction ws generalizing S with
  | nil => exact ⟨[], by simp [buildStrong]⟩
  | cons w ws ih =>
    obtain ⟨T, hT⟩ := ih (S ++ [tab (evalCodes S w)])
    exact ⟨tab (evalCodes S w) :: T, by simp [buildStrong, hT]⟩

private theorem buildStrong_getD (S : List (Equiv.Perm (Fin n))) (ws : List (List Int)) :
    ∀ i < ws.length,
      (buildStrong S ws).getD (S.length + i) 1 =
        evalCodes ((buildStrong S ws).take (S.length + i)) (ws.getD i []) := by
  induction ws generalizing S with
  | nil => intro i hi; exact absurd hi (by simp)
  | cons w ws ih =>
    intro i hi
    obtain ⟨T, hT⟩ := buildStrong_prefix (S ++ [tab (evalCodes S w)]) ws
    cases i with
    | zero =>
      simp only [buildStrong, hT, Nat.add_zero, List.getD_cons_zero]
      have h1 : (S ++ [tab (evalCodes S w)] ++ T).getD S.length 1 = tab (evalCodes S w) := by
        simp [List.getD_eq_getElem?_getD]
      have h2 : List.take S.length (S ++ [tab (evalCodes S w)] ++ T) = S := by
        simp
      rw [h1, h2, tab_eq]
    | succ i =>
      have := ih (S ++ [tab (evalCodes S w)]) i (by simpa using hi)
      simp only [buildStrong]
      have e : S.length + (i + 1) = (S ++ [tab (evalCodes S w)]).length + i := by
        simp; omega
      rw [e]
      simpa using this

private theorem decodeWord_cons_of_lt (j : Nat) (z : Int) (w : List Int) (h : z.natAbs - 1 < j) :
    decodeWord j (z :: w) = (⟨z.natAbs - 1, h⟩, decide (0 < z)) :: decodeWord j w := by
  simp [decodeWord, decodeLetter, h]

private theorem decodeWord_cons_of_not_lt (j : Nat) (z : Int) (w : List Int)
    (h : ¬ z.natAbs - 1 < j) : decodeWord j (z :: w) = decodeWord j w := by
  simp [decodeWord, decodeLetter, h]

private theorem evalCodes_eq_schreierWordValue (S : List (Equiv.Perm (Fin n))) {r : Nat}
    (T : Fin r → Equiv.Perm (Fin n)) {j : Nat} (hj : j ≤ r) (hS : S.length = j)
    (hT : ∀ h : Fin r, h.val < j → T h = S.getD h.val 1) (w : List Int) :
    evalCodes S w = schreierWordValue T j hj (decodeWord j w) := by
  induction w with
  | nil => rfl
  | cons z w ih =>
    by_cases h : z.natAbs - 1 < j
    · rw [decodeWord_cons_of_lt j z w h, evalCodes, ih]
      by_cases hz : 0 < z
      · simp only [hz, decide_true, if_true, schreierWordValue_cons_positive]
        have e : z.toNat - 1 = z.natAbs - 1 := by omega
        rw [e, hT ⟨z.natAbs - 1, by omega⟩ h]
      · simp only [hz, decide_false, if_false, schreierWordValue_cons_negative]
        have e : (-z).toNat - 1 = z.natAbs - 1 := by omega
        rw [e, hT ⟨z.natAbs - 1, by omega⟩ h]
    · rw [decodeWord_cons_of_not_lt j z w h, evalCodes, ih]
      have h1 : z.natAbs - 1 ≥ S.length := by omega
      by_cases hz : 0 < z
      · have e : z.toNat - 1 = z.natAbs - 1 := by omega
        simp [hz, e, List.getD_eq_getElem?_getD, List.getElem?_eq_none h1]
      · have e : (-z).toNat - 1 = z.natAbs - 1 := by omega
        simp [hz, e, List.getD_eq_getElem?_getD, List.getElem?_eq_none h1]

private theorem certificate_strong_get (hn : 1 ≤ n) (gens : List (Equiv.Perm (Fin n)))
    (words : List (List Int)) {k : Nat} (base : Vector (Fin n) k) (hbase : base.toList.Nodup)
    (j : Fin (certificate hn gens words base hbase).strongCount) :
    (certificate hn gens words base hbase).strong.get j =
      (buildStrong gens words).getD j.val 1 := by
  have hj : j.val < (buildStrong gens words).length := by
    rw [length_buildStrong]; exact j.isLt
  simp [certificate, Vector.get, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  rfl

theorem certificate_initial (hn : 1 ≤ n) (gens : List (Equiv.Perm (Fin n)))
    (words : List (List Int)) {k : Nat} (base : Vector (Fin n) k) (hbase : base.toList.Nodup) :
    ∀ j : Fin (certificate hn gens words base hbase).originalCount,
      (certificate hn gens words base hbase).strong.get
          (Fin.castLE (certificate hn gens words base hbase).originalCount_le j) =
        (certificate hn gens words base hbase).original.get j := by
  intro j
  rw [certificate_strong_get]
  obtain ⟨T, hT⟩ := buildStrong_prefix gens words
  have hj : j.val < gens.length := j.isLt
  have e1 : (Fin.castLE (certificate hn gens words base hbase).originalCount_le j).val =
      j.val := rfl
  rw [e1, hT]
  simp [certificate, Vector.get, List.getD_eq_getElem?_getD, List.getElem?_append_left hj]
  rw [List.getElem?_eq_getElem hj]
  rfl

theorem certificate_words (hn : 1 ≤ n) (gens : List (Equiv.Perm (Fin n)))
    (words : List (List Int)) {k : Nat} (base : Vector (Fin n) k) (hbase : base.toList.Nodup) :
    ∀ (j : Fin (certificate hn gens words base hbase).strongCount)
      (hj : (certificate hn gens words base hbase).originalCount ≤ j.val),
      (certificate hn gens words base hbase).strong.get j =
        (certificate hn gens words base hbase).derivationValue j hj := by
  intro j hj
  have hjlt : j.val < gens.length + words.length := j.isLt
  obtain ⟨i, hi⟩ : ∃ i, j.val = gens.length + i := ⟨j.val - gens.length, by
    have : gens.length ≤ j.val := hj
    omega⟩
  have hiw : i < words.length := by omega
  have h1 := buildStrong_getD gens words i hiw
  rw [certificate_strong_get, hi, h1]
  show _ = schreierWordValue _ j.val _ (decodeWord j.val (words.getD (j.val - gens.length) []))
  have hi' : j.val - gens.length = i := by omega
  rw [hi', ← hi]
  refine evalCodes_eq_schreierWordValue _ _ _ ?_ ?_ _
  · rw [List.length_take, length_buildStrong]
    omega
  · intro h hh
    rw [certificate_strong_get]
    simp [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hh]

@[expose] def LettersOf (n : Nat) (F : Nat → Nat → Nat) (S : List (Equiv.Perm (Fin n))) : Prop :=
  ∀ j < S.length, IsPermN n (F (2 * j)) ∧ permOf n (F (2 * j)) = S.getD j 1 ∧
    ∀ x < n, F (2 * j + 1) x = finv n (F (2 * j)) x

private theorem mem_rawOf_strong (hn : 1 ≤ n) (F : Nat → Nat → Nat) (NL : Nat) {k : Nat}
    (bs : Vector (Fin n) k) (hbs : bs.toList.Nodup) (s : Equiv.Perm (Fin n)) :
    s ∈ (rawOf n hn F NL bs hbs).strong.toList ↔ ∃ l < NL, permOf n (F l) = s := by
  simp only [rawOf, Vector.toList_ofFn, List.mem_ofFn, Set.mem_range]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i.val, i.isLt, hi⟩
  · rintro ⟨l, hl, h⟩
    exact ⟨⟨l, hl⟩, h⟩

private theorem inv_fixes_iff (g : Equiv.Perm (Fin n)) (b : Fin n) : g⁻¹ b = b ↔ g b = b := by
  rw [Equiv.Perm.inv_def, Equiv.symm_apply_eq, eq_comm]

theorem levelSubgroup_certificate_eq (hn : 1 ≤ n) (gens : List (Equiv.Perm (Fin n)))
    (words : List (List Int)) {k : Nat} (base : Vector (Fin n) k) (hbase : base.toList.Nodup)
    {F : Nat → Nat → Nat} (hF : LettersOf n F (buildStrong gens words)) (i : Nat) :
    (certificate hn gens words base hbase).levelSubgroup i =
      (rawOf n hn F (2 * (gens.length + words.length)) base hbase).levelSubgroup i := by
  have hlen : (buildStrong gens words).length = gens.length + words.length :=
    length_buildStrong gens words
  unfold RawSchreierDatum.levelSubgroup
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro s hs
    obtain ⟨hs1, hs2⟩ := (RawSchreierDatum.mem_levelGenerators_iff _ _ _).1 hs
    rw [certificate_strong_toList] at hs1
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hs1
    refine Subgroup.subset_closure ((RawSchreierDatum.mem_levelGenerators_iff _ _ _).2 ⟨?_, hs2⟩)
    rw [mem_rawOf_strong]
    obtain ⟨-, h2, -⟩ := hF j hj
    refine ⟨2 * j, by omega, ?_⟩
    rw [h2, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
    rfl
  · rw [Subgroup.closure_le]
    intro s hs
    obtain ⟨hs1, hs2⟩ := (RawSchreierDatum.mem_levelGenerators_iff _ _ _).1 hs
    obtain ⟨l, hl, rfl⟩ := (mem_rawOf_strong hn F _ base hbase _).1 hs1
    have hj : l / 2 < (buildStrong gens words).length := by omega
    obtain ⟨hperm, hval, hinv⟩ := hF (l / 2) hj
    have hget : (buildStrong gens words).getD (l / 2) 1 = (buildStrong gens words)[l / 2] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
      rfl
    have hmem : (buildStrong gens words)[l / 2] ∈
        (certificate hn gens words base hbase).strong.toList := by
      rw [certificate_strong_toList]
      exact List.getElem_mem hj
    rcases Nat.mod_two_eq_zero_or_one l with h | h
    · have hFl : F l = F (2 * (l / 2)) := congrArg F (by omega)
      have hs : permOf n (F l) = (buildStrong gens words)[l / 2] := by
        rw [hFl, hval, hget]
      rw [hs] at hs2 ⊢
      exact Subgroup.subset_closure
        ((RawSchreierDatum.mem_levelGenerators_iff _ _ _).2 ⟨hmem, hs2⟩)
    · have hFl : F l = F (2 * (l / 2) + 1) := congrArg F (by omega)
      have hs : permOf n (F l) = ((buildStrong gens words)[l / 2])⁻¹ := by
        have e1 : permOf n (F l) = permOf n (finv n (F (2 * (l / 2)))) := by
          rw [hFl]
          exact permOf_congr hinv
        rw [e1, ← permOf_inv hperm, hval, hget]
      rw [hs] at hs2 ⊢
      refine Subgroup.inv_mem _ (Subgroup.subset_closure
        ((RawSchreierDatum.mem_levelGenerators_iff _ _ _).2 ⟨hmem, ?_⟩))
      intro b hb
      exact (inv_fixes_iff _ b).1 (hs2 b hb)

theorem check_certificate (hn : 1 ≤ n) (gens : List (Equiv.Perm (Fin n)))
    (words : List (List Int)) {k : Nat} (base : Vector (Fin n) k) (hbase : base.toList.Nodup)
    {F : Nat → Nat → Nat} (hF : LettersOf n F (buildStrong gens words))
    (hQ' : (rawOf n hn F (2 * (gens.length + words.length)) base hbase).check = true) :
    (certificate hn gens words base hbase).check = true :=
  check_of_levelSubgroup_eq hQ' rfl rfl (levelSubgroup_certificate_eq hn gens words base hbase hF)
    (certificate_initial hn gens words base hbase) (certificate_words hn gens words base hbase)

end CFSG.KS.PK

end
