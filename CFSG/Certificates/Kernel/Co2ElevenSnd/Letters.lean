module

public import Certificates.Data.Kernel.Co2Eleven
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co2SevenInputs
public import CFSG.Certificates.Kernel.Spor.TabWords
public import CFSG.Certificates.Kernel.Spor.RawDefs
import CFSG.Certificates.Kernel.Co2ElevenSnd.Pack

public section

namespace CFSG.KC.Co2Eleven.Snd

open CFSG.KC.Enum CFSG.KS CFSG.KC.Co2Eleven CFSG.KS.TW CFSG.Sporadic.Th.Native
  CFSG.Sporadic.Fi23.Native CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co2SevenNative
  CFSG.Perm.Native

@[expose] def wordLet (WV WVI : Nat → Nat) (l : Nat) : Nat :=
  if l % 2 = 0 then WV (l / 2) else WVI (l / 2)

theorem wordLet_even (WV WVI : Nat → Nat) (j : Nat) : wordLet WV WVI (2 * j) = WV j := by
  unfold wordLet
  rw [if_pos (by omega), show 2 * j / 2 = j by omega]

theorem wordLet_odd (WV WVI : Nat → Nat) (j : Nat) : wordLet WV WVI (2 * j + 1) = WVI j := by
  unfold wordLet
  rw [if_neg (by omega), show (2 * j + 1) / 2 = j by omega]

theorem tr_congr {n : Nat} {t : Table} {f g : Nat → Nat} (h : TR n t f)
    (e : ∀ x < n, f x = g x) : TR n t g :=
  ⟨h.1, fun i hi => by rw [← e i hi]; exact h.2 i hi⟩

theorem tr_unpack {P : Nat} (hP : ∀ x < 2300, ap12 P x < 2300) :
    TR 2300 ((CFSG.KS.Raw.unpack 2300 12 P).map UInt32.ofNat) (ap12 P) := by
  refine ⟨by simp [CFSG.KS.Raw.unpack], fun i hi => ⟨?_, hP i hi⟩⟩
  unfold ap
  rw [getElem!_pos _ i (by simpa [CFSG.KS.Raw.unpack] using hi), Array.getElem_map]
  simp only [CFSG.KS.Raw.unpack, Array.getElem_ofFn, UInt32.toNat_ofNat']
  have h2 : ap12 P i < 2 ^ 32 := by
    have := hP i hi
    omega
  exact Nat.mod_eq_of_lt h2

theorem tr_invT {P Q : Nat} {T : Table} (hT : TR 2300 T (ap12 P)) (h : perm12 P Q = true) :
    TR 2300 (invT 2300 T) (ap12 Q) :=
  invT_TR (by decide) hT fun i hi =>
    ⟨(perm12_inv h i hi).1, (perm12_inv h i hi).2, ((perm12_facts h).2.2 i hi).2⟩

theorem invOK_gen {P Q : Nat} {T : Table} (hT : TR 2300 T (ap12 P)) (h : perm12 P Q = true) :
    invOK 2300 T (invT 2300 T) = true :=
  invOK_of hT (tr_invT hT h) fun i hi => ((perm12_facts h).2.2 i hi).2

theorem lettersK_facts {A B : Nat} {WV WVI : Nat → Nat} {ws : List (List Int)}
    (h : lettersK A B WV WVI ws = true) :
    perm12 A (pinvS 2300 12 (mask 12) A) = true ∧ perm12 B (pinvS 2300 12 (mask 12) B) = true ∧
      ∀ j < ws.length, perm12 (WV j) (WVI j) = true ∧
        WV j = wordK A (pinvS 2300 12 (mask 12) A) B (pinvS 2300 12 (mask 12) B) WV WVI
          (ws.getD j []) := by
  unfold lettersK at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, Nat.beq_eq] at h
  obtain ⟨⟨hA, hB⟩, hW⟩ := h
  exact ⟨hA, hB, hW⟩

theorem tr_gens {A B : Nat} {T0 T1 : Table} (h0 : TR 2300 T0 (ap12 A))
    (h1 : TR 2300 T1 (ap12 B)) (hA : perm12 A (pinvS 2300 12 (mask 12) A) = true)
    (hB : perm12 B (pinvS 2300 12 (mask 12) B) = true) (WV WVI : Nat → Nat) {z : Int}
    (hz : z ≠ 0) (hz2 : z.natAbs ≤ 2) :
    TR 2300 (co2Gens T0 T1 z) (ap12 (letK A (pinvS 2300 12 (mask 12) A) B
      (pinvS 2300 12 (mask 12) B) WV WVI z)) := by
  have hc : z = 1 ∨ z = -1 ∨ z = 2 ∨ z = -2 := by omega
  rcases hc with rfl | rfl | rfl | rfl
  · simpa [co2Gens, letK] using h0
  · simpa [co2Gens, letK] using tr_invT h0 hA
  · simpa [co2Gens, letK] using h1
  · simpa [co2Gens, letK] using tr_invT h1 hB

private theorem tr_letter {Ai Bi A B : Nat} {WV WVI : Nat → Nat} {gens : Int → Table}
    {L : Array Table} {j : Nat}
    (hg : ∀ z : Int, z ≠ 0 → z.natAbs ≤ 2 → TR 2300 (gens z) (ap12 (letK A Ai B Bi WV WVI z)))
    (hL : ∀ l < 2 * j, TR 2300 L[l]! (ap12 (wordLet WV WVI l))) {z : Int} (hz : z ≠ 0)
    (hzj : z.natAbs ≤ 2 ∨ z.natAbs < j + 3) :
    TR 2300 (slpLetterT gens L z) (ap12 (letK A Ai B Bi WV WVI z)) := by
  unfold slpLetterT
  by_cases h2 : z.natAbs ≤ 2
  · rw [if_pos h2]
    exact hg z hz h2
  · rw [if_neg h2]
    have h3 : z.natAbs - 3 < j := by omega
    have n1 : z ≠ 1 := fun e => h2 (by rw [e]; decide)
    have n2 : z ≠ -1 := fun e => h2 (by rw [e]; decide)
    have n3 : z ≠ 2 := fun e => h2 (by rw [e]; decide)
    have n4 : z ≠ -2 := fun e => h2 (by rw [e]; decide)
    by_cases hp : 0 < z
    · rw [if_pos hp]
      have e : letK A Ai B Bi WV WVI z = WV (z.natAbs - 3) := by
        unfold letK
        rw [if_neg n1, if_neg n2, if_neg n3, if_neg n4, if_pos hp]
      rw [e, ← wordLet_even WV WVI]
      exact hL _ (by omega)
    · rw [if_neg hp]
      have e : letK A Ai B Bi WV WVI z = WVI (z.natAbs - 3) := by
        unfold letK
        rw [if_neg n1, if_neg n2, if_neg n3, if_neg n4, if_neg hp]
      rw [e, ← wordLet_odd WV WVI]
      exact hL _ (by omega)

private def stepS (gens : Int → Table) (L : Array Table) (w : List Int) : Array Table :=
  let T := wordT 2300 (slpLetterT gens L) w
  (L.push T).push (invT 2300 T)

private theorem push_get_lt {α : Type} [Inhabited α] (L : Array α) (a : α) {l : Nat}
    (hl : l < L.size) : (L.push a)[l]! = L[l]! := by
  rw [getElem!_pos _ l (by simp; omega), getElem!_pos _ l hl, Array.getElem_push_lt]

private theorem push_get_eq {α : Type} [Inhabited α] (L : Array α) (a : α) :
    (L.push a)[L.size]! = a := by
  rw [getElem!_pos _ L.size (by simp), Array.getElem_push_eq]

private theorem slp_take {Ai Bi A B : Nat} {WV WVI : Nat → Nat} {gens : Int → Table}
    {ws : List (List Int)}
    (hg : ∀ z : Int, z ≠ 0 → z.natAbs ≤ 2 → TR 2300 (gens z) (ap12 (letK A Ai B Bi WV WVI z)))
    (hs : ∀ j < ws.length, ∀ z ∈ ws.getD j [], z ≠ 0 ∧ (z.natAbs ≤ 2 ∨ z.natAbs < j + 3))
    (hW : ∀ j < ws.length, perm12 (WV j) (WVI j) = true ∧
      WV j = wordK A Ai B Bi WV WVI (ws.getD j [])) :
    ∀ j ≤ ws.length, ((ws.take j).foldl (stepS gens) #[]).size = 2 * j ∧
      ∀ l < 2 * j, TR 2300 ((ws.take j).foldl (stepS gens) #[])[l]! (ap12 (wordLet WV WVI l))
  | 0, _ => ⟨rfl, fun l hl => absurd hl (by omega)⟩
  | j + 1, hj => by
    obtain ⟨ih1, ih2⟩ := slp_take hg hs hW j (by omega)
    have hjl : j < ws.length := by omega
    have ht : ws.take (j + 1) = ws.take j ++ [ws.getD j []] := by
      rw [List.take_succ, List.getElem?_eq_getElem hjl, Option.toList_some,
        List.getD_eq_getElem _ _ hjl]
    rw [ht, List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize (ws.take j).foldl (stepS gens) #[] = L at ih1 ih2
    have hTw : TR 2300 (wordT 2300 (slpLetterT gens L) (ws.getD j []))
        (fun x => (ws.getD j []).foldr (fun z y => ap12 (letK A Ai B Bi WV WVI z) y) x) :=
      wordT_TR (by decide) (ws.getD j []) fun z hz =>
        tr_letter hg ih2 (hs j hjl z hz).1 (hs j hjl z hz).2
    have hT : TR 2300 (wordT 2300 (slpLetterT gens L) (ws.getD j [])) (ap12 (WV j)) :=
      tr_congr hTw fun x hx => by rw [(hW j hjl).2, ap12_wordK _ _ _ _ _ _ _ hx]
    have hU := tr_invT hT (hW j hjl).1
    refine ⟨by simp [stepS, ih1]; omega, fun l hl => ?_⟩
    show TR 2300 ((L.push _).push _)[l]! _
    by_cases h1 : l < 2 * j
    · rw [push_get_lt _ _ (by simp; omega), push_get_lt _ _ (by omega)]
      exact ih2 l h1
    · by_cases h2 : l = 2 * j
      · subst h2
        rw [push_get_lt _ _ (by simp; omega), ← ih1, push_get_eq, ih1, wordLet_even]
        exact hT
      · have h3 : l = 2 * j + 1 := by omega
        subst h3
        have h4 := push_get_eq (L.push (wordT 2300 (slpLetterT gens L) (ws.getD j [])))
          (invT 2300 (wordT 2300 (slpLetterT gens L) (ws.getD j [])))
        rw [Array.size_push, ih1] at h4
        rw [h4, wordLet_odd]
        exact hU

theorem slpLetters_TR {A B : Nat} {WV WVI : Nat → Nat} {T0 T1 : Table}
    {words : Array (List Int)} (h0 : TR 2300 T0 (ap12 A)) (h1 : TR 2300 T1 (ap12 B))
    (hs : slpOK words = true) (hl : lettersK A B WV WVI words.toList = true) :
    (slpLetters 2300 (co2Gens T0 T1) words).size = 2 * words.size ∧
      ∀ l < 2 * words.size,
        TR 2300 (slpLetters 2300 (co2Gens T0 T1) words)[l]! (ap12 (wordLet WV WVI l)) := by
  obtain ⟨hA, hB, hW⟩ := lettersK_facts hl
  have hlen : words.toList.length = words.size := Array.length_toList
  have hs' : ∀ j < words.toList.length, ∀ z ∈ words.toList.getD j [],
      z ≠ 0 ∧ (z.natAbs ≤ 2 ∨ z.natAbs < j + 3) := by
    intro j hj z hz
    unfold slpOK at hs
    rw [allIn_iff] at hs
    have h := hs j (by rw [← hlen]; exact hj)
    rw [getElem!_pos _ j (by rw [← hlen]; exact hj), ← Array.getElem_toList,
      ← List.getD_eq_getElem _ [] (by simpa using hj), List.all_eq_true] at h
    have h' := h z hz
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.or_eq_true, decide_eq_true_eq] at h'
    exact h'
  have e : slpLetters 2300 (co2Gens T0 T1) words =
      words.toList.foldl (stepS (co2Gens T0 T1)) #[] := by
    rw [Array.foldl_toList]
    rfl
  have key := slp_take (gens := co2Gens T0 T1) (fun z hz hz2 => tr_gens h0 h1 hA hB WV WVI hz hz2)
    hs' hW words.toList.length (Nat.le_refl _)
  rw [List.take_length] at key
  rw [e, ← hlen]
  exact key

private theorem arr_get_getD (a : Array Nat) (i : Nat) : a[i]! = a.toList.getD i 0 := by
  rw [← Array.getElem!_toList, List.getElem!_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  rfl

private theorem getD_mem_lt {l : List Nat} {i : Nat} (h : i < l.length) : l.getD i 0 ∈ l := by
  rw [List.getD_eq_getElem _ _ h]
  exact List.getElem_mem h

theorem subLetters_TR {L : Array Table} {WV WVI : Nat → Nat} {nw : Nat} {chain : Array Nat}
    (hL : ∀ l < 2 * nw, TR 2300 L[l]! (ap12 (wordLet WV WVI l)))
    (hc : ∀ c ∈ chain.toList, c < nw) :
    (subLetters L chain).size = 2 * chain.size ∧ ∀ l < 2 * chain.size,
      TR 2300 (subLetters L chain)[l]! (ap12 (chainLet WV WVI chain.toList l)) := by
  refine ⟨by simp [subLetters], fun l hl => ?_⟩
  have hl2 : l / 2 < chain.toList.length := by simp; omega
  have hcl : chain[l / 2]! < nw := by
    rw [arr_get_getD]
    exact hc _ (getD_mem_lt hl2)
  unfold subLetters
  rw [getElem!_pos _ l (by simpa using hl), Array.getElem_ofFn]
  unfold chainLet
  by_cases he : l % 2 = 0
  · simp only [he, if_true]
    rw [← arr_get_getD, ← wordLet_even WV WVI]
    exact hL _ (by omega)
  · simp only [he, if_false]
    rw [← arr_get_getD, ← wordLet_odd WV WVI]
    exact hL _ (by omega)

theorem iterAp_eq {Y : Table} {y : Nat} (hY : TR 2300 Y (ap12 y)) :
    ∀ (i : Nat) {x : Nat}, x < 2300 → iterAp Y i x = iterK y i x ∧ iterK y i x < 2300
  | 0, x, hx => ⟨rfl, hx⟩
  | i + 1, x, hx => by
    obtain ⟨e, h⟩ := iterAp_eq hY i hx
    have e1 : iterAp Y (i + 1) x = ap Y (iterAp Y i x) := rfl
    have e2 : iterK y (i + 1) x = ap12 y (iterK y i x) := rfl
    rw [e1, e2, e, (hY.2 _ h).1]
    exact ⟨rfl, (hY.2 _ h).2⟩

end CFSG.KC.Co2Eleven.Snd

end
