module

public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.Fi7GenData
public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.Fi24FiveGen

public section

namespace CFSG.HardMathSupport.Dickson.I271.Fi7

open CFSG.Sporadic.Fi24 CFSG.Sporadic.Fi24.Native
open CFSG.Sporadic.Fi23 (slpG slpG_eq)
open CFSG.Sporadic.Th (wordG)

@[expose] noncomputable def letterG {G : Type*} [Group G] (gensG : ℤ → G)
    (words : Array (List ℤ)) (i : ℕ) (z : ℤ) : G :=
  if z.natAbs ≤ 2 then gensG z
  else if z.natAbs - 3 < i then
    (if 0 < z then slpG gensG words (z.natAbs - 3) else (slpG gensG words (z.natAbs - 3))⁻¹)
  else 1

theorem slpG_eq_letterG {G : Type*} [Group G] (gensG : ℤ → G) (words : Array (List ℤ)) (i : ℕ) :
    slpG gensG words i = wordG (letterG gensG words i) words[i]! :=
  slpG_eq gensG words i

private theorem getElem!_push' {α : Type*} [Inhabited α] (L : Array α) (x : α) {i : ℕ}
    (hi : i < L.size) : (L.push x)[i]! = L[i]! := by
  rw [getElem!_pos _ i (by simp; omega), Array.getElem_push_lt hi, getElem!_pos L i hi]


theorem sim_mGen {z : ℤ} (hz0 : z ≠ 0) (hz : z.natAbs ≤ 2) :
    Fi24Sim (mGen z) (genG z) ∧ Fi24Sim (mGen (-z)) (genG z)⁻¹ := by
  have hb : Fi24Sim (powW 781 (matB ()) 2) b⁻¹ := by
    have h := fi24Sim_pow 2 fi24Sim_b
    have hb2 : b ^ 2 = b⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← pow_succ, CFSG.Sporadic.Fi24.b_cube]
    rw [← hb2]
    exact h
  have ha : Fi24Sim (matA ()) a⁻¹ := by
    rw [a_inv]
    exact fi24Sim_a
  have ha' : Fi24Sim (matA ()) a⁻¹⁻¹ := by
    rw [inv_inv]
    exact fi24Sim_a
  have hb' : Fi24Sim (matB ()) b⁻¹⁻¹ := by
    rw [inv_inv]
    exact fi24Sim_b
  have hcases : z = 1 ∨ z = -1 ∨ z = 2 ∨ z = -2 := by omega
  have e1 : mGen 1 = matA () := by simp [mGen]
  have e2 : mGen (-1) = matA () := by simp [mGen]
  have e3 : mGen 2 = matB () := by simp [mGen]
  have e4 : mGen (-2) = powW 781 (matB ()) 2 := by simp [mGen]
  have g1 : genG 1 = a := by simp [genG]
  have g2 : genG (-1) = a⁻¹ := by simp [genG]
  have g3 : genG 2 = b := by simp [genG]
  have g4 : genG (-2) = b⁻¹ := by simp [genG]
  rcases hcases with rfl | rfl | rfl | rfl
  · rw [e1, e2, g1]
    exact ⟨fi24Sim_a, ha⟩
  · rw [neg_neg, e2, e1, g2]
    exact ⟨ha, ha'⟩
  · rw [e3, e4, g3]
    exact ⟨fi24Sim_b, hb⟩
  · rw [neg_neg, e4, e3, g4]
    exact ⟨hb, hb'⟩

theorem sim_idW : Fi24Sim (idW 781) 1 := by
  have h := fi24Sim_one
  have e : fi24Ops.one = idW 781 := by dsimp only [fi24Ops]
  rwa [e] at h

theorem sim_mul {X Y : Array W} {g h : J} (hX : Fi24Sim X g) (hY : Fi24Sim Y h) :
    Fi24Sim (mulW X Y) (g * h) :=
  fi24Sim_mul hX hY

theorem sim_pow {X : Array W} {g : J} (e : ℕ) (hX : Fi24Sim X g) : Fi24Sim (powW 781 X e) (g ^ e) :=
  fi24Sim_pow e hX

theorem sim_eq {X Y : Array W} {g h : J} (hX : Fi24Sim X g) (hY : Fi24Sim Y h)
    (hXY : eqRows 781 X Y = true) : g = h :=
  fi24Sim_eq hX hY (by dsimp only [fi24Ops]; exact hXY)

theorem sim_ne {X Y : Array W} {g h : J} (hX : Fi24Sim X g) (hY : Fi24Sim Y h)
    (hXY : eqRows 781 X Y = false) : g ≠ h :=
  fi24Sim_ne hX hY (by dsimp only [fi24Ops]; simp [hXY])

theorem sim_mProd_foldl {f : ℤ → Array W} {F : ℤ → J} (ls : List ℤ)
    (hf : ∀ z ∈ ls, Fi24Sim (f z) (F z)) {acc : Array W} {g : J} (hacc : Fi24Sim acc g) :
    Fi24Sim (ls.foldl (fun acc z => mulW acc (f z)) acc) (g * (ls.map F).prod) := by
  induction ls generalizing acc g with
  | nil => simpa using hacc
  | cons z ls ih =>
    simp only [List.foldl_cons, List.map_cons, List.prod_cons]
    have h1 : Fi24Sim (mulW acc (f z)) (g * F z) := fi24Sim_mul hacc (hf z List.mem_cons_self)
    have := ih (fun z' hz' => hf z' (List.mem_cons_of_mem _ hz')) h1
    rwa [mul_assoc] at this

theorem sim_mProd {f : ℤ → Array W} {F : ℤ → J} (w : List ℤ)
    (hf : ∀ z ∈ w, Fi24Sim (f z) (F z)) : Fi24Sim (mProd f w) (wordG F w) := by
  cases w with
  | nil =>
    simp only [mProd, wordG, List.map_nil, List.prod_nil]
    exact sim_idW
  | cons l ls =>
    unfold mProd wordG
    simpa using sim_mProd_foldl ls (fun z hz => hf z (List.mem_cons_of_mem _ hz))
      (hf l List.mem_cons_self)

theorem sim_mLetter {L : Array (Array W)} {i : ℕ} {words : Array (List ℤ)}
    (hL : ∀ k < i, Fi24Sim L[2 * k]! (slpG genG words k) ∧
      Fi24Sim L[2 * k + 1]! (slpG genG words k)⁻¹) {z : ℤ} (hz0 : z ≠ 0)
    (hz : z.natAbs ≤ 2 ∨ z.natAbs < i + 3) :
    Fi24Sim (mLetter L z) (letterG genG words i z) ∧
      Fi24Sim (mLetter L (-z)) (letterG genG words i z)⁻¹ := by
  by_cases h2 : z.natAbs ≤ 2
  · have hneg : (-z).natAbs ≤ 2 := by simpa using h2
    have := sim_mGen hz0 h2
    unfold mLetter letterG
    rw [if_pos h2, if_pos hneg, if_pos h2]
    exact this
  · have hk : z.natAbs - 3 < i := by omega
    have hneg : ¬ (-z).natAbs ≤ 2 := by simpa using h2
    obtain ⟨h1, h2'⟩ := hL _ hk
    unfold mLetter letterG
    rw [if_neg h2, if_neg hneg, if_neg h2, if_pos hk]
    simp only [Int.natAbs_neg]
    by_cases hpos : 0 < z
    · have hn : ¬ 0 < -z := by omega
      rw [if_pos hpos, if_neg hn, if_pos hpos]
      exact ⟨h1, h2'⟩
    · have hn : 0 < -z := by omega
      rw [if_neg hpos, if_pos hn, if_neg hpos, inv_inv]
      exact ⟨h2', h1⟩

theorem sim_mLetters {words : Array (List ℤ)} (hok : CFSG.Sporadic.Fi23.Native.slpOK words = true) :
    (mLetters words).size = 2 * words.size ∧ ∀ j < words.size,
      Fi24Sim (mLetters words)[2 * j]! (slpG genG words j) ∧
      Fi24Sim (mLetters words)[2 * j + 1]! (slpG genG words j)⁻¹ := by
  have hw : ∀ j < words.size, ∀ z ∈ words[j]!, z ≠ 0 ∧ (z.natAbs ≤ 2 ∨ z.natAbs < j + 3) := by
    intro j hj z hz
    unfold CFSG.Sporadic.Fi23.Native.slpOK at hok
    have := (CFSG.Sporadic.Th.allIn_eq_true.1 hok) j (Nat.zero_le _) hj
    rw [List.all_eq_true] at this
    have := this z hz
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.or_eq_true, decide_eq_true_eq] at this
    exact this
  unfold mLetters
  apply Array.foldl_induction (fun m (L : Array (Array W)) => L.size = 2 * m ∧ ∀ j < m,
    Fi24Sim L[2 * j]! (slpG genG words j) ∧ Fi24Sim L[2 * j + 1]! (slpG genG words j)⁻¹)
  · exact ⟨rfl, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  · intro i L hL
    obtain ⟨hsz, hent⟩ := hL
    have hwi : words[i.1]! = words[i] := by
      rw [getElem!_pos words i.1 i.2]
      rfl
    have hlet : ∀ z ∈ words[i], Fi24Sim (mLetter L z) (letterG genG words i z) ∧
        Fi24Sim (mLetter L (-z)) (letterG genG words i z)⁻¹ := by
      intro z hz
      obtain ⟨hz0, hz'⟩ := hw i.1 i.2 z (by rw [hwi]; exact hz)
      exact sim_mLetter hent hz0 hz'
    have hX : Fi24Sim (mWord L words[i]) (slpG genG words i) := by
      rw [slpG_eq_letterG, hwi]
      exact sim_mProd _ fun z hz => (hlet z hz).1
    have hY : Fi24Sim (mWordInv L words[i]) (slpG genG words i)⁻¹ := by
      rw [slpG_eq_letterG, hwi]
      have h := sim_mProd (f := fun z => mLetter L (-z))
        (F := fun z => (letterG genG words i z)⁻¹) (words[i]).reverse
        (fun z hz => (hlet z (List.mem_reverse.1 hz)).2)
      have e : wordG (fun z => (letterG genG words i z)⁻¹) (words[i]).reverse =
          (wordG (letterG genG words i) words[i])⁻¹ := by
        simp only [wordG, List.map_reverse, List.prod_inv_reverse, List.map_map]
        rfl
      rw [← e]
      exact h
    generalize mWord L words[i] = X at hX ⊢
    generalize mWordInv L words[i] = Y at hY ⊢
    have hext : ∀ k < L.size, ((L.push X).push Y)[k]! = L[k]! := by
      intro k hk
      rw [getElem!_push' _ _ (by simp; omega), getElem!_push' _ _ hk]
    have hT : ((L.push X).push Y)[2 * i.1]! = X := by
      rw [getElem!_push' _ _ (by simp; omega), getElem!_pos _ _ (by simp; omega)]
      simp [Array.getElem_push, hsz]
    have hTi : ((L.push X).push Y)[2 * i.1 + 1]! = Y := by
      rw [getElem!_pos _ _ (by simp; omega)]
      simp [Array.getElem_push, hsz]
    refine ⟨by simp [hsz]; ring, fun j hj => ?_⟩
    by_cases hji : j < i.1
    · rw [hext _ (by omega), hext _ (by omega)]
      exact hent j hji
    · obtain rfl : j = i.1 := by omega
      rw [hT, hTi]
      exact ⟨hX, hY⟩

end CFSG.HardMathSupport.Dickson.I271.Fi7
