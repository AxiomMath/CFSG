module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Orders
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.CocodeMask
public import Certificates.Certificate450260
public import Certificates.Data.RouteP.M24Defect

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model

open Equiv CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Quasithin.H.Mathieu
open CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Native
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator
  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Fi24Three

@[expose] noncomputable def epsAt (k : ℕ) : Q3 := if h : k < 11 then epsElt ⟨k, h⟩ else 1

theorem epsAt_of_lt {k : ℕ} (h : k < 11) : epsAt k = epsElt ⟨k, h⟩ := dif_pos h

theorem epsAt_of_ge {k : ℕ} (h : 11 ≤ k) : epsAt k = 1 := dif_neg (by omega)

@[expose] noncomputable def epsListFrom : ℕ → ℕ → List Q3
  | 0, _ => []
  | k + 1, s => epsAt s :: epsListFrom k (s + 1)

@[expose] noncomputable def epsList : List Q3 := epsListFrom 11 0

@[expose] noncomputable def epsMask (m : ℕ) : Q3 := maskProd epsList m

theorem length_epsListFrom : ∀ k s : ℕ, (epsListFrom k s).length = k
  | 0, _ => rfl
  | k + 1, s => by simp [epsListFrom, length_epsListFrom k]

theorem mem_epsListFrom : ∀ k s : ℕ, ∀ x ∈ epsListFrom k s, ∃ i, x = epsAt i
  | 0, _, x, h => by simp [epsListFrom] at h
  | k + 1, s, x, h => by
    simp only [epsListFrom, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨s, rfl⟩
    · exact mem_epsListFrom k (s + 1) x h

theorem getD_epsListFrom :
    ∀ k s j : ℕ, (epsListFrom k s).getD j 1 = if j < k then epsAt (s + j) else 1
  | 0, s, j => by simp [epsListFrom]
  | k + 1, s, 0 => by simp [epsListFrom]
  | k + 1, s, j + 1 => by
    rw [epsListFrom, List.getD_cons_succ, getD_epsListFrom k (s + 1) j]
    have h : s + (j + 1) = s + 1 + j := by omega
    rw [h]
    by_cases hj : j < k
    · rw [if_pos hj, if_pos (by omega)]
    · rw [if_neg hj, if_neg (by omega)]

theorem length_epsList : epsList.length = 11 := length_epsListFrom 11 0

theorem mem_epsList {x : Q3} (hx : x ∈ epsList) : ∃ i, x = epsAt i := mem_epsListFrom 11 0 x hx

theorem getD_epsList {j : ℕ} (hj : j < 11) : epsList.getD j 1 = epsElt ⟨j, hj⟩ := by
  rw [epsList, getD_epsListFrom, if_pos hj, Nat.zero_add, epsAt_of_lt hj]

theorem epsAt_mem_E0 (k : ℕ) : epsAt k ∈ E0 := by
  by_cases h : k < 11
  · rw [epsAt_of_lt h]
    exact epsElt_mem_E0 _
  · rw [epsAt_of_ge (by omega)]
    exact E0.one_mem

theorem epsMask_zero : epsMask 0 = 1 := maskProd_zero _

theorem epsMask_mod (m : ℕ) : epsMask (m % 2 ^ 11) = epsMask m := by
  have h := maskProd_mod epsList m
  rwa [length_epsList] at h

theorem epsMask_mem_E0 (m : ℕ) : epsMask m ∈ E0 :=
  maskProd_mem E0 epsList (fun _ hg => by obtain ⟨i, rfl⟩ := mem_epsList hg; exact epsAt_mem_E0 i) m

section Certs


theorem epsAt_mul_self (k : ℕ) : epsAt k * epsAt k = 1 := by
  by_cases h : k < 11
  · rw [epsAt_of_lt h]
    exact epsElt_mul_self _
  · rw [epsAt_of_ge (by omega), one_mul]

theorem epsAt_comm (i j : ℕ) : epsAt i * epsAt j = epsAt j * epsAt i := by
  by_cases hi : i < 11 <;> by_cases hj : j < 11
  · rw [epsAt_of_lt hi, epsAt_of_lt hj]
    exact epsElt_comm _ _
  · rw [epsAt_of_ge (by omega : 11 ≤ j)]
    simp
  · rw [epsAt_of_ge (by omega : 11 ≤ i)]
    simp
  · rw [epsAt_of_ge (by omega : 11 ≤ i)]
    simp

theorem epsMask_xor (a b : ℕ) : epsMask (a ^^^ b) = epsMask a * epsMask b :=
  maskProd_xor epsList
    (fun _ hg => by
      obtain ⟨i, rfl⟩ := mem_epsList hg
      exact epsAt_mul_self i)
    (fun _ hg _ hh => by
      obtain ⟨i, rfl⟩ := mem_epsList hg
      obtain ⟨j, rfl⟩ := mem_epsList hh
      exact epsAt_comm i j) a b

theorem epsMask_mul_self (m : ℕ) : epsMask m * epsMask m = 1 := by
  rw [← epsMask_xor, Nat.xor_self, epsMask_zero]

theorem epsMask_inv (m : ℕ) : (epsMask m)⁻¹ = epsMask m :=
  inv_eq_of_mul_eq_one_right (epsMask_mul_self m)

theorem epsMask_two_pow {j : ℕ} (hj : j < 11) : epsMask (2 ^ j) = epsElt ⟨j, hj⟩ := by
  rw [epsMask, maskProd_two_pow, getD_epsList hj]

theorem exists_epsMask_of_mem_E0 {x : Q3} (hx : x ∈ E0) : ∃ m < 2 ^ 11, epsMask m = x := by
  refine Subgroup.closure_induction (p := fun x _ => ∃ m < 2 ^ 11, epsMask m = x) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨j, rfl⟩
    exact ⟨2 ^ j.val, Nat.pow_lt_pow_right (by norm_num) j.isLt, epsMask_two_pow j.isLt⟩
  · exact ⟨0, by norm_num, epsMask_zero⟩
  · rintro x y _ _ ⟨m, hm, rfl⟩ ⟨m', hm', rfl⟩
    exact ⟨m ^^^ m', Nat.xor_lt_two_pow hm hm', epsMask_xor m m'⟩
  · rintro x _ ⟨m, hm, rfl⟩
    exact ⟨m, hm, (epsMask_inv m).symm⟩

theorem epsMask_injOn {a b : ℕ} (ha : a < 2 ^ 11) (hb : b < 2 ^ 11)
    (h : epsMask a = epsMask b) : a = b := by
  haveI : Finite E0 := finite_and_card_E0_le.1
  let f : Fin (2 ^ 11) → ↥E0 := fun m => ⟨epsMask m, epsMask_mem_E0 m⟩
  have hsurj : Function.Surjective f := by
    rintro ⟨x, hx⟩
    obtain ⟨m, hm, rfl⟩ := exists_epsMask_of_mem_E0 hx
    exact ⟨⟨m, hm⟩, rfl⟩
  have hbij : Function.Bijective f :=
    hsurj.bijective_of_nat_card_le (by rw [Nat.card_eq_fintype_card, Fintype.card_fin, card_E0])
  exact congrArg Fin.val (hbij.1 (a₁ := ⟨a, ha⟩) (a₂ := ⟨b, hb⟩) (Subtype.ext h))

theorem E0_comm {x y : Q3} (hx : x ∈ E0) (hy : y ∈ E0) : x * y = y * x := by
  obtain ⟨m, -, rfl⟩ := exists_epsMask_of_mem_E0 hx
  obtain ⟨m', -, rfl⟩ := exists_epsMask_of_mem_E0 hy
  rw [← epsMask_xor, ← epsMask_xor, Nat.xor_comm]

theorem conj_epsMask (g : Q3) (cs : List ℕ)
    (hcs : epsList.map (fun x => g * x * g⁻¹) = cs.map epsMask) (m : ℕ) :
    g * epsMask m * g⁻¹ = epsMask (actM cs m) := by
  calc g * epsMask m * g⁻¹ = (MulAut.conj g).toMonoidHom (maskProd epsList m) := by
        simp [epsMask, MulAut.conj_apply]
    _ = maskProd (epsList.map (MulAut.conj g).toMonoidHom) m := (maskProd_map _ _ _).symm
    _ = maskProd (cs.map epsMask) m := by
        rw [← hcs]
        rfl
    _ = epsMask (actM cs m) := maskProd_map_actM epsMask epsMask_xor cs m

end Certs

theorem getElem_epsList {i : ℕ} (hi : i < epsList.length) : epsList[i] = epsAt i := by
  have h11 : i < 11 := by simpa [length_epsList] using hi
  rw [← List.getD_eq_getElem _ 1 hi, epsList, getD_epsListFrom, if_pos h11, Nat.zero_add]

theorem map_epsList_conj (g : Q3) {cs : List ℕ} (hcs : cs.length = 11)
    (h : ∀ j < 11, g * epsAt j * g⁻¹ = epsMask cs[j]!) :
    epsList.map (fun x => g * x * g⁻¹) = cs.map epsMask := by
  apply List.ext_getElem
  · simp [length_epsList, hcs]
  · intro i h1 h2
    have hi : i < 11 := by simpa [length_epsList] using h1
    simp only [List.getElem_map, getElem_epsList]
    rw [h i hi, getElem!_pos cs i (by simpa [hcs] using hi)]

structure CocodeParts (tabs : Array Table) : Prop where
  invA : invOK degree tabs[aReg]! (invT degree tabs[aReg]!) = true
  invB : invOK degree tabs[bReg]! (invT degree tabs[bReg]!) = true
  conjA : conjOK tabs (invT degree tabs[aReg]!) (invT degree tabs[bReg]!) 1 conjACols = true
  conjB : conjOK tabs (invT degree tabs[aReg]!) (invT degree tabs[bReg]!) 2 conjBCols = true
  rel : relOK tabs (invT degree tabs[aReg]!) (invT degree tabs[bReg]!) (relLetters ()) = true

theorem CocodeParts.of_cocodeOKAt {tabs : Array Table} (h : cocodeOKAt tabs = true) :
    CocodeParts tabs := by
  unfold cocodeOKAt at h
  simp only [Bool.and_eq_true, and_assoc] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

section Parts


theorem cocodeOK_eq_true : cocodeOK () = true :=
  Certificates.certificate450260

theorem cocodeParts : CocodeParts objTabs :=
  CocodeParts.of_cocodeOKAt cocodeOK_eq_true

end Parts

@[expose] noncomputable def cocodeG (l : ℤ) : Q3 :=
  if l = 1 then aElt else if l = -1 then aElt⁻¹ else if l = 2 then bElt else
  if l = -2 then bElt⁻¹ else if 3 ≤ l ∧ l < 14 then epsAt (l - 3).toNat else 1

theorem cocodeG_one : cocodeG 1 = aElt := by simp [cocodeG]

theorem cocodeG_neg_one : cocodeG (-1) = aElt⁻¹ := by simp [cocodeG]

theorem cocodeG_two : cocodeG 2 = bElt := by simp [cocodeG]

theorem cocodeG_neg_two : cocodeG (-2) = bElt⁻¹ := by simp [cocodeG]

theorem cocodeG_eps (s : ℕ) : cocodeG ((s : ℤ) + 3) = epsAt s := by
  unfold cocodeG
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  by_cases hs : s < 11
  · have h : ((s : ℤ) + 3 - 3).toNat = s := by omega
    rw [if_pos ⟨by omega, by omega⟩, h]
  · rw [if_neg (by omega), epsAt_of_ge (by omega)]

theorem wordG_append (u v : List ℤ) :
    wordG cocodeG (u ++ v) = wordG cocodeG u * wordG cocodeG v := by
  simp [wordG, List.map_append, List.prod_append]

theorem wordG_epsLetters : ∀ k s m : ℕ,
    wordG cocodeG (epsLetters k s m) = maskProd (epsListFrom k s) m
  | 0, s, m => by simp [epsLetters, epsListFrom, wordG]
  | k + 1, s, m => by
    rw [epsLetters, epsListFrom, maskProd_cons, wordG_append, wordG_epsLetters k (s + 1) (m / 2)]
    by_cases hm : m % 2 = 1
    · simp [hm, wordG, cocodeG_eps]
    · simp [hm, wordG]

theorem wordG_epsWord (m : ℕ) : wordG cocodeG (epsWord m) = epsMask m :=
  wordG_epsLetters 11 0 m

abbrev invTabA : Table := invT degree objTabs[aReg]!

abbrev invTabB : Table := invT degree objTabs[bReg]!

abbrev letterTabs : ℤ → Table := cocodeLetter objTabs invTabA invTabB

open CFSG.Sporadic.Bridge CFSG.Sporadic.Bridge.TwoGen Certificates.RouteP.M24Defect in
@[expose] def letterInt (l : ℕ × Bool) : ℤ :=
  if l.2 then (l.1 : ℤ) + 1 else -((l.1 : ℤ) + 1)

open CFSG.Sporadic.Bridge CFSG.Sporadic.Bridge.TwoGen Certificates.RouteP.M24Defect

theorem cocodeG_letterInt {l : ℕ × Bool} (hl : l.1 < 2) :
    cocodeG (letterInt l) = if l.2 then img2 aElt bElt l.1 else (img2 aElt bElt l.1)⁻¹ := by
  obtain ⟨i, s⟩ := l
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl <;> cases s
  · exact (cocodeG_neg_one)
  · exact cocodeG_one
  · exact cocodeG_neg_two
  · exact cocodeG_two

theorem wordG_map_letterInt : ∀ w : List (ℕ × Bool), (∀ l ∈ w, l.1 < 2) →
    wordG cocodeG (w.map letterInt) = wordProd (img2 aElt bElt) w
  | [], _ => by simp [wordG, wordProd]
  | l :: w, hw => by
    have ih := wordG_map_letterInt w fun l' hl' => hw l' (List.mem_cons_of_mem _ hl')
    simp only [List.map_cons, wordG, wordProd, List.prod_cons] at ih ⊢
    rw [ih, cocodeG_letterInt (hw l List.mem_cons_self)]

theorem relLetters_eq : relLetters () = relWords.map (List.map letterInt) := by decide +kernel

theorem length_relWords : relWords.length = 7 := rfl

theorem lt_two_of_mem_relWords : ∀ w ∈ relWords, ∀ l ∈ w, l.1 < 2 := by decide +kernel

section CertsAll


theorem rep_cocodeLetter (l : ℤ) : Rep 920808 (letterTabs l) (cocodeG l) := by
  have hp := cocodeParts
  unfold letterTabs cocodeLetter cocodeG
  split_ifs with h1 h2 h3 h4 h5
  · exact rep_aElt
  · exact Rep.inv_of_invOK rep_aElt hp.invA
  · exact rep_bElt
  · exact Rep.inv_of_invOK rep_bElt hp.invB
  · have hlt : (l - 3).toNat < 11 := by omega
    rw [epsAt_of_lt hlt]
    exact rep_epsElt ⟨(l - 3).toNat, hlt⟩
  · exact Rep.idT (by norm_num)

theorem rep_cocodeWord (w : List ℤ) : Rep 920808 (wordT degree letterTabs w) (wordG cocodeG w) :=
  Rep.wordT (by norm_num) w fun l _ => rep_cocodeLetter l

theorem eq_of_rep_eqTab {g h : Q3} {S T : Table} (hS : Rep 920808 S g) (hT : Rep 920808 T h)
    (hST : eqTab 920808 S T = true) : g = h := by
  apply eq_of_idx_eq
  intro i hi
  rw [← hS i hi, ← hT i hi]
  exact eqTab_iff.1 hST i hi

theorem wordG_conj_of_conjOK {c : ℤ} {cols : List ℕ}
    (h : conjOK objTabs invTabA invTabB c cols = true) {j : ℕ} (hj : j < 11) :
    wordG cocodeG [c, (j : ℤ) + 3, -c] = epsMask cols[j]! := by
  unfold conjOK at h
  have h1 := List.all_eq_true.1 h j (List.mem_range.2 hj)
  rw [← wordG_epsWord]
  exact eq_of_rep_eqTab (rep_cocodeWord _) (rep_cocodeWord _) h1

theorem aElt_mul_epsAt_mul_inv {j : ℕ} (hj : j < 11) :
    aElt * epsAt j * aElt⁻¹ = epsMask conjACols[j]! := by
  have h := wordG_conj_of_conjOK cocodeParts.conjA hj
  rw [← h]
  simp [wordG, cocodeG_one, cocodeG_neg_one, cocodeG_eps, mul_assoc]

theorem bElt_mul_epsAt_mul_inv {j : ℕ} (hj : j < 11) :
    bElt * epsAt j * bElt⁻¹ = epsMask conjBCols[j]! := by
  have h := wordG_conj_of_conjOK cocodeParts.conjB hj
  rw [← h]
  simp [wordG, cocodeG_two, cocodeG_neg_two, cocodeG_eps, mul_assoc]

theorem aElt_mul_epsMask_mul_inv (m : ℕ) :
    aElt * epsMask m * aElt⁻¹ = epsMask (actM conjACols m) :=
  conj_epsMask aElt conjACols
    (map_epsList_conj aElt (by decide) fun _ hj => aElt_mul_epsAt_mul_inv hj) m

theorem bElt_mul_epsMask_mul_inv (m : ℕ) :
    bElt * epsMask m * bElt⁻¹ = epsMask (actM conjBCols m) :=
  conj_epsMask bElt conjBCols
    (map_epsList_conj bElt (by decide) fun _ hj => bElt_mul_epsAt_mul_inv hj) m

theorem wordProd_relWords_getElem {i : ℕ} (hi : i < 7) :
    wordProd (img2 aElt bElt) relWords[i]! = epsMask relEps[i]! := by
  have h := cocodeParts.rel
  unfold relOK at h
  have h1 := List.all_eq_true.1 h i (List.mem_range.2 hi)
  have h2 := eq_of_rep_eqTab (rep_cocodeWord _) (rep_cocodeWord _) h1
  rw [wordG_epsWord, relLetters_eq,
    getElem!_pos (relWords.map (List.map letterInt)) i (by simp [length_relWords, hi]),
    List.getElem_map, ← getElem!_pos relWords i (by simp [length_relWords, hi]),
    wordG_map_letterInt _ (lt_two_of_mem_relWords _ (by
      rw [getElem!_pos relWords i (by simp [length_relWords, hi])]
      exact List.getElem_mem _))] at h2
  exact h2

theorem wordProd_relWords_mem_E0 {r : List (ℕ × Bool)} (hr : r ∈ relWords) :
    wordProd (img2 aElt bElt) r ∈ E0 := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hr
  have hi7 : i < 7 := by simpa [length_relWords] using hi
  have h := wordProd_relWords_getElem hi7
  rw [getElem!_pos relWords i hi] at h
  rw [h]
  exact epsMask_mem_E0 _

end CertsAll

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model
