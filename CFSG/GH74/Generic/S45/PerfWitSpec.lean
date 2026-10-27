module

public import CFSG.GH74.Generic.S45.PerfWitCheck
public import CFSG.GH74.Generic.S45.LModelWit
public import CFSG.Sporadic.SmallOddCore.CentSpec

public section

namespace CFSG.GH74.Generic.S45

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
open scoped commutatorElement

variable {n : ℕ}

@[expose] noncomputable def pwLetterG (n : ℕ) (gs : Array Table) (l : ℤ) : Equiv.Perm (Fin n) :=
  if 0 < l then tp n gs[l.toNat - 1]! else (tp n gs[l.natAbs - 1]!)⁻¹

theorem lettersOK_spec {k : ℕ} {w : List ℤ} (h : lettersOK k w = true) :
    ∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ k := by
  intro l hl
  have := List.all_eq_true.1 h l hl
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at this
  exact this

theorem rep_pwLetter {gs : Array Table} (hperm : ∀ g ∈ gs, permOK n g = true)
    (hinv : ∀ g ∈ gs, invOK n g (invT n g) = true) {l : ℤ} (hl0 : l ≠ 0)
    (hlk : l.natAbs ≤ gs.size) : Rep n (pwLetter n gs l) (pwLetterG n gs l) := by
  have hmem : ∀ j, j < gs.size → gs[j]! ∈ gs := fun j hj => getElem!_mem_array hj
  by_cases hl : 0 < l
  · have hj : l.toNat - 1 < gs.size := by omega
    simp only [pwLetter, pwLetterG, hl, ite_true]
    exact rep_tp (hperm _ (hmem _ hj))
  · have hj : l.natAbs - 1 < gs.size := by omega
    simp only [pwLetter, pwLetterG, hl, ite_false]
    exact Rep.inv_of_invOK (rep_tp (hperm _ (hmem _ hj))) (hinv _ (hmem _ hj))

theorem pwLetterG_neg (gs : Array Table) {l : ℤ} (hl0 : l ≠ 0) :
    pwLetterG n gs (-l) = (pwLetterG n gs l)⁻¹ := by
  by_cases hl : 0 < l
  · have h1 : ¬ 0 < -l := by omega
    simp only [pwLetterG, hl, h1, ite_true, ite_false]
    have : (-l).natAbs = l.toNat := by omega
    rw [this]
  · have h1 : 0 < -l := by omega
    simp only [pwLetterG, hl, h1, ite_true, ite_false, inv_inv]
    have : (-l).toNat = l.natAbs := by omega
    rw [this]

theorem wordG_invWord (gs : Array Table) {w : List ℤ} (hw : ∀ l ∈ w, l ≠ 0) :
    wordG (pwLetterG n gs) (invWord w) = (wordG (pwLetterG n gs) w)⁻¹ := by
  unfold wordG invWord
  rw [List.prod_inv_reverse, List.map_reverse, List.map_map, List.map_map]
  congr 2
  apply List.map_congr_left
  intro l hl
  simp only [Function.comp_apply]
  exact pwLetterG_neg gs (hw l hl)

theorem perfWitOK_spec (hn : n < 2 ^ 32) {gs : List Table} {W : PerfWit}
    (h : perfWitOK n gs W = true) :
    ⁅closure (tp n '' {x | x ∈ gs.toArray}), closure (tp n '' {x | x ∈ gs.toArray})⁆ =
        closure (tp n '' {x | x ∈ gs.toArray}) ∧
      ∃ x ∈ closure (tp n '' {x | x ∈ gs.toArray}), orderOf x = 4 := by
  set Q : Subgroup (Equiv.Perm (Fin n)) := closure (tp n '' {x | x ∈ gs.toArray}) with hQ
  simp only [perfWitOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨hlen, hgens⟩, hcomm⟩, hfour1⟩, hfour2⟩ := h
  have hsize : gs.toArray.size = gs.length := by simp
  have hperm : ∀ g ∈ gs.toArray, permOK n g = true := by
    intro g hg
    exact (hgens g (by simpa using hg)).1
  have hinv : ∀ g ∈ gs.toArray, invOK n g (invT n g) = true := by
    intro g hg
    exact (hgens g (by simpa using hg)).2
  have hLmem : ∀ l : ℤ, l ≠ 0 → l.natAbs ≤ gs.length → pwLetterG n gs.toArray l ∈ Q := by
    intro l hl0 hlk
    have hmem : ∀ j, j < gs.toArray.size → tp n gs.toArray[j]! ∈ Q := fun j hj =>
      subset_closure ⟨_, getElem!_mem_array hj, rfl⟩
    by_cases hl : 0 < l
    · have hj : l.toNat - 1 < gs.toArray.size := by rw [hsize]; omega
      simp only [pwLetterG, hl, ite_true]
      exact hmem _ hj
    · have hj : l.natAbs - 1 < gs.toArray.size := by rw [hsize]; omega
      simp only [pwLetterG, hl, ite_false]
      exact Q.inv_mem (hmem _ hj)
  have hword : ∀ w : List ℤ, (∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ gs.length) →
      wordG (pwLetterG n gs.toArray) w ∈ Q ∧
        Rep n (wordT n (pwLetter n gs.toArray) w) (wordG (pwLetterG n gs.toArray) w) := by
    intro w hw
    refine ⟨?_, Rep.wordT hn w fun l hl => rep_pwLetter hperm hinv (hw l hl).1 (by
      rw [hsize]; exact (hw l hl).2)⟩
    unfold wordG
    exact list_prod_mem (fun x hx => by
      obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hx
      exact hLmem l (hw l hl).1 (hw l hl).2)
  have hinvword : ∀ w : List ℤ, (∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ gs.length) →
      ∀ l ∈ invWord w, l ≠ 0 ∧ l.natAbs ≤ gs.length := by
    intro w hw l hl
    unfold invWord at hl
    obtain ⟨l', hl', rfl⟩ := List.mem_map.1 (List.mem_reverse.1 hl)
    exact ⟨by simpa using (hw l' hl').1, by simpa using (hw l' hl').2⟩
  refine ⟨le_antisymm ?_ ?_, ?_⟩
  · rw [commutator_le]
    intro a ha b hb
    exact Q.mul_mem (Q.mul_mem (Q.mul_mem ha hb) (Q.inv_mem ha)) (Q.inv_mem hb)
  · rw [hQ, closure_le]
    rintro _ ⟨g, hg, rfl⟩
    obtain ⟨i, hi, rfl⟩ : ∃ i, i < gs.length ∧ gs.toArray[i]! = g := by
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem (by simpa using hg)
      exact ⟨i, hi, by simp [getElem!_pos, hi]⟩
    obtain ⟨⟨hu, hv⟩, heq⟩ := hcomm i hi
    have hu' := lettersOK_spec hu
    have hv' := lettersOK_spec hv
    have hrepg : Rep n gs.toArray[i]! (tp n gs.toArray[i]!) :=
      rep_tp (hperm _ (getElem!_mem_array (by rw [hsize]; exact hi)))
    set u := (W.comms[i]!).1 with hudef
    set v := (W.comms[i]!).2 with hvdef
    obtain ⟨hmu, hru⟩ := hword u hu'
    obtain ⟨hmv, hrv⟩ := hword v hv'
    have hall : ∀ l ∈ u ++ v ++ invWord u ++ invWord v, l ≠ 0 ∧ l.natAbs ≤ gs.length := by
      intro l hl
      simp only [List.mem_append] at hl
      rcases hl with ((hl | hl) | hl) | hl
      · exact hu' l hl
      · exact hv' l hl
      · exact hinvword u hu' l hl
      · exact hinvword v hv' l hl
    obtain ⟨-, hrall⟩ := hword _ hall
    have heq' := (tblEq_iff_eq hrepg hrall).1 heq
    have hwu : wordG (pwLetterG n gs.toArray) (invWord u) = (wordG (pwLetterG n gs.toArray) u)⁻¹ :=
      wordG_invWord gs.toArray (fun l hl => (hu' l hl).1)
    have hwv : wordG (pwLetterG n gs.toArray) (invWord v) = (wordG (pwLetterG n gs.toArray) v)⁻¹ :=
      wordG_invWord gs.toArray (fun l hl => (hv' l hl).1)
    have hprod : wordG (pwLetterG n gs.toArray) (u ++ v ++ invWord u ++ invWord v) =
        ⁅wordG (pwLetterG n gs.toArray) u, wordG (pwLetterG n gs.toArray) v⁆ := by
      unfold wordG at hwu hwv ⊢
      simp only [List.map_append, List.prod_append, hwu, hwv, commutatorElement_def, mul_assoc]
    rw [heq', hprod]
    exact Subgroup.commutator_mem_commutator hmu hmv
  · have hf := lettersOK_spec hfour1
    obtain ⟨hmx, hrx⟩ := hword W.four hf
    exact ⟨_, hmx, (ordTest_iff_perm hrx (by norm_num)).1 hfour2⟩

theorem perfOrd4_of_perfWit (hn : n < 2 ^ 32) {G : Subgroup (Equiv.Perm (Fin n))}
    {t : Equiv.Perm (Fin n)} {gs : List Table} {W : PerfWit} (h : perfWitOK n gs W = true)
    (hC : closure (tp n '' {x | x ∈ gs.toArray}) = G ⊓ Subgroup.centralizer ({t} : Set _)) :
    PerfOrd4 G t := by
  obtain ⟨hperf, x, hx, hx4⟩ := perfWitOK_spec hn h
  exact ⟨_, hC.le, hperf, x, hx, hx4⟩

end CFSG.GH74.Generic.S45
