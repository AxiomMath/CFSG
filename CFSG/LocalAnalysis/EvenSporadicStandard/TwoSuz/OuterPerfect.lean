module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoSuz.Model
public import CFSG.Sporadic.SuzOddCore.InvPerms
public import Certificates.Certificate25030
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Suzuki

public section

namespace CFSG.EvenSporadicStandard.TwoSuz

open Subgroup CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.Tits
  CFSG.Sporadic.SuzOddCore CFSG.Sporadic.Recognition.SuzMultiplier
open CFSG.Sporadic.Bridge.SuzGPL.Native (surjWords)
open scoped commutatorElement

section Words

variable {H : Type*} [Group H]

@[expose] def outerEvalS (g : ℕ → H) (w : List ℤ) : H :=
  (w.map fun l => if 0 < l then g (l.natAbs - 1) else (g (l.natAbs - 1))⁻¹).prod

theorem outerEvalS_nil (g : ℕ → H) : outerEvalS g [] = 1 := rfl

theorem outerEvalS_cons (g : ℕ → H) (l : ℤ) (w : List ℤ) :
    outerEvalS g (l :: w) =
      (if 0 < l then g (l.natAbs - 1) else (g (l.natAbs - 1))⁻¹) * outerEvalS g w := by
  simp [outerEvalS]

theorem outerEvalS_append (g : ℕ → H) (u v : List ℤ) :
    outerEvalS g (u ++ v) = outerEvalS g u * outerEvalS g v := by
  simp [outerEvalS, List.prod_append]

theorem outerEvalS_invW (g : ℕ → H) :
    ∀ w : List ℤ, (∀ l ∈ w, l ≠ 0) → outerEvalS g (outerInvW w) = (outerEvalS g w)⁻¹
  | [], _ => by simp [outerInvW, outerEvalS_nil]
  | l :: w, hw => by
    have hl : l ≠ 0 := hw l List.mem_cons_self
    have ih := outerEvalS_invW g w fun l' hl' => hw l' (List.mem_cons_of_mem _ hl')
    have e : outerInvW (l :: w) = outerInvW w ++ [-l] := by simp [outerInvW]
    rw [e, outerEvalS_append, ih, outerEvalS_cons, outerEvalS_cons, outerEvalS_nil, mul_one,
      mul_inv_rev]
    congr 1
    by_cases hpos : 0 < l
    · have : ¬ 0 < -l := by omega
      rw [ite_eq_right this, ite_eq_left hpos, Int.natAbs_neg]
    · have : 0 < -l := by omega
      rw [ite_eq_left this, ite_eq_right hpos, Int.natAbs_neg, inv_inv]

theorem outerEvalS_congr {g g' : ℕ → H} {k : ℕ} (hg : ∀ i < k, g i = g' i) :
    ∀ {w : List ℤ}, lettersOK k w = true → outerEvalS g w = outerEvalS g' w
  | [], _ => rfl
  | l :: w, hw => by
    simp only [lettersOK, List.all_cons, Bool.and_eq_true, bne_iff_ne, ne_eq,
      decide_eq_true_eq] at hw
    obtain ⟨⟨hl0, hlk⟩, hw⟩ := hw
    have hw' : lettersOK k w = true := by simpa [lettersOK, List.all_eq_true] using hw
    have hi : l.natAbs - 1 < k := by omega
    rw [outerEvalS_cons, outerEvalS_cons, outerEvalS_congr hg hw', hg _ hi]

theorem map_outerEvalS {H' : Type*} [Group H'] (f : H →* H') (g : ℕ → H) (w : List ℤ) :
    f (outerEvalS g w) = outerEvalS (fun i => f (g i)) w := by
  induction w with
  | nil => simp [outerEvalS_nil]
  | cons l w ih =>
    rw [outerEvalS_cons, outerEvalS_cons, map_mul, ih]
    congr 1
    split_ifs <;> simp

theorem outerEvalS_mem {S : Subgroup H} {g : ℕ → H} {k : ℕ} (hg : ∀ i < k, g i ∈ S) :
    ∀ {w : List ℤ}, lettersOK k w = true → outerEvalS g w ∈ S
  | [], _ => S.one_mem
  | l :: w, hw => by
    simp only [lettersOK, List.all_cons, Bool.and_eq_true, bne_iff_ne, ne_eq,
      decide_eq_true_eq] at hw
    obtain ⟨⟨hl0, hlk⟩, hw⟩ := hw
    have hw' : lettersOK k w = true := by simpa [lettersOK, List.all_eq_true] using hw
    have hi : l.natAbs - 1 < k := by omega
    rw [outerEvalS_cons]
    refine S.mul_mem ?_ (outerEvalS_mem hg hw')
    split_ifs
    · exact hg _ hi
    · exact S.inv_mem (hg _ hi)

end Words

section Perm

theorem rep_outerEvalS {n j : ℕ} {S Sinv : Array (Array ℕ)} {gs : ℕ → Equiv.Perm (Fin n)}
    (hS : ∀ h < j, Rep n S[h]! (gs h)) (hSinv : ∀ h < j, Rep n Sinv[h]! (gs h)⁻¹) :
    ∀ w : List ℤ, lettersOK j w = true → Rep n (wordA n S Sinv w) (outerEvalS gs w)
  | [], _ => by simpa [wordA, outerEvalS_nil] using (rep_idA (n := n))
  | l :: w, hw => by
    simp only [lettersOK, List.all_cons, Bool.and_eq_true, bne_iff_ne, ne_eq,
      decide_eq_true_eq] at hw
    obtain ⟨⟨hl0, hlj⟩, hw⟩ := hw
    have hw' : lettersOK j w = true := by simpa [lettersOK, List.all_eq_true] using hw
    have ih := rep_outerEvalS hS hSinv w hw'
    have hlet := rep_letterA hS hSinv ⟨hl0, hlj⟩
    rw [wordA, outerEvalS_cons]
    by_cases hpos : 0 < l
    · rw [ite_eq_left (decide_eq_true hpos)] at hlet
      rw [ite_eq_left hpos]
      exact rep_compA hlet ih
    · rw [ite_eq_right (by simpa using hpos)] at hlet
      rw [ite_eq_right hpos]
      exact rep_compA hlet ih

end Perm

section Matrices

theorem GenSys.outer_letterU_odd (G : GenSys) (h : G.valid = true) (i : ℕ) :
    G.letterU h (2 * i + 1) = (G.letterU h (2 * i))⁻¹ := by
  refine Units.ext ?_
  have h1 : (2 * i + 1) % 2 = 1 := by omega
  have h2 : (2 * i + 1) / 2 = i := by omega
  have h3 : (2 * i) % 2 = 0 := by omega
  have h4 : (2 * i) / 2 = i := by omega
  simp only [GenSys.letterU, h1, h2, h3, h4, ite_true, one_ne_zero, ite_false]
  rfl

theorem GenSys.outer_val_letterU_even (G : GenSys) (h : G.valid = true) (s : ℕ) :
    ((G.letterU h (2 * s) : GL12) : Matrix (Fin 12) (Fin 12) (ZMod 3)) =
      ofMt (G.mats.getD s oneM) := by
  rw [GenSys.val_letterU]
  have h3 : (2 * s) % 2 = 0 := by omega
  have h4 : (2 * s) / 2 = s := by omega
  simp [GenSys.letter, h3, h4]

theorem GenSys.outer_letterU_zCode (G : GenSys) (h : G.valid = true) (l : ℤ) :
    G.letterU h (zCode l) =
      if 0 < l then G.letterU h (2 * (l.natAbs - 1)) else (G.letterU h (2 * (l.natAbs - 1)))⁻¹ := by
  by_cases hl : 0 < l
  · have e : zCode l = 2 * (l.natAbs - 1) := by
      simp only [zCode, hl, ite_true]
      omega
    rw [e, ite_eq_left hl]
  · have e : zCode l = 2 * (l.natAbs - 1) + 1 := by
      simp only [zCode, hl, ite_false]
      omega
    rw [e, GenSys.outer_letterU_odd, ite_eq_right hl]

theorem GenSys.outer_evalU_zCode (G : GenSys) (h : G.valid = true) (w : List ℤ) :
    G.evalU h (w.map zCode) = outerEvalS (fun i => G.letterU h (2 * i)) w := by
  induction w with
  | nil => simp [GenSys.evalU, outerEvalS_nil]
  | cons l w ih =>
    have : G.evalU h ((l :: w).map zCode) = G.letterU h (zCode l) * G.evalU h (w.map zCode) := by
      simp [GenSys.evalU]
    rw [this, ih, outerEvalS_cons, GenSys.outer_letterU_zCode]

theorem GenSys.outer_transfer (G : GenSys) (h : G.valid = true) {H : Type*} [Group H]
    (ψ : H →* GL12)
    {g : ℕ → H} {k : ℕ} (hg : ∀ i < k, ψ (g i) = G.letterU h (2 * i)) {w : List ℤ}
    (hw : lettersOK k w = true) : ψ (outerEvalS g w) = G.evalU h (w.map zCode) := by
  rw [GenSys.outer_evalU_zCode, map_outerEvalS]
  exact outerEvalS_congr hg hw

theorem GenSys.outerSub_mats_getD (G : GenSys) {n s : ℕ} (hs : s < n) (w : ℕ → List ℤ) :
    (G.outerSub n w).mats.getD s oneM = G.eval ((w s).map zCode) := by
  simp [GenSys.outerSub, hs]

theorem GenSys.outerSub_letterU (G : GenSys) (h : G.valid = true) {n : ℕ} (w : ℕ → List ℤ)
    (h' : (G.outerSub n w).valid = true) {s : ℕ} (hs : s < n) :
    (G.outerSub n w).letterU h' (2 * s) = G.evalU h ((w s).map zCode) := by
  refine Units.ext ?_
  rw [GenSys.outer_val_letterU_even, GenSys.outerSub_mats_getD G hs, GenSys.ofMt_eval G h]

end Matrices

section Block

theorem outerLvl0_mats_zero : outerLvl0.mats.getD 0 oneM = mulM negM matA := by simp [outerLvl0]

theorem outerLvl0_mats_one : outerLvl0.mats.getD 1 oneM = mulM negM matB := by simp [outerLvl0]

theorem exists_perfect_of_outerBlockOK {H : Type*} [Group H] {i : ℕ} {b : OuterBlock}
    (hb : outerBlockOK i b = true) (ψ : H →* GL12) (hψ : Function.Injective ψ) (a c : H)
    (ha : ((ψ a : GL12) : Matrix (Fin 12) (Fin 12) (ZMod 3)) = ofMt (mulM negM matA))
    (hc : ((ψ c : GL12) : Matrix (Fin 12) (Fin 12) (ZMod 3)) = ofMt (mulM negM matB))
    {t : H} (ht : ψ t = -1) (q : H →* Equiv.Perm (Fin 1782)) {τ : Equiv.Perm (Fin 1782)}
    (hτ : Rep 1782 (tArr i) τ) (hqa : Rep 1782 b0Arr (q a)) (hqc : Rep 1782 b1Arr (q c))
    (hinv0 : isInvA 1782 b0Arr (invCand 1782 b0Arr) = true)
    (hinv1 : isInvA 1782 b1Arr (invCand 1782 b1Arr) = true) :
    ∃ P : Subgroup H, P ≤ ⁅P, P⁆ ∧ t ∈ P ∧ ∀ p ∈ P, q p * τ = τ * q p := by
  simp only [outerBlockOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at hb
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, hlen1⟩, hlen2⟩, hgens⟩, huv⟩, hzs⟩, hneg⟩, hz⟩, hnegeq⟩ := hb
  set gensL : ℕ → H := fun j => if j = 0 then a else c with hgensL
  set ls : ℕ → H := fun s => outerEvalS gensL (b.gens.getD s []) with hls
  set cs : ℕ → H := fun j =>
    ⁅outerEvalS ls (b.us.getD j []), outerEvalS ls (b.vs.getD j [])⁆ with hcs
  have hU0 : ∀ j < 2, ψ (gensL j) = outerLvl0.letterU h0 (2 * j) := by
    intro j hj
    refine Units.ext ?_
    rw [GenSys.outer_val_letterU_even]
    interval_cases j
    · rw [outerLvl0_mats_zero]
      exact ha
    · rw [outerLvl0_mats_one]
      exact hc
  have hmemg : ∀ s < b.gens.length, b.gens.getD s [] ∈ b.gens := fun s hs => by
    rw [List.getD_eq_getElem _ _ hs]
    exact List.getElem_mem hs
  have hmemu : ∀ j < b.us.length, b.us.getD j [] ∈ b.us ++ b.vs := fun j hj => by
    rw [List.getD_eq_getElem _ _ hj]
    exact List.mem_append_left _ (List.getElem_mem hj)
  have hmemv : ∀ j < b.us.length, b.vs.getD j [] ∈ b.us ++ b.vs := fun j hj => by
    rw [List.getD_eq_getElem _ _ (hlen1 ▸ hj)]
    exact List.mem_append_right _ (List.getElem_mem _)
  have hmemz : ∀ s < b.gens.length, b.zs.getD s [] ∈ b.zs := fun s hs => by
    rw [List.getD_eq_getElem _ _ (hlen2 ▸ hs)]
    exact List.getElem_mem _
  have hψ1 : ∀ s < b.gens.length, ψ (ls s) = (outerLvl1 b).letterU h1 (2 * s) := by
    intro s hs
    have e : (outerLvl1 b).letterU h1 (2 * s) = outerLvl0.evalU h0 ((b.gens.getD s []).map zCode) :=
      GenSys.outerSub_letterU outerLvl0 h0 (fun s => b.gens.getD s []) h1 hs
    rw [e]
    exact GenSys.outer_transfer outerLvl0 h0 ψ hU0 (hgens _ (hmemg s hs)).1
  have hψ2 : ∀ j < b.us.length, ψ (cs j) = (outerLvl2 b).letterU h2 (2 * j) := by
    intro j hj
    have hA : ψ (outerEvalS ls (b.us.getD j [])) =
        outerEvalS (fun i => (outerLvl1 b).letterU h1 (2 * i)) (b.us.getD j []) := by
      rw [← GenSys.outer_evalU_zCode]
      exact GenSys.outer_transfer (outerLvl1 b) h1 ψ hψ1 (huv _ (hmemu j hj))
    have hB : ψ (outerEvalS ls (b.vs.getD j [])) =
        outerEvalS (fun i => (outerLvl1 b).letterU h1 (2 * i)) (b.vs.getD j []) := by
      rw [← GenSys.outer_evalU_zCode]
      exact GenSys.outer_transfer (outerLvl1 b) h1 ψ hψ1 (huv _ (hmemv j hj))
    have hnu : ∀ l ∈ b.us.getD j [], l ≠ 0 := by
      intro l hl
      have := huv _ (hmemu j hj)
      simp only [lettersOK, List.all_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq] at this
      exact (this l hl).1
    have hnv : ∀ l ∈ b.vs.getD j [], l ≠ 0 := by
      intro l hl
      have := huv _ (hmemv j hj)
      simp only [lettersOK, List.all_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq] at this
      exact (this l hl).1
    have e : (outerLvl2 b).letterU h2 (2 * j) = (outerLvl1 b).evalU h1
        ((outerCommW (b.us.getD j []) (b.vs.getD j [])).map zCode) :=
      GenSys.outerSub_letterU (outerLvl1 b) h1
        (fun j => outerCommW (b.us.getD j []) (b.vs.getD j [])) h2 hj
    rw [e, GenSys.outer_evalU_zCode, outerCommW, outerEvalS_append, outerEvalS_append,
      outerEvalS_append, outerEvalS_invW _ _ hnu, outerEvalS_invW _ _ hnv, hcs,
      map_commutatorElement, hA, hB, commutatorElement_def]
  have hzs' : ∀ s < b.gens.length, lettersOK b.us.length (b.zs.getD s []) = true :=
    fun s hs => hzs _ (hmemz s hs)
  have hperf : ∀ s < b.gens.length, ls s = outerEvalS cs (b.zs.getD s []) := by
    intro s hs
    apply hψ
    rw [hψ1 s hs, GenSys.outer_transfer (outerLvl2 b) h2 ψ hψ2 (hzs' s hs)]
    refine Units.ext ?_
    rw [GenSys.outer_val_letterU_even, ← GenSys.ofMt_eval (outerLvl2 b) h2, hz s hs]
  have ht' : t = outerEvalS ls b.neg := by
    apply hψ
    rw [ht, GenSys.outer_transfer (outerLvl1 b) h1 ψ hψ1 hneg]
    refine Units.ext ?_
    rw [← GenSys.ofMt_eval (outerLvl1 b) h1, hnegeq, ofMt_negM]
    rfl
  have hA : ∀ j < 2, Rep 1782 (#[b0Arr, b1Arr] : Array (Array ℕ))[j]! (q (gensL j)) := by
    intro j hj
    interval_cases j
    · exact hqa
    · exact hqc
  have hAinv : ∀ j < 2, Rep 1782 ((#[b0Arr, b1Arr] : Array (Array ℕ)).map (invCand 1782))[j]!
      (q (gensL j))⁻¹ := by
    intro j hj
    rw [getElem!_map_of_lt (by simp; omega)]
    interval_cases j
    · exact rep_inv_of_isInvA hqa hinv0
    · exact rep_inv_of_isInvA hqc hinv1
  have hcomm : ∀ s < b.gens.length, q (ls s) * τ = τ * q (ls s) := by
    intro s hs
    obtain ⟨hl2, hcm⟩ := hgens _ (hmemg s hs)
    have hrep : Rep 1782 (wordArr 1782 #[b0Arr, b1Arr] (b.gens.getD s []))
        (outerEvalS (fun j => q (gensL j)) (b.gens.getD s [])) := rep_outerEvalS hA hAinv _ hl2
    have h := eq_of_eqA (rep_compA hrep hτ) (rep_compA hτ hrep) hcm
    have hq : q (ls s) = outerEvalS (fun j => q (gensL j)) (b.gens.getD s []) :=
      map_outerEvalS q gensL _
    rw [hq]
    exact h
  set P : Subgroup H := Subgroup.closure {x | ∃ s < b.gens.length, x = ls s} with hP
  have hlsP : ∀ s < b.gens.length, ls s ∈ P := fun s hs => Subgroup.subset_closure ⟨s, hs, rfl⟩
  refine ⟨P, ?_, ?_, ?_⟩
  · rw [hP, Subgroup.closure_le]
    rintro _ ⟨s, hs, rfl⟩
    have hcs_mem : ∀ j < b.us.length, cs j ∈ ⁅P, P⁆ := fun j hj =>
      commutator_mem_commutator (outerEvalS_mem hlsP (huv _ (hmemu j hj)))
        (outerEvalS_mem hlsP (huv _ (hmemv j hj)))
    rw [hperf s hs]
    exact outerEvalS_mem hcs_mem (hzs' s hs)
  · rw [ht']
    exact outerEvalS_mem hlsP hneg
  · have hPC : P ≤ (Subgroup.centralizer ({τ} : Set (Equiv.Perm (Fin 1782)))).comap q := by
      rw [hP, Subgroup.closure_le]
      rintro _ ⟨s, hs, rfl⟩
      exact mem_centralizer_singleton_iff.2 (hcomm s hs)
    intro p hp
    exact mem_centralizer_singleton_iff.1 (hPC hp)

end Block

section Model

theorem outer_wordCodes_toLetters :
    ∀ w : List ℤ, lettersOK gcS w = true → wordCodes (toLetters gcS w) = w.map zCode
  | [], _ => rfl
  | l :: w, hw => by
    simp only [lettersOK, List.all_cons, Bool.and_eq_true, bne_iff_ne, ne_eq,
      decide_eq_true_eq] at hw
    obtain ⟨⟨hl0, hlj⟩, hw⟩ := hw
    have hw' : lettersOK gcS w = true := by simpa [lettersOK, List.all_eq_true] using hw
    have hcons : toLetters gcS (l :: w) =
        (⟨l.natAbs - 1, by omega⟩, decide (0 < l)) :: toLetters gcS w := by
      simp [toLetters, hl0, hlj]
    rw [hcons, List.map_cons]
    have ih := outer_wordCodes_toLetters w hw'
    simp only [wordCodes, List.map_cons] at ih ⊢
    rw [ih]
    congr 1
    by_cases hpos : 0 < l
    · simp only [zCode, hpos, decide_true, ite_true]
      omega
    · simp only [zCode, hpos, decide_false, ite_false, Bool.false_eq_true]
      omega

@[expose] def outerSurjFG (k : ℕ) : FreeGroup (Fin gcS) :=
  FreeGroup.mk (toLetters gcS surjWords[k]!)

section Twisted


theorem exists_twisted_gens {L : Type} [Group L] [Finite L] [Group.IsPerfect L]
    (q : L →* suzM) (hq : Function.Surjective q) {t : L} (ht : orderOf t = 2)
    (hker : q.ker = zpowers t) (hcen : zpowers t ≤ center L) :
    ∃ (ψ : L →* GL12) (a c : L), Function.Injective ψ ∧ ψ t = -1 ∧
      ((ψ a : GL12) : Matrix (Fin 12) (Fin 12) (ZMod 3)) = ofMt (mulM negM matA) ∧
      ((ψ c : GL12) : Matrix (Fin 12) (Fin 12) (ZMod 3)) = ofMt (mulM negM matB) ∧
      Rep 1782 b0Arr ((suzM.subtype.comp q) a) ∧ Rep 1782 b1Arr ((suzM.subtype.comp q) c) ∧
      isInvA 1782 b0Arr (invCand 1782 b0Arr) = true ∧
      isInvA 1782 b1Arr (invCand 1782 b1Arr) = true := by
  obtain ⟨φ, ψ, hφ, hψ, hqφ, hψφ, hψt⟩ := exists_embedding q hq ht hker hcen
  have hTab := Certificates.certificate15030
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := tab_facts hTab
  have hsw : ∀ k, k < 2 → surjWords.getD k [] = surjWords[k]! := fun k hk => by
    rw [Array.getD_eq_getD_getElem?, getElem!_pos surjWords k (by omega)]
    simp [h6, hk]
  have hb0 : wordIn 7 suzGenP surjWords[0]! = suzB0 :=
    eq_of_eqA (wordArr_surj hTab (by decide)) rep_b0 h9
  have hb1 : wordIn 7 suzGenP surjWords[1]! = suzB1 :=
    eq_of_eqA (wordArr_surj hTab (by decide)) rep_b1 h10
  have hq0 : ((q (φ (PresentedGroup.mk _ (outerSurjFG 0))) : suzM) : Equiv.Perm (Fin 1782)) =
      suzB0 := by
    rw [← MonoidHom.comp_apply, hqφ, suzπ_mk, coe_lift_suzGen]
    exact hb0
  have hq1 : ((q (φ (PresentedGroup.mk _ (outerSurjFG 1))) : suzM) : Equiv.Perm (Fin 1782)) =
      suzB1 := by
    rw [← MonoidHom.comp_apply, hqφ, suzπ_mk, coe_lift_suzGen]
    exact hb1
  have hψ0 : ((ψ (φ (PresentedGroup.mk _ (outerSurjFG 0))) : GL12) :
      Matrix (Fin 12) (Fin 12) (ZMod 3)) = ofMt (mulM negM matA) := by
    rw [← MonoidHom.comp_apply, hψφ, outerSurjFG, rho_mk, outer_wordCodes_toLetters _ h7,
      ← GenSys.ofMt_eval coverGS coverGS_valid, ← hsw 0 (by omega)]
    exact congrArg ofMt coverCheck_facts.2.2.2.2.2.1.symm
  have hψ1 : ((ψ (φ (PresentedGroup.mk _ (outerSurjFG 1))) : GL12) :
      Matrix (Fin 12) (Fin 12) (ZMod 3)) = ofMt (mulM negM matB) := by
    rw [← MonoidHom.comp_apply, hψφ, outerSurjFG, rho_mk, outer_wordCodes_toLetters _ h8,
      ← GenSys.ofMt_eval coverGS coverGS_valid, ← hsw 1 (by omega)]
    exact congrArg ofMt coverCheck_facts.2.2.2.2.2.2.symm
  have hr0 : Rep 1782 b0Arr
      ((suzM.subtype.comp q) (φ (PresentedGroup.mk _ (outerSurjFG 0)))) := by
    show Rep 1782 b0Arr
      ((q (φ (PresentedGroup.mk _ (outerSurjFG 0))) : suzM) : Equiv.Perm (Fin 1782))
    rw [hq0]
    exact rep_b0
  have hr1 : Rep 1782 b1Arr
      ((suzM.subtype.comp q) (φ (PresentedGroup.mk _ (outerSurjFG 1)))) := by
    show Rep 1782 b1Arr
      ((q (φ (PresentedGroup.mk _ (outerSurjFG 1))) : suzM) : Equiv.Perm (Fin 1782))
    rw [hq1]
    exact rep_b1
  exact ⟨ψ, _, _, hψ, hψt, hψ0, hψ1, hr0, hr1, isInvA_of_allPermsOK h1 (j := 0) (by decide),
    isInvA_of_allPermsOK h1 (j := 1) (by decide)⟩

end Twisted

section Embedding


theorem exists_perfect_outer_model {L : Type} [Group L] [Finite L] [Group.IsPerfect L]
    (q : L →* suzM) (hq : Function.Surjective q) {t : L} (ht : orderOf t = 2)
    (hker : q.ker = zpowers t) (hcen : zpowers t ≤ center L) {i : ℕ} (hi : i = 2 ∨ i = 3) :
    ∃ P : Subgroup L, P ≤ ⁅P, P⁆ ∧ t ∈ P ∧
      ∀ p ∈ P, (q p : Equiv.Perm (Fin 1782)) * suzInv i = suzInv i * (q p) := by
  obtain ⟨ψ, a, c, hψ, hψt, hψ0, hψ1, hr0, hr1, hinv0, hinv1⟩ :=
    exists_twisted_gens q hq ht hker hcen
  have hcert := Certificates.certificate25030
  simp only [outerCheck, Bool.and_eq_true] at hcert
  have hblk : outerBlockOK i (outerBlock i) = true := by
    rcases hi with rfl | rfl
    · exact hcert.1
    · exact hcert.2
  have hi4 : i < 4 := by omega
  exact exists_perfect_of_outerBlockOK hblk ψ hψ a c hψ0 hψ1 hψt (suzM.subtype.comp q)
    (rep_suzInv hi4) hr0 hr1 hinv0 hinv1

end Embedding

end Model

end CFSG.EvenSporadicStandard.TwoSuz
