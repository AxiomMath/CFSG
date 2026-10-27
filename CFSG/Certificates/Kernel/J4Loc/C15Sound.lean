module

public import CFSG.Certificates.Kernel.J4Loc.TrioOctSound
public import CFSG.Certificates.Kernel.J4Loc.SubsSound
public import Certificates.Data.Kernel.J4Loc.C15
public import Certificates.Data.J4Loc.TrioZ

public section

namespace CFSG.KS.J4Loc

open CFSG.KC.J4Q CFSG.KC.J4Loc CFSG.KC.Loop CFSG.Sporadic.J4.QT CFSG.Quasithin.J4Loc

theorem hasZ_iff (TK i : ℕ) : hasZ TK i = true ↔ 1131 ∈ octF TK i := by
  unfold hasZ octF
  rw [bitB_eq, mem_keyK, List.mem_toFinset]

section Sound

variable {TK TR N I0 : ℕ} (h : OctAll letterRows TK TR N I0)
include h

theorem wordF_idxW : ∀ (w : List ℕ), (∀ l ∈ w, l < 6) → ∀ i < N,
    idxW TR w i < N ∧ wordF letterRows w (octF TK i) = octF TK (idxW TR w i) := by
  intro w
  induction w with
  | nil => intro _ i hi; exact ⟨hi, rfl⟩
  | cons l w ih =>
    intro hw i hi
    obtain ⟨hj, he⟩ := (octOK_spec (h i hi)).2.2.2.1 l (hw l List.mem_cons_self)
    change idxW TR w _ < N ∧ wordF letterRows w ((octF TK i).image (actK (rowL letterRows l))) = _
    rw [he]
    exact ih (fun a ha => hw a (List.mem_cons_of_mem _ ha)) _ hj

variable (hLR : ∀ l < 6, (letterRows.getD l []).length = 11) (hI0 : I0 < N)
  (hV0 : octF TK I0 = V0F)
include hLR hI0 hV0

theorem trioZ_eq : TrioZ = octF TK '' {i | i < N ∧ hasZ TK i = true} := by
  ext W
  constructor
  · rintro ⟨hW, hz⟩
    rw [trioOct_eq h hLR hI0 hV0] at hW
    obtain ⟨i, hi, rfl⟩ := hW
    exact ⟨i, ⟨hi, (hasZ_iff TK i).2 hz⟩, rfl⟩
  · rintro ⟨i, ⟨hi, hz⟩, rfl⟩
    refine ⟨?_, (hasZ_iff TK i).1 hz⟩
    rw [trioOct_eq h hLR hI0 hV0]
    exact ⟨i, hi, rfl⟩

theorem trioZ_ncard : TrioZ.ncard = cntZ TK N := by
  have e : octF TK '' {i | i < N ∧ hasZ TK i = true} =
      ((((Finset.range N).filter fun i => hasZ TK i = true).image (octF TK) : Finset (Finset ℕ)) :
        Set (Finset ℕ)) := by
    ext
    simp
  rw [trioZ_eq h hLR hI0 hV0, e, Set.ncard_coe_finset,
    Finset.card_image_of_injOn (fun i hi j hj he => octF_inj h
      (Finset.mem_range.1 (Finset.mem_filter.1 hi).1) (Finset.mem_range.1 (Finset.mem_filter.1 hj).1)
      he)]
  have hc := rec_count_eq (hasZ TK) N
  change cntZ TK N = _ at hc
  rw [hc, Finset.card_def, Finset.filter_val, Finset.range_val, Multiset.range,
    Multiset.filter_coe, Multiset.coe_card]
  simp

theorem wordImgF_octF {ws : List ℕ} (hws : ∀ l ∈ ws, l < 6) {i : ℕ} (hi : i < N) :
    idxW TR ws i < N ∧
      wordImgF (ws.map fun l => letters.getD l 0) (octF TK i) = octF TK (idxW TR ws i) := by
  rw [← wordF_eq hLR ws hws]
  exact wordF_idxW h ws hws i hi

theorem c15K_sound {wa wb : List ℕ} (hwa : ∀ l ∈ wa, l < 6) (hwb : ∀ l ∈ wb, l < 6)
    (hc : c15K TK TR N wa wb = true) :
    let A := wordImgF (wa.map fun l => letters.getD l 0)
    let B := wordImgF (wb.map fun l => letters.getD l 0)
    TrioZ.ncard = 15 ∧
      (∀ W ∈ TrioZ, A (B W) = B (A W) ∧ A (A (A W)) = W ∧ B (B (B W)) = W) ∧
      ∃ W ∈ TrioZ, A W ≠ W ∧ B W ≠ W ∧ B W ≠ A W ∧ B W ≠ A (A W) := by
  intro A B
  obtain ⟨h1, h2⟩ := andB_true hc
  obtain ⟨h2, h3⟩ := andB_true h2
  have hA : ∀ i < N, idxW TR wa i < N ∧ A (octF TK i) = octF TK (idxW TR wa i) :=
    fun i hi => wordImgF_octF h hLR hI0 hV0 hwa hi
  have hB : ∀ i < N, idxW TR wb i < N ∧ B (octF TK i) = octF TK (idxW TR wb i) :=
    fun i hi => wordImgF_octF h hLR hI0 hV0 hwb hi
  have hW : ∀ W ∈ TrioZ, ∃ i < N, hasZ TK i = true ∧ W = octF TK i := by
    intro W hW
    rw [trioZ_eq h hLR hI0 hV0] at hW
    obtain ⟨i, ⟨hi, hz⟩, rfl⟩ := hW
    exact ⟨i, hi, hz, rfl⟩
  refine ⟨by rw [trioZ_ncard h hLR hI0 hV0]; exact Nat.eq_of_beq_eq_true h1, ?_, ?_⟩
  · intro W hW'
    obtain ⟨i, hi, hz, rfl⟩ := hW W hW'
    rcases orB_true (CFSG.KS.allN_spec h2 i hi) with hn | hz'
    · rw [notB_eq, hz] at hn
      exact absurd hn (by decide)
    unfold zOK at hz'
    rw [strictB_eq, strictB_eq] at hz'
    obtain ⟨e1, hz'⟩ := andB_true hz'
    obtain ⟨e2, e3⟩ := andB_true hz'
    obtain ⟨ha, ea⟩ := hA i hi
    obtain ⟨hb, eb⟩ := hB i hi
    obtain ⟨hab, eab⟩ := hA _ hb
    obtain ⟨hba, eba⟩ := hB _ ha
    obtain ⟨haa, eaa⟩ := hA _ ha
    obtain ⟨-, eaaa⟩ := hA _ haa
    obtain ⟨hbb, ebb⟩ := hB _ hb
    obtain ⟨-, ebbb⟩ := hB _ hbb
    refine ⟨?_, ?_, ?_⟩
    · rw [eb, eab, ea, eba, Nat.eq_of_beq_eq_true e1]
    · rw [ea, eaa, eaaa, Nat.eq_of_beq_eq_true e2]
    · rw [eb, ebb, ebbb, Nat.eq_of_beq_eq_true e3]
  · obtain ⟨i, hi, hz⟩ := anyK_spec h3
    obtain ⟨hz, hn⟩ := andB_true hz
    unfold neZ at hn
    rw [strictB_eq, strictB_eq] at hn
    obtain ⟨n1, hn⟩ := andB_true hn
    obtain ⟨n2, hn⟩ := andB_true hn
    obtain ⟨n3, n4⟩ := andB_true hn
    rw [notB_eq, Bool.not_eq_true'] at n1 n2 n3 n4
    replace n1 := Nat.ne_of_beq_eq_false n1
    replace n2 := Nat.ne_of_beq_eq_false n2
    replace n3 := Nat.ne_of_beq_eq_false n3
    replace n4 := Nat.ne_of_beq_eq_false n4
    obtain ⟨ha, ea⟩ := hA i hi
    obtain ⟨hb, eb⟩ := hB i hi
    obtain ⟨haa, eaa⟩ := hA _ ha
    have hZ : octF TK i ∈ TrioZ := by
      rw [trioZ_eq h hLR hI0 hV0]
      exact ⟨i, ⟨hi, hz⟩, rfl⟩
    refine ⟨octF TK i, hZ, ?_, ?_, ?_, ?_⟩
    · rw [ea]
      exact fun e => n1 (octF_inj h ha hi e)
    · rw [eb]
      exact fun e => n2 (octF_inj h hb hi e)
    · rw [eb, ea]
      exact fun e => n3 (octF_inj h hb ha e)
    · rw [eb, ea, eaa]
      exact fun e => n4 (octF_inj h hb haa e)

end Sound

end CFSG.KS.J4Loc

end
