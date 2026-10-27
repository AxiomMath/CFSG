module

public import CFSG.RankThree.PartOne.KS.RuFiveCentralizers
public import Certificates.Certificate24940
public import Certificates.Certificate24941

public section

namespace CFSG.EvenSporadicStandard.RuStd.S2

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Mathieu CFSG.RankThree.Native
open CFSG.RankThree.PartOne

noncomputable def signedWordP (n : ℕ) (gs : Array (Array ℕ)) (w : List (ℕ × Bool)) :
    Equiv.Perm (Fin n) :=
  (w.map fun l => if l.2 then permOfArr n gs[l.1]! else (permOfArr n gs[l.1]!)⁻¹).prod

theorem rep_signedWordA {n : ℕ} {gs : Array (Array ℕ)}
    (hv : ∀ k < gs.size, validA n gs[k]! = true) :
    ∀ w : List (ℕ × Bool), (∀ l ∈ w, l.1 < gs.size) →
      Rep n (signedWordA n gs w) (signedWordP n gs w)
  | [], _ => by simpa [signedWordA, signedWordP] using (rep_idA (n := n))
  | l :: w, hw => by
    have hl : l.1 < gs.size := hw l List.mem_cons_self
    have ih := rep_signedWordA hv w (fun l' hl' => hw l' (List.mem_cons_of_mem _ hl'))
    obtain ⟨k, b⟩ := l
    cases b
    · simp only [signedWordA, signedWordP, List.map_cons, List.prod_cons]
      exact rep_compA (rep_inv_of_validA (hv k hl)) ih
    · simp only [signedWordA, signedWordP, List.map_cons, List.prod_cons]
      exact rep_compA (rep_of_validA (hv k hl)) ih

theorem signedWordP_mem {n : ℕ} {gs : Array (Array ℕ)} :
    ∀ w : List (ℕ × Bool), (∀ l ∈ w, l.1 < gs.size) →
      signedWordP n gs w ∈ Subgroup.closure (permsA n gs)
  | [], _ => by simp [signedWordP]
  | l :: w, hw => by
    have hl : l.1 < gs.size := hw l List.mem_cons_self
    have ih := signedWordP_mem (n := n) (gs := gs) w
      (fun l' hl' => hw l' (List.mem_cons_of_mem _ hl'))
    obtain ⟨k, b⟩ := l
    have hk : permOfArr n gs[k]! ∈ Subgroup.closure (permsA n gs) :=
      Subgroup.subset_closure (mem_permsA hl)
    simp only [signedWordP, List.map_cons, List.prod_cons] at ih ⊢
    cases b
    · exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hk) ih
    · exact Subgroup.mul_mem _ hk ih

theorem ruFiveLine_comm_zero_one :
    ruFiveLine 0 * ruFiveLine 1 = ruFiveLine 1 * ruFiveLine 0 := by
  have h := Certificates.certificate24940
  simp only [ruFiveLinesCheck, Bool.and_eq_true] at h
  exact (commA_iff (rep_ruFiveLine 0) (rep_ruFiveLine 1)).1 h.1

theorem ruFiveLines_unique
    (j : Fin 31) (hrec : (ruFiveRecordOf j : ℕ) = 0)
    (hc : ruFiveLine j * ruFiveLine 1 = ruFiveLine 1 * ruFiveLine j) : j = 0 := by
  have h := Certificates.certificate24940
  simp only [ruFiveLinesCheck, Bool.and_eq_true] at h
  have hj := allLt_spec h.2 j.2
  simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true', beq_iff_eq] at hj
  have hcomm : commA 4060 ruFiveLines[(j : ℕ)]! ruFiveLines[1]! = true :=
    (commA_iff (rep_ruFiveLine j) (rep_ruFiveLine 1)).2 hc
  have hrec' : ruFiveRec.getD j 0 % 31 = 0 := hrec
  rcases hj with (h1 | h1) | h1
  · exact absurd hrec' h1
  · rw [hcomm] at h1
    exact absurd h1 (by simp)
  · exact Fin.ext h1

theorem ruFiveQ8_exists :
    ∃ i j : Equiv.Perm (Fin 4060), i ∈ ruFiveC0 ∧ j ∈ ruFiveC0 ∧ i ^ 4 = 1 ∧ i ^ 2 ≠ 1 ∧
      j ^ 2 = i ^ 2 ∧ j * i * j⁻¹ = i⁻¹ := by
  have h := Certificates.certificate24941
  simp only [ruFiveQ8Check, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨hvI, hvJ⟩, h4⟩, h2⟩, hj2⟩, hconj⟩ := h
  have hv : ∀ k < ruFiveC0Gens.size, validA 4060 ruFiveC0Gens[k]! = true :=
    fun k hk => enumOK_gens_valid ruFiveC0_enum hk
  have hsz : ruFiveC0Gens.size = 3 := by simp [ruFiveC0Gens]
  have hwI : ∀ l ∈ q8WordI, l.1 < ruFiveC0Gens.size := by
    intro l hl
    simp only [q8WordI, List.mem_singleton] at hl
    rw [hl, hsz]
    decide
  have hwJ : ∀ l ∈ q8WordJ, l.1 < ruFiveC0Gens.size := by
    intro l hl
    simp only [q8WordJ, List.mem_cons, List.not_mem_nil, or_false] at hl
    rw [hsz]
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have hI := rep_signedWordA hv q8WordI hwI
  have hJ := rep_signedWordA hv q8WordJ hwJ
  have eI : permOfArr 4060 (signedWordA 4060 ruFiveC0Gens q8WordI) =
      signedWordP 4060 ruFiveC0Gens q8WordI := RankThree.Native.permOfArr_eq_of_rep hI
  have eJ : permOfArr 4060 (signedWordA 4060 ruFiveC0Gens q8WordJ) =
      signedWordP 4060 ruFiveC0Gens q8WordJ := RankThree.Native.permOfArr_eq_of_rep hJ
  have hIinv := eI ▸ rep_inv_of_validA hvI
  have hJinv := eJ ▸ rep_inv_of_validA hvJ
  refine ⟨signedWordP 4060 ruFiveC0Gens q8WordI, signedWordP 4060 ruFiveC0Gens q8WordJ,
    signedWordP_mem q8WordI hwI, signedWordP_mem q8WordJ hwJ, ?_, ?_, ?_, ?_⟩
  · exact (eqA_iff (rep_powArr hI 4) rep_idA).1 h4
  · intro hc
    have := (eqA_iff (rep_powArr hI 2) rep_idA).2 hc
    rw [h2] at this
    exact Bool.false_ne_true this
  · exact ((eqA_iff (rep_powArr hI 2) (rep_powArr hJ 2)).1 hj2).symm
  · exact (eqA_iff (rep_compA (rep_compA hJ hI) hJinv) hIinv).1 hconj

end CFSG.EvenSporadicStandard.RuStd.S2
