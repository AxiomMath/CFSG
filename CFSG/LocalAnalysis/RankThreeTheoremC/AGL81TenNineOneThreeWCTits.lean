module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434RemTitsLocal
public import Certificates.Certificate5171
import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

namespace TenNineOneThree

open Subgroup CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.Schreier.Tits CFSG.RankThree.PartTwo.Sec4.Item434RemTits

section Fuse

@[expose] noncomputable def titsWx : Equiv.Perm (Fin 1755) := wordIn 13 titsT xWord

theorem titsWC_parts :
    lettersOK 13 xWord = true ∧ lettersOK 13 yWord = true ∧ lettersOK 13 zWord = true ∧
    lettersOK 13 (titsUWord ++ titsUInvWord) = true ∧
    eqA 1755 (wordArr 1755 titsDerivedArrs (titsUWord ++ titsUInvWord)) (idA 1755) = true ∧
    sylArrs.all (fun g => !(commA g titsYArr && commA g titsZArr) || eqA 1755 g (idA 1755) ||
      eqA 1755 g titsXArr || eqA 1755 g (compA 1755 titsXArr titsXArr)) = true ∧
    eqA 1755 titsYArr (idA 1755) = false ∧ eqA 1755 titsYArr titsXArr = false ∧
    eqA 1755 titsYArr (compA 1755 titsXArr titsXArr) = false := by
  have h := Certificates.certificate5171
  simp only [titsWCCheck, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem rep_titsX : Rep 1755 titsXArr titsWx := rep_wordArr_titsT titsWC_parts.1

theorem rep_titsY : Rep 1755 titsYArr (wordIn 13 titsT yWord) :=
  rep_wordArr_titsT titsWC_parts.2.1

theorem rep_titsZ : Rep 1755 titsZArr (wordIn 13 titsT zWord) :=
  rep_wordArr_titsT titsWC_parts.2.2.1

theorem titsY_eq :
    wordIn 13 titsT yWord =
      wordIn 13 titsT titsUWord * titsWx * (wordIn 13 titsT titsUWord)⁻¹ := by
  have hu : wordIn 13 titsT (titsUWord ++ titsUInvWord) = 1 :=
    eq_of_eqA (rep_wordArr_titsT titsWC_parts.2.2.2.1) rep_idA titsWC_parts.2.2.2.2.1
  rw [wordIn_append] at hu
  rw [yWord_eq, wordIn_append, wordIn_append, ← inv_eq_of_mul_eq_one_right hu]
  rfl

theorem wordIn_mem_sylGrp {w : List ℤ} (hw : w ∈ sylWords) : wordIn 13 titsT w ∈ sylGrp :=
  mem_sylGrp.2 (List.mem_map_of_mem hw)

theorem wordIn_nil' : wordIn 13 titsT ([] : List ℤ) = 1 := rfl

theorem titsY_mem : wordIn 13 titsT yWord ∈ sylGrp := by
  have h := wordIn_mem_sylGrp (w := (fun k => powWord xWord (k / 9) ++ powWord yWord (k / 3 % 3) ++
    powWord zWord (k % 3)) 3) (List.mem_map_of_mem (List.mem_range.2 (by norm_num)))
  simpa [powWord, wordIn_append, wordIn_nil'] using h

theorem titsZ_mem : wordIn 13 titsT zWord ∈ sylGrp := by
  have h := wordIn_mem_sylGrp (w := (fun k => powWord xWord (k / 9) ++ powWord yWord (k / 3 % 3) ++
    powWord zWord (k % 3)) 1) (List.mem_map_of_mem (List.mem_range.2 (by norm_num)))
  simpa [powWord, wordIn_append, wordIn_nil'] using h

theorem titsX_mem : titsWx ∈ sylGrp := by
  have h := wordIn_mem_sylGrp (w := (fun k => powWord xWord (k / 9) ++ powWord yWord (k / 3 % 3) ++
    powWord zWord (k % 3)) 9) (List.mem_map_of_mem (List.mem_range.2 (by norm_num)))
  simpa [powWord, wordIn_append, wordIn_nil', titsWx] using h

theorem eq_of_mem_sylGrp_comm {a : Equiv.Perm (Fin 1755)} (ha : a ∈ sylGrp)
    (hy : a * wordIn 13 titsT yWord = wordIn 13 titsT yWord * a)
    (hz : a * wordIn 13 titsT zWord = wordIn 13 titsT zWord * a) :
    a = 1 ∨ a = titsWx ∨ a = titsWx * titsWx := by
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 (mem_sylGrp.1 ha)
  have hr := rep_of_mem hw
  have h := List.all_eq_true.1 titsWC_parts.2.2.2.2.2.1 _ (List.mem_map_of_mem hw)
  rw [(commA_iff hr rep_titsY).2 hy, (commA_iff hr rep_titsZ).2 hz] at h
  simp only [Bool.and_self, Bool.not_true, Bool.false_or, Bool.or_eq_true] at h
  rcases h with (h | h) | h
  · exact Or.inl (eq_of_eqA hr rep_idA h)
  · exact Or.inr (Or.inl (eq_of_eqA hr rep_titsX h))
  · exact Or.inr (Or.inr (eq_of_eqA hr (rep_compA rep_titsX rep_titsX) h))

theorem mem_zpowers_titsX {g : Equiv.Perm (Fin 1755)} (hg : g ∈ zpowers titsWx) :
    g = 1 ∨ g = titsWx ∨ g = titsWx * titsWx := by
  have h3 : titsWx ^ 3 = 1 := by
    rw [pow_succ, pow_two]
    exact cube_of_mem_sylPerms (mem_sylGrp.1 titsX_mem)
  rcases (Nat.dvd_prime Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one h3) with h1 | h1
  · rw [orderOf_eq_one_iff] at h1
    rw [h1, zpowers_one_eq_bot, mem_bot] at hg
    exact Or.inl hg
  · rw [mem_zpowers_iff_mem_range_orderOf, h1] at hg
    simp only [Finset.mem_image, Finset.mem_range] at hg
    obtain ⟨i, hi, rfl⟩ := hg
    interval_cases i
    · exact Or.inl (pow_zero _)
    · exact Or.inr (Or.inl (pow_one _))
    · exact Or.inr (Or.inr (pow_two _))

theorem titsY_not_mem : wordIn 13 titsT yWord ∉ zpowers titsWx := by
  intro h
  obtain ⟨-, -, -, -, -, -, h1, h2, h3⟩ := titsWC_parts
  rcases mem_zpowers_titsX h with h | h | h
  · rw [(eqA_iff rep_titsY rep_idA).2 h] at h1; cases h1
  · rw [(eqA_iff rep_titsY rep_titsX).2 h] at h2; cases h2
  · rw [(eqA_iff rep_titsY (rep_compA rep_titsX rep_titsX)).2 h] at h3; cases h3

end Fuse

end TenNineOneThree

end CFSG.LocalAnalysis.RankThreeTheoremC
