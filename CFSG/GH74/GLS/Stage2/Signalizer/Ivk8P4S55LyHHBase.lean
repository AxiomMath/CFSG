
module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55Heis
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55WordG
public import CFSG.Sporadic.Ly.Certificate
public import CFSG.Sporadic.Ly.SimpleBase

@[expose] public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.LyHH

open CFSG.Sporadic.Ly CFSG.Sporadic.Ly.HH
open CFSG.Sporadic.Ly.Native (nPts genTables)
open CFSG.Sporadic.Th CFSG.Perm
open CFSG.Sporadic.Th.Native (Table ap compT powT order3OK invOK invT wordT)
open CFSG.Sporadic.Fi23 (slpG slpG_eq rep_slpLetters)
open CFSG.Sporadic.Fi23.Native (slpOK slpLetters slpLetterT)
open CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.WordG

section

noncomputable def hhGs (j : ℕ) : J := slpG genG hhWords j

noncomputable def hhLetterG (z : ℤ) : J :=
  if z.natAbs ≤ 2 then genG z
  else if 0 < z then hhGs (z.natAbs - 3) else (hhGs (z.natAbs - 3))⁻¹

theorem hhLetterG_eq : hhLetterG = CFSG.Sporadic.Ly.Omega.slpLetter hhWords := by
  funext z
  unfold hhLetterG hhGs CFSG.Sporadic.Ly.Omega.slpLetter genG CFSG.Sporadic.Ly.Omega.seedLetter
  rfl

end

section

theorem hh_rels : ∀ r ∈ hhRels, wordG hhLetterG r.1 = wordG hhLetterG r.2 := by
  rw [hhLetterG_eq]
  exact CFSG.Sporadic.Ly.ly_word_facts.2.2.1

theorem hh_ne : ∀ r ∈ hhNe, wordG hhLetterG r.1 ≠ wordG hhLetterG r.2.1 := by
  rw [hhLetterG_eq]
  exact CFSG.Sporadic.Ly.ly_word_facts.2.2.2

theorem hhL1 : hhLetterG 1 = a := by simp [hhLetterG, genG]

theorem hhL5 : hhLetterG 5 = hhGs 2 := by simp [hhLetterG]

theorem hhL7 : hhLetterG 7 = hhGs 4 := by simp [hhLetterG]

theorem hhL8 : hhLetterG 8 = hhGs 5 := by simp [hhLetterG]

theorem hhL9 : hhLetterG 9 = hhGs 6 := by simp [hhLetterG]

theorem hhL10 : hhLetterG 10 = hhGs 7 := by simp [hhLetterG]

theorem hhLn7 : hhLetterG (-7) = (hhGs 4)⁻¹ := by simp [hhLetterG]

theorem hhLn8 : hhLetterG (-8) = (hhGs 5)⁻¹ := by simp [hhLetterG]

theorem hhLn9 : hhLetterG (-9) = (hhGs 6)⁻¹ := by simp [hhLetterG]

theorem hh_J :
    ∃ u e f d : J, u ^ 21 = 1 ∧ u ^ 7 ≠ 1 ∧ u ^ 3 ≠ 1 ∧ a * u = u * a ∧
      Heis.Rel e f d ∧ d = f * e * f⁻¹ * e⁻¹ ∧ u ^ 7 * e * (u ^ 7)⁻¹ = f ∧
      u ^ 7 * f * (u ^ 7)⁻¹ = e ^ 4 * f ^ 4 * d ^ 3 ∧ f ≠ e := by
  have R := hh_rels
  have N := hh_ne
  have hx : hhGs 5 = hhGs 2 ^ 7 := by
    have h := R ([8], List.replicate 7 5) (by decide +kernel)
    simp only [wordG_cons, wordG_nil, wordG_replicate, mul_one, hhL8, hhL5] at h
    exact h
  have hxe : hhGs 5 * hhGs 4 * (hhGs 5)⁻¹ = hhGs 6 := by
    have h := R ([9], [8, 7, -8]) (by decide +kernel)
    simp only [wordG_cons, wordG_nil, mul_one, hhL8, hhL9, hhL7, hhLn8] at h
    simpa only [mul_assoc] using h.symm
  have hd : hhGs 7 = hhGs 6 * hhGs 4 * (hhGs 6)⁻¹ * (hhGs 4)⁻¹ := by
    have h := R ([10], [9, 7, -9, -7]) (by decide +kernel)
    simp only [wordG_cons, wordG_nil, mul_one, hhL10, hhL9, hhL7, hhLn9, hhLn7] at h
    simpa only [mul_assoc] using h
  have hu21 : hhGs 2 ^ 21 = 1 := by
    have h := R (List.replicate 21 5, []) (by decide +kernel)
    simp only [wordG_nil, wordG_replicate, hhL5] at h
    exact h
  have hau : a * hhGs 2 = hhGs 2 * a := by
    have h := R ([1, 5], [5, 1]) (by decide +kernel)
    simp only [wordG_cons, wordG_nil, mul_one, hhL1, hhL5] at h
    exact h
  have he5 : hhGs 4 ^ 5 = 1 := by
    have h := R (List.replicate 5 7, []) (by decide +kernel)
    simp only [wordG_nil, wordG_replicate, hhL7] at h
    exact h
  have hde : hhGs 7 * hhGs 4 = hhGs 4 * hhGs 7 := by
    have h := R ([10, 7], [7, 10]) (by decide +kernel)
    simp only [wordG_cons, wordG_nil, mul_one, hhL10, hhL7] at h
    exact h
  have hdf : hhGs 7 * hhGs 6 = hhGs 6 * hhGs 7 := by
    have h := R ([10, 9], [9, 10]) (by decide +kernel)
    simp only [wordG_cons, wordG_nil, mul_one, hhL10, hhL9] at h
    exact h
  have hd5 : hhGs 7 ^ 5 = 1 := by
    have h := R (List.replicate 5 10, []) (by decide +kernel)
    simp only [wordG_nil, wordG_replicate, hhL10] at h
    exact h
  have hxf : hhGs 5 * hhGs 6 * (hhGs 5)⁻¹ = hhGs 4 ^ 4 * hhGs 6 ^ 4 * hhGs 7 ^ 3 := by
    have h := R ([8, 9, -8], List.replicate 4 7 ++ List.replicate 4 9 ++ List.replicate 3 10)
      (by decide +kernel)
    simp only [wordG_cons, wordG_nil, wordG_append, wordG_replicate, mul_one, hhL8, hhL9, hhLn8,
      hhL7, hhL10] at h
    simpa only [mul_assoc] using h
  have hu7 : hhGs 2 ^ 7 ≠ 1 := by
    have h := N (List.replicate 7 5, [], 0) (by decide +kernel)
    simp only [wordG_nil, wordG_replicate, hhL5] at h
    exact h
  have hu3 : hhGs 2 ^ 3 ≠ 1 := by
    have h := N (List.replicate 3 5, [], 0) (by decide +kernel)
    simp only [wordG_nil, wordG_replicate, hhL5] at h
    exact h
  have hfe : hhGs 6 ≠ hhGs 4 := by
    have h := N ([9], [7], 0) (by decide +kernel)
    simp only [wordG_cons, wordG_nil, mul_one, hhL9, hhL7] at h
    exact h
  refine ⟨hhGs 2, hhGs 4, hhGs 6, hhGs 7, hu21, hu7, hu3, hau, ⟨he5, ?_, hd5, hde, hdf, ?_⟩, hd,
    ?_, ?_, hfe⟩
  · rw [← hxe, conj_pow, he5]; group
  · rw [hd]; group
  · rw [← hx]; exact hxe
  · rw [← hx]; exact hxf

theorem hh_obstruction :
    ∃ x s : J, orderOf x = 3 ∧ orderOf s = 7 ∧ a * x = x * a ∧ a * s = s * a ∧ x * s = s * x ∧
      ∃ E : Subgroup J, IsPGroup 5 ↥E ∧ (∀ z ∈ E, x * z * x⁻¹ ∈ E) ∧ ∃ z ∈ E, x * z * x⁻¹ ≠ z := by
  obtain ⟨u, e, f, d, hu21, hu7, hu3, hau, hR, hd, hxe, hxf, hfe⟩ := hh_J
  exact Heis.obstruction_abs hR hu21 hu7 hu3 hau hd hxe hxf hfe

end

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.LyHH
