module

public import CFSG.Sporadic.J4.QTOutNorm
public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.Local

public section

namespace CFSG.EvenSporadicStandard.J4Std.DataMod

open Subgroup CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT

theorem Hloc_top_eq (hF : J4Facts) :
    Hloc (⊤ : Subgroup J) (Eg uJ 11) = Hj := by
  rw [Hloc, inf_top_eq]
  exact normalizer_Eg_eq_Hj hF

theorem wordProd_conj (hM : MatFacts) {W : List ℤ}
    (hW : ∀ ℓ ∈ W, ℓ ∈ letters) (c : ℕ) :
    wordProd xJ W * eta uJ 11 c * (wordProd xJ W)⁻¹ = eta uJ 11 (W.foldr act c) := by
  rw [wordProd_xJ]
  exact word_conj XJ act W (fun ℓ hℓ c => hX_all hM (hW ℓ hℓ) c) c

theorem exists_Hconj_of_word (hM : MatFacts) {W : List ℤ}
    (hW : ∀ ℓ ∈ W, ℓ ∈ letters) {c c' : ℕ} (h : W.foldr act c = c') :
    ∃ k ∈ Hj, k * eta uJ 11 c * k⁻¹ = eta uJ 11 c' :=
  ⟨wordProd xJ W, wordProd_mem_Hj hW, by rw [wordProd_conj hM hW, h]⟩

theorem orbit_root_cases : ∀ o ∈ orbits, o.1 = 1 ∨ o.1 = 3 := by
  intro o ho
  have h : orbits.map Prod.fst = [1, 3] := rfl
  have h1 : o.1 ∈ orbits.map Prod.fst := List.mem_map_of_mem ho
  rw [h] at h1
  simpa using h1

theorem exists_Hconj_root (hM : MatFacts) {c : ℕ} (hc0 : c ≠ 0)
    (hc : c < 2 ^ 11) :
    ∃ r, (r = 1 ∨ r = 3) ∧ ∃ k ∈ Hj, k * eta uJ 11 r * k⁻¹ = eta uJ 11 c := by
  obtain ⟨o, ho, p, hp, hpc⟩ := orbit_cover c hc hc0
  obtain ⟨hlet, hfold⟩ := orbit_words o ho p hp
  refine ⟨o.1, orbit_root_cases o ho, ?_⟩
  rw [hpc] at hfold
  exact exists_Hconj_of_word hM hlet hfold

theorem mem_Hloc_top (hF : J4Facts) {h : J} :
    h ∈ Hloc (⊤ : Subgroup J) (Eg uJ 11) ↔ h ∈ Hj := by
  rw [Hloc_top_eq hF]

theorem mem_hOrbit_top (hF : J4Facts) {a u : J} :
    u ∈ hOrbit (⊤ : Subgroup J) (Eg uJ 11) a ↔ ∃ h ∈ Hj, h * a * h⁻¹ = u := by
  simp only [hOrbit, Set.mem_ofPred_eq, Hloc_top_eq hF]

end CFSG.EvenSporadicStandard.J4Std.DataMod
