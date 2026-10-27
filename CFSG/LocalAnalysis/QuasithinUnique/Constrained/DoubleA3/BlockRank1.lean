module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Basic245BaumannCS

public section

namespace CFSG.QuasithinUnique.DoubleA3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Subgroup

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G}

omit [Finite G] in
theorem mem_normalizer_baum {g : G} (hg : g ∈ S) : g ∈ normalizer (baum S : Set G) :=
  normalizer_le_normalizer_baum S (Subgroup.le_normalizer hg)

theorem blockU_le_baum (hcs : ConstrainedSetting G T M H S L) (h3 : IsAltType L 3) :
    blockU L ≤ baum S :=
  (C56.baumann_A3_cs hcs h3).1

theorem isPGroup_baum (hcs : ConstrainedSetting G T M H S L) : IsPGroup 2 (baum S) :=
  hcs.sylow.isPGroup.to_le inf_le_left

theorem rank1_block₁ (hcs : ConstrainedSetting G T M H S L)
    (h3 : IsAltType L 3) (hnt : ¬ baum S ≤ centralizer (blockU L : Set G)) :
    ∃ z ∈ blockU L, z ≠ 1 ∧ blockU L ⊓ centralizer (baum S : Set G) = zpowers z ∧
      C5.Rank1 (baum S) (baum S ⊓ centralizer (blockU L : Set G)) (blockU L) (zpowers z) 2 := by
  obtain ⟨hBN, -⟩ := (C56.baumann_A3_cs hcs h3).2
  obtain ⟨-, hU4, hU2, hUab, -⟩ := (hcs.block.1.1 : IsShort2 L).alt3_structure h3
  exact rank1_of_klein hU4 hU2 hUab (blockU_le_baum hcs h3)
    (fun g hg => C1.mem_normalizer_blockU (hBN hg)) (isPGroup_baum hcs) hnt

theorem rank1_block₂ {Q₁ W₁ : Subgroup G} (hcs : ConstrainedSetting G T M H S L)
    (h3 : IsAltType L 3) {s : G} (hs : s ∈ S)
    (R1 : C5.Rank1 (baum S) Q₁ (blockU L) W₁ 2)
    (hnt : ¬ baum S ≤ centralizer (blockU2 L s : Set G)) :
    ∃ z ∈ blockU2 L s, z ≠ 1 ∧ blockU2 L s ⊓ centralizer (baum S : Set G) = zpowers z ∧
      C5.Rank1 (baum S) (baum S ⊓ centralizer (blockU2 L s : Set G)) (blockU2 L s)
        (zpowers z) 2 := by
  obtain ⟨-, hU4, hU2, -, -⟩ := (hcs.block.1.1 : IsShort2 L).alt3_structure h3
  have hsB : s ∈ normalizer (baum S : Set G) := mem_normalizer_baum hs
  have hU4' : Nat.card (blockU2 L s) = 4 := by
    rw [← hU4]; exact C5.card_conjSubgroup (blockU L) s
  have hU2' : ∀ a ∈ blockU2 L s, a ^ 2 = 1 := by
    intro a ha
    have ha' : s * a * s⁻¹ ∈ blockU L := mem_conjR.mp ha
    have h1 : (s * a * s⁻¹) * (s * a * s⁻¹) = 1 := by
      have := hU2 _ ha'
      rwa [pow_two] at this
    have : a * a = s⁻¹ * ((s * a * s⁻¹) * (s * a * s⁻¹)) * s := by group
    rw [h1] at this
    rw [pow_two, this]; group
  exact rank1_of_klein hU4' hU2' (R1.conj_comm s) (R1.conj_le_B hsB) (R1.B_le_normU_conj hsB)
    (isPGroup_baum hcs) hnt

end CFSG.QuasithinUnique.DoubleA3
