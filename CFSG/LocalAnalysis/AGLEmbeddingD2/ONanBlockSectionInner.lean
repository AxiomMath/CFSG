module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.ONanBlockInnerParabolic
import CFSG.LocalAnalysis.AGLEmbeddingD2.ONanBlockInnerStep
import CFSG.LocalAnalysis.AGLEmbeddingD2.ONanBlockInnerTypes
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoEscapeBlocksAux
import CFSG.LocalAnalysis.AGLEmbedding.BlockFactReductionsIVTypes
public import CFSG.LocalAnalysis.AGLEmbeddingD2.AltFiveBlocks

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique InnerStep InnerTypes

theorem inf_centralizer_eq_bot_of_not_dvd {X : Type*} [Group X] {Lb E : Subgroup X}
    (hEL : E ≤ Lb) (hE : IsElemAbelian 3 E) (h3 : ¬ 3 ∣ Nat.card (Subgroup.center ↥Lb)) :
    E ⊓ Subgroup.centralizer (Lb : Set X) = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxE, hxC⟩
  rw [Subgroup.mem_bot]
  have hxL : x ∈ Lb := hEL hxE
  set z : ↥(Subgroup.center ↥Lb) := ⟨⟨x, hxL⟩, Subgroup.mem_center_iff.mpr fun g =>
    Subtype.ext (Subgroup.mem_centralizer_iff.mp hxC g g.2)⟩ with hz
  have hz3 : z ^ 3 = 1 := Subtype.ext (Subtype.ext (hE.2 x hxE))
  have hdvd : orderOf z ∣ 3 := orderOf_dvd_of_pow_eq_one hz3
  rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h | h
  · have := orderOf_eq_one_iff.1 h
    exact congrArg (fun w : ↥(Subgroup.center ↥Lb) => ((w : ↥Lb) : X)) this
  · exact absurd (h ▸ orderOf_dvd_natCard z) h3

theorem kFactBlockAltFiveSectionInner_of_types (h86 : Asc81bEightSix) (h93 : Asc81bNineThree)
    (hFive : KFactBlockFiveNoncyclic) (hP : KFactBlockAltFiveSectionParabolic) :
    KFactBlockAltFiveSectionInner := by
  intro G _ _ M S L U hK hA hL hX hS hB hUM hUN hUL φ hφ hφ1
  have hSL := h86 G M S hK hA _ hL.component
  have h60 : Nat.card (alternatingGroup (Fin 5)) ∣ Nat.card (blockPL M S L) :=
    card_dvd_card_blockPL hSL hB hUM hUN hUL φ hφ hφ1
  have h5 : 5 ∣ Nat.card (blockPL M S L) := by
    have h : 5 ∣ Nat.card (alternatingGroup (Fin 5)) := by
      rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
      decide
    exact h.trans h60
  by_cases h3 : 3 ∣ Nat.card (Subgroup.center ↥(barM M L))
  · obtain ⟨hperf, hnab⟩ := block_perfect_nonabelian hL
    have hZ1 : Subgroup.center ↥(barM M L) = ⊥ → False := fun hZ => by
      rw [hZ, Subgroup.card_bot] at h3
      exact absurd (Nat.le_of_dvd one_pos h3) (by norm_num)
    rcases h93 G M S L hK hA hL with h1 | h2 | h3t | h4 | h5t | h6 | h7 | h8
    · exact absurd h1 hX
    · exact hP G M S L U hK hA hL hX hS hB h2 h3 hUM hUN hUL φ hφ hφ1
    · exact (hZ1 (center_eq_bot_of_isOrthogonalTwo hperf hnab h3t.2.1)).elim
    · exact absurd (h5.trans (card_blockPL_dvd_of_nineThreeFour h4)) (by norm_num)
    · obtain ⟨-, ⟨e⟩, -⟩ := h5t
      exact (hZ1 (center_eq_bot_of_mulEquiv_alternating hnab e)).elim
    · obtain ⟨-, n, ⟨e1⟩, ⟨e2⟩⟩ := h6
      have h5n : 5 ∣ Nat.card (Equiv.Perm (Fin n)) :=
        dvd_card_of_dvd_card_pCore_quotient e2 (by norm_num) h5
      rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin] at h5n
      have hn5 : 5 ≤ n := (Nat.Prime.dvd_factorial Nat.prime_five).1 h5n
      exact (not_three_dvd_card_center_of_alt hL (by omega) e1 h3).elim
    · obtain ⟨-, n, ⟨e⟩, -⟩ := h7
      exact (hZ1 (center_eq_bot_of_mulEquiv_alternating hnab e)).elim
    · obtain ⟨-, N, r, -, -, -, -, -, ⟨e⟩, -⟩ := h8
      exact (hZ1 (center_eq_bot_of_mulEquiv_alternating hnab e)).elim
  · obtain ⟨⟨E, hEL, hE, hEc⟩, -⟩ := hFive G M S L hK hA hL hX hS h5
    exact Or.inl ⟨E, hEL, hE, hEc, inf_centralizer_eq_bot_of_not_dvd hEL hE h3⟩

end CFSG.AGLEmbeddingD2
