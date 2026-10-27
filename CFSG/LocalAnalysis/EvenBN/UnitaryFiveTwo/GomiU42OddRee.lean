module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42Aut
public import CFSG.GH74.GLS.IVK.Proofs2.GHInvRee
public import CFSG.GH74.GLS.IVK.Proofs2.GHInvAutRank

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.IVK.GHInv

variable {X : Type} [Group X] [Finite X] {J D E : Subgroup X} {a : X}

theorem GomiU42Data.exists_elementary_aut (h : GomiU42Data X J D E a) :
    haveI := h.normal
    ∃ E' : Subgroup (MulAut ↥D), (∀ e ∈ E', e * e = 1) ∧ Nat.card E' = 2 ^ 8 := by
  haveI := h.normal
  haveI := h.elementary
  refine ⟨E.map (MulAut.conjNormal : X →* MulAut D), ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul]
    have h2 : x * x = 1 := by
      rw [← pow_two]
      exact CFSG.elemPow_eq_one_of_isElementaryAbelian x hx
    rw [h2, map_one]
  · rw [Subgroup.card_map_of_injective h.conjNormal_injective, h.card_E]

theorem GomiU42Data.false_of_oddLie_reeTits'
    (h : GomiU42Data X J D E a) {t : StatedLieTag} {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (ht : t ∈ reeTitsTags) (hD : ReeTitsModel ↥D t p f) : False := by
  have hadm := hD.1
  have hree : ReeTitsModel ↥D .twistedG2 3 f := by
    simp only [reeTitsTags, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl
    · obtain ⟨-, -, -, hp3, -⟩ := hadm
      subst hp3
      exact hD
    · exact absurd hadm.2.2.2.1 hp2
    · exact absurd hadm.2.2.2.1 hp2
  haveI := h.simple
  have hZ : center ↥D = ⊥ := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup h.nonabelian).2
  obtain ⟨E', hE'sq, hE'card⟩ := h.exists_elementary_aut
  have hle := card_le_two_pow_add_of_aut (L := ↥D) hZ (r := 3) (s := 0)
    (fun E hE => ree_card_elementary_le hree E hE)
    (fun E hE => ree_card_outer_elementary hree E hE) E' hE'sq
  rw [hE'card] at hle
  norm_num at hle

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
