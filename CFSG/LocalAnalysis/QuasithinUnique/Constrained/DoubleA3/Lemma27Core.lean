module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Lemma27

public section

namespace CFSG.QuasithinUnique.DoubleA3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G}

theorem lemma2_4_27A3_part34 (hD : AppC.C56DoubleA3) (h27_1 : Lemma2_4_27_1A3)
    (hcs : ConstrainedSetting G T M H S L) (h3 : IsAltType L 3) (hne : conjJoin S L ≠ L) :
    (IsElemAbelian 2 (blockTC T S L) ∧ pCoreOf 2 H = blockTC T S L ⊔ blockU0 S L ∧
      blockTC T S L ⊓ blockU0 S L = ⊥ ∧
      ∀ x ∈ T, x ∉ S → blockTC T S L ⊓ conjR (blockTC T S L) x = ⊥) ∧
    (∀ x ∈ T, x ∉ S →
      baum S = blockTC T S L ⊔ (blockU0 S L ⊔ conjR (blockU0 S L) x) ∧
      blockTC T S L ⊓ (blockU0 S L ⊔ conjR (blockU0 S L) x) = ⊥ ∧
      (∀ t ∈ blockTC T S L, ∀ y ∈ blockU0 S L ⊔ conjR (blockU0 S L) x, t * y = y * t) ∧
      ⁅conjJoin S L, conjR (blockU0 S L) x⁆ = conjJoin S L) := by
  obtain ⟨s, hcfg⟩ := exists_A3A3 hcs h3 hne
  obtain ⟨hidx, hbJ, hJT⟩ := h27_1 G T M H S L hcs h3 hne
  have hTN : T ≤ normalizer (S : Set G) := normalizer_of_relIndex_two hcs.le_T hidx
  obtain ⟨hU0, hDab, hbD, hQ, -, -, hx⟩ := hD G T M H S L hcs h3 hne T hcs.le_T le_rfl hidx
  have hQ' : pCoreOf 2 H = blockD S L ⊔ blockU0 S L := by rw [← hbD]; exact hQ
  have hUL : blockU L ≤ L := hcfg.isA4.le
  have hUbot : blockU L ≠ ⊥ := fun h => by
    have := hcfg.isA4.card_U
    rw [h, Subgroup.card_bot] at this
    omega
  have hTC : blockTC T S L = blockD S L := blockTC_eq_blockD hcs hU0 hQ hUbot hUL
  have hDab' : IsElemAbelian 2 (blockD S L) := hbD ▸ hDab
  refine ⟨?_, ?_⟩
  · rw [hTC]
    refine ⟨hDab', hQ', ?_, ?_⟩
    · rw [eq_bot_iff]
      rintro g ⟨hgD, hgU⟩
      have hU0L : blockU0 S L ≤ conjJoin S L := iSup_mono fun g => Subgroup.map_mono hUL
      have := hcfg.center_L0 g (hU0L hgU) (fun l hl =>
        (Subgroup.mem_centralizer_iff.mp hgD.2 l hl).symm)
      rw [this]; exact one_mem _
    · intro x hxT hxS
      have := (hx x hxT hxS).1
      rwa [hbD] at this
  · intro x hxT hxS
    rw [hTC]
    have hx' := hx x hxT hxS
    obtain ⟨hDD, hbaum, -⟩ := hx'
    have hinf := blockD_inf_sup_conj hD hcfg hU0 hQ' hcs.le_T le_rfl hidx hxT hxS
    refine ⟨?_, hinf.1, hinf.2, ?_⟩
    · have h1 : baum S = baumD S L ⊔ (blockU0 S L ⊔ conjR (blockU0 S L) x) :=
        hbaum.trans (sup_assoc _ _ _)
      rw [hbD] at h1
      exact h1
    · obtain ⟨z₁, z₂, hz₁1, hz₂1, hz₁C, hz₂C, R1, R2⟩ := rank1_blocks hD hcfg
      obtain ⟨y, hyT, hyS, hc1, -, hc2, -, -⟩ :=
        exists_good_elt hD hcfg hcs.le_T le_rfl hidx
      have hSU0 : S ≤ normalizer (blockU0 S L : Set G) := C56.S_le_normalizer_conjJoin (blockU L)
      rw [conjR_eq_of_mem_diff hcs.le_T hidx hSU0 hyT hyS hxT hxS]
      exact commutator_conjJoin_eq hcfg hU0 R1 (hTN hyT) hc1 hc2

end CFSG.QuasithinUnique.DoubleA3
