
module

public import CFSG.GH74.QTGen4.Recog.G23.GlueExtCBase
public import CFSG.Certificates.Kernel.HcPackSound
import all Certificates.Data.G23RecogGlueInputs

public section

namespace CFSG.KC.HcPack

open CFSG.GH74.QTGen4.Recog.G23

section Count

theorem Hc_card_le : Nat.card Hc ≤ 576 := by
  have hfin := (Certificates.certificate320008).1
  have h := Nat.card_le_card_of_surjective _ φ5.rangeRestrict_surjective
  rw [range_φ5] at h
  exact h.trans Certificates.certificate320008.2

theorem elts_nodup_bfs : elts.Nodup :=
  bfsAux_nodup mulL 576 gensL 600 [idL] [idL] (List.nodup_singleton _)

theorem elts_image_of_len (hlen : elts.length = 576) :
    (elts.toFinset : Set (List ℕ)) = Lst '' (Hc : Set (Equiv.Perm (Fin 32))) := by
  apply Set.eq_of_subset_of_ncard_le
  · intro l hl
    obtain ⟨σ, hσ, rfl⟩ := elts_sound l (List.mem_toFinset.mp hl)
    exact ⟨σ, hσ, rfl⟩
  · rw [Set.ncard_image_of_injective _ Lst_injective, Set.ncard_coe_finset,
      List.toFinset_card_of_nodup elts_nodup_bfs, hlen, ← Nat.card_coe_set_eq]
    exact Hc_card_le
  · exact Set.toFinite _

theorem mem_elts_of_Hc_len (hlen : elts.length = 576) (σ : Equiv.Perm (Fin 32)) (hσ : σ ∈ Hc) :
    Lst σ ∈ elts := by
  have h : Lst σ ∈ (elts.toFinset : Set (List ℕ)) := by
    rw [elts_image_of_len hlen]; exact ⟨σ, hσ, rfl⟩
  exact List.mem_toFinset.mp h

theorem gensL_sound : ∀ g ∈ gensL, ∃ τ ∈ Hc, Lst τ = g := by
  intro g hg
  rcases List.mem_append.mp hg with hg | hg
  · obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hg
    exact ⟨gen k, Subgroup.subset_closure (Set.mem_range_self k), rfl⟩
  · obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hg
    exact ⟨(gen k)⁻¹, Subgroup.inv_mem _ (Subgroup.subset_closure (Set.mem_range_self k)), rfl⟩

theorem elts_facts (hlen : elts.length = 576) : (elts.length = 576) ∧ elts.Nodup ∧
    (∀ s ∈ elts, ∀ g ∈ gensL, mulL s g ∈ elts) ∧ idL ∈ elts := by
  refine ⟨hlen, elts_nodup_bfs, ?_, ?_⟩
  · intro s hs g hg
    obtain ⟨σ, hσ, rfl⟩ := elts_sound s hs
    obtain ⟨τ, hτ, rfl⟩ := gensL_sound g hg
    rw [← Lst_mul]
    exact mem_elts_of_Hc_len hlen _ (Subgroup.mul_mem _ hσ hτ)
  · rw [glue_idL_eq]
    exact mem_elts_of_Hc_len hlen 1 (Subgroup.one_mem _)

end Count

end CFSG.KC.HcPack

end
