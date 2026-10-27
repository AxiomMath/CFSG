module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitGHCertCheck
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitGHCertRel
import all CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG.CosetTable

namespace GHCert

theorem ghWordsD_eq : ghWordsD = ghWords := rfl

end GHCert

theorem ghPresentationBound : GHPresentationBound :=
  GHCert.presentation_bound

namespace GHCert

open CFSG.Sporadic.SmallF2 CFSG.Sporadic.Th
open CFSG.Sporadic.HS.Native (hsData)

theorem mem_nfCodes {k : ℕ} {c : ℤ} (hc : c ∈ nfCodes k) :
    ∃ i : ℕ, i < 9 ∧ c = (i : ℤ) + 1 := by
  simp only [nfCodes, List.mem_filterMap, List.mem_range] at hc
  obtain ⟨i, hi, h⟩ := hc
  split_ifs at h with hb
  · exact ⟨i, hi, (Option.some.inj h).symm⟩

theorem gensG9_pos (i : ℕ) : gensG9 ((i : ℤ) + 1) = ghG i := by
  simp [gensG9]

theorem ghFam_ghG : ghFam (ghG 0) (ghG 1) (ghG 2) (ghG 3) (ghG 4) (ghG 5) (ghG 6) (ghG 7)
    (ghG 8) = fun i : Fin 9 => ghG i.val := by
  funext i
  fin_cases i <;> rfl

theorem ghRel_ghG :
    GHRel (ghG 0) (ghG 1) (ghG 2) (ghG 3) (ghG 4) (ghG 5) (ghG 6) (ghG 7) (ghG 8) := by
  refine ghRel_of_lift_eq_one fun r hr => ?_
  rw [ghFam_ghG]
  exact ghG_rels r (ghWordsD_eq ▸ hr)

abbrev ghSet : Set (J hsData) :=
  {ghG 0, ghG 1, ghG 2, ghG 3, ghG 4, ghG 5, ghG 6, ghG 7, ghG 8}

theorem nfG_mem (k : ℕ) : nfG k ∈ Subgroup.closure ghSet := by
  refine (Subgroup.closure ghSet).list_prod_mem fun g hg => ?_
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hg
  obtain ⟨i, hi, rfl⟩ := mem_nfCodes hc
  rw [gensG9_pos]
  apply Subgroup.subset_closure
  interval_cases i <;> simp

theorem card_closure_ghG : Nat.card (Subgroup.closure ghSet) = 512 := by
  refine le_antisymm (ghRel_card_closure_le ghPresentationBound ghRel_ghG) ?_
  let F : Fin 512 → Subgroup.closure ghSet := fun k => ⟨nfG k, nfG_mem k⟩
  have hF : Function.Injective F := fun k k' h =>
    Fin.ext (nfG_inj k k.isLt k' k'.isLt (congrArg Subtype.val h))
  have := Nat.card_le_card_of_injective F hF
  rwa [Nat.card_eq_fintype_card, Fintype.card_fin] at this

end GHCert

open CFSG.Sporadic.SmallF2 GHCert in
theorem ghRelInHS : GHRelInHS := by
  have e : CFSG.Blueprint.NativeSporadic.HS ≃* J CFSG.Sporadic.HS.Native.hsData :=
    seedEquiv CFSG.Sporadic.HS.hsFacts.toBaseFacts
  refine ⟨e.symm (ghG 0), e.symm (ghG 1), e.symm (ghG 2), e.symm (ghG 3), e.symm (ghG 4),
    e.symm (ghG 5), e.symm (ghG 6), e.symm (ghG 7), e.symm (ghG 8), ghRel_map e.symm ghRel_ghG, ?_⟩
  have hs : ({e.symm (ghG 0), e.symm (ghG 1), e.symm (ghG 2), e.symm (ghG 3), e.symm (ghG 4),
      e.symm (ghG 5), e.symm (ghG 6), e.symm (ghG 7), e.symm (ghG 8)} :
      Set CFSG.Blueprint.NativeSporadic.HS) =
      e.symm '' ghSet := by
    simp only [ghSet, Set.image_insert_eq, Set.image_singleton]
  rw [hs, card_closure_image, card_closure_ghG]

end CFSG.ComponentClassification.HSFLit
