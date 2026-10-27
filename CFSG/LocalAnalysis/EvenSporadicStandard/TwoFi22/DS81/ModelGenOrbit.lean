module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.ModelGenLower
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.ModelGenUpper
public import Certificates.Certificate25262

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Gen

open Subgroup CFSG.Sporadic.Fi23 FrameJ CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open scoped Pointwise

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

set_option linter.unusedSectionVars false



theorem orbit_t0_ge : 443520 ≤ Nat.card (MulAction.orbit
    ↥((E0 : Subgroup ↥Cd) ⊔
      Subgroup.closure {y : ↥Cd | y ∈ normalizer (E0 : Set ↥Cd) ∧ Odd (orderOf y)})
    (![190, 195, 526, 594, 752] : Fin 5 → Fin 3510)) := by
  set K : Subgroup ↥Cd := (E0 : Subgroup ↥Cd) ⊔
    Subgroup.closure {y : ↥Cd | y ∈ normalizer (E0 : Set ↥Cd) ∧ Odd (orderOf y)} with hK
  have h : 443520 ≤ Nat.card (MulAction.orbit
      ↥(Subgroup.closure {x : CFSG.Sporadic.Fi22.J | x • uPts = uPts ∧ Odd (orderOf x)})
      (![190, 195, 526, 594, 752] : Fin 5 → Fin 3510)) := Certificates.certificate25262
  have hle : Subgroup.closure {x : CFSG.Sporadic.Fi22.J | x • uPts = uPts ∧ Odd (orderOf x)} ≤
      K.map piC := by
    rw [Subgroup.closure_le]
    rintro x ⟨hU, hodd⟩
    obtain ⟨c, hc, ho⟩ := exists_odd_lift x (orderOf x) hodd (pow_orderOf_eq_one x)
    have hn : c ∈ normalizer (E0 : Set Cd) := by
      rw [mem_normalizer_iff_mem_stab, mem_stab_iff]
      intro u hu
      rw [smul_eq_piC, hc, ← hU]
      exact Finset.smul_mem_smul_finset hu
    exact ⟨c, Subgroup.mem_sup_right (subset_closure ⟨hn, ho⟩), hc⟩
  refine h.trans (Nat.card_mono (Set.toFinite _) ?_)
  rintro _ ⟨⟨x, hx⟩, rfl⟩
  obtain ⟨c, hcK, hc⟩ := hle hx
  refine ⟨⟨c, hcK⟩, ?_⟩
  funext i
  change c • (![190, 195, 526, 594, 752] : Fin 5 → Fin 3510) i =
    x • (![190, 195, 526, 594, 752] : Fin 5 → Fin 3510) i
  rw [smul_eq_piC, hc]

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Gen
