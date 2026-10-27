module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.ModelGenFrame
public import Certificates.Certificate25261

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Gen

open Subgroup CFSG.Sporadic.Fi23 FrameJ CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open scoped Pointwise

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

set_option linter.unusedSectionVars false

section

theorem smul_eq_pi22 (c : Cd) (u : Fin 3510) : c • u = pi22 (piC c) u := by
  rw [pi22_piC]
  rfl

theorem smul_eq_piC (c : Cd) (u : Fin 3510) : c • u = piC c • u := by
  rw [smul_eq_pi22]
  rfl

theorem smul_finset_eq_piC (c : Cd) (V : Finset (Fin 3510)) : c • V = piC c • V := by
  ext u
  simp only [Finset.mem_smul_finset, smul_eq_piC]

end

section

theorem orbit_uPts_ge : 142155 ≤ Nat.card (MulAction.orbit Cd uPts) := by
  have h : 142155 ≤ Nat.card (MulAction.orbit CFSG.Sporadic.Fi22.J uPts) :=
    Certificates.certificate25261
  refine h.trans (Nat.card_mono (Set.toFinite _) ?_)
  rintro _ ⟨g, rfl⟩
  obtain ⟨c, rfl⟩ := piC_surjective g
  exact ⟨c, smul_finset_eq_piC c uPts⟩

theorem card_normalizer_le : Nat.card (normalizer (E0 : Set Cd)) ≤ 908328960 := by
  have hle : normalizer (E0 : Set Cd) ≤ Stab := fun c hc => mem_normalizer_iff_mem_stab.1 hc
  have h1 : Stab.index ∣ (normalizer (E0 : Set Cd)).index := Subgroup.index_dvd_of_le hle
  have h2 : Stab.index = Nat.card (MulAction.orbit Cd uPts) := by
    unfold Stab
    rw [MulAction.index_stabilizer, Nat.card_coe_set_eq]
  have h3 : 142155 ≤ (normalizer (E0 : Set Cd)).index := by
    refine (h2 ▸ orbit_uPts_ge).trans (Nat.le_of_dvd ?_ h1)
    exact Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have h4 := Subgroup.card_mul_index (normalizer (E0 : Set Cd))
  rw [card_centralizer_d] at h4
  by_contra hcon
  have h5 := Nat.mul_le_mul (not_le.1 hcon) h3
  omega

end

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Gen
