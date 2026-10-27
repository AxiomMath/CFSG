module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldSpecialUnitary

public section

namespace CFSG.ComponentClassification.CatalogueBGraphField

noncomputable section

open Matrix CatalogueBUnitaryIsometry CFSG.LieType.Universal.Unitary

universe u

theorem scalar_mem_SUid_iff (n : ℕ) (K : Type u) [Field K]
    (hn : 1 ≤ n) (sigma : K ≃+* K) (c : Kˣ) :
    GeneralLinearGroup.scalar (Fin n) c ∈ SUid sigma n ↔
      sigma (c : K) * (c : K) = 1 ∧ (c : K) ^ n = 1 := by
  have hdet : (GeneralLinearGroup.scalar (Fin n) c).val.det = (c : K) ^ n := by
    simpa only [GeneralLinearGroup.val_det_apply, Units.val_pow_eq_pow_val,
      Fintype.card_fin] using congrArg Units.val (GeneralLinearGroup.det_scalar (n := Fin n) c)
  rw [mem_SUid, ← mem_Uid_iff sigma n _, hdet, scalar_mem_unitary_iff n K hn sigma c]
  exact and_comm

theorem specialUnitaryScalars_mem_iff (n : ℕ) (K : Type u) [Field K]
    (hn : 1 ≤ n) (sigma : K ≃+* K) (g : SUid sigma n) :
    g ∈ specialUnitaryScalars n K sigma ↔
      ∃ c : Kˣ, sigma (c : K) * (c : K) = 1 ∧ (c : K) ^ n = 1 ∧
        GeneralLinearGroup.scalar (Fin n) c = g.val := by
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨hnorm, hpower⟩ := (scalar_mem_SUid_iff n K hn sigma c).mp
      (hc.symm ▸ g.property)
    exact ⟨c, hnorm, hpower, hc⟩
  · rintro ⟨c, _, _, hc⟩
    exact ⟨c, hc⟩

theorem specialUnitaryScalars_central (n : ℕ) (K : Type u) [Field K]
    (sigma : K ≃+* K) :
    specialUnitaryScalars n K sigma ≤ Subgroup.center (SUid sigma n) := by
  rintro g ⟨c, hc⟩
  change GeneralLinearGroup.scalar (Fin n) c = g.val at hc
  apply Subgroup.mem_center_iff.mpr
  intro h
  apply Subtype.ext
  change h.val * g.val = g.val * h.val
  rw [← hc]
  exact (GeneralLinearGroup.scalar_commute c h.val).symm

end

end CFSG.ComponentClassification.CatalogueBGraphField
