module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesProj

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open QuadraticMap

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

private lemma aux_unit_mul_self (u : ℤˣ) : u * u = 1 := by
  rcases Int.units_eq_one_or u with h | h <;> rw [h] <;> decide

private lemma aux_solve_sign {σ α β : ℤˣ} (h : σ * α * β = α) (hα : α * α = 1)
    (hβ : β * β = 1) : σ = β := by
  have h' : σ * (α * β) = α := by rw [← mul_assoc]; exact h
  have hσ : σ = α * (α * β)⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq]; exact h'
  rw [hσ, mul_inv_rev, inv_eq_of_mul_eq_one_right hα, inv_eq_of_mul_eq_one_right hβ]
  calc α * (β * α) = α * β * α := by rw [← mul_assoc]
    _ = α * α * β := by rw [mul_assoc, mul_comm β α, ← mul_assoc]
    _ = β := by rw [hα, one_mul]

private lemma aux_sandwich (x α : ℤˣ) (hx : x * x = 1) : x * α * x = α := by
  rw [mul_assoc, mul_comm α x, ← mul_assoc, hx, one_mul]

private lemma aux_pow_neg_one (k : ℕ) : (-1 : ℤˣ) ^ k = Int.negOnePow (k : ℤ) := by
  rw [Int.negOnePow_def, zpow_natCast]

private lemma aux_neg_one_pow_sq (k : ℕ) : (-1 : ℤˣ) ^ (k * k) = (-1 : ℤˣ) ^ k := by
  rw [aux_pow_neg_one (k * k), aux_pow_neg_one k, Nat.cast_mul]
  exact Int.negOnePow_mul_self (k : ℤ)

theorem toProj_mem_centralizer_iff {s : OGroup Q} (hs : s * s = 1) (g : OGroup Q) :
    toProj Q g ∈ Subgroup.centralizer ({toProj Q s} : Set (ProjOrth Q)) ↔
      g * s * g⁻¹ = s ∨ g * s * g⁻¹ = piOrth Q * s := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h1 : toProj Q (g * s * g⁻¹) = toProj Q s := by
      calc toProj Q (g * s * g⁻¹)
          = toProj Q g * toProj Q s * (toProj Q g)⁻¹ := by
            rw [map_mul, map_mul, map_inv]
        _ = (toProj Q g * toProj Q s) * (toProj Q g)⁻¹ := rfl
        _ = (toProj Q s * toProj Q g) * (toProj Q g)⁻¹ := by rw [h]
        _ = toProj Q s := by group
    have heq : (g * s * g⁻¹)⁻¹ * s = g * s * g⁻¹ * s := by
      have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
      rw [mul_inv_rev, mul_inv_rev, inv_inv, hsinv]
      group
    have hmem : g * s * g⁻¹ * s ∈ piGroup Q := by
      rw [← heq]
      exact QuotientGroup.eq.mp h1
    rcases (mem_piGroup_iff.mp hmem) with h1' | h1'
    · left
      calc g * s * g⁻¹ = (g * s * g⁻¹) * (s * s) := by rw [hs, mul_one]
        _ = ((g * s * g⁻¹) * s) * s := by rw [← mul_assoc]
        _ = 1 * s := by rw [h1']
        _ = s := one_mul s
    · right
      calc g * s * g⁻¹ = (g * s * g⁻¹) * (s * s) := by rw [hs, mul_one]
        _ = ((g * s * g⁻¹) * s) * s := by rw [← mul_assoc]
        _ = piOrth Q * s := by rw [h1']
  · rintro (h | h)
    · calc toProj Q g * toProj Q s
          = toProj Q (g * s) := by rw [map_mul]
        _ = toProj Q ((g * s * g⁻¹) * g) := by congr 1; group
        _ = toProj Q (g * s * g⁻¹) * toProj Q g := by rw [map_mul]
        _ = toProj Q s * toProj Q g := by rw [h]
    · have hpi : toProj Q (piOrth Q) = 1 := by
        change (piOrth Q : ProjOrth Q) = 1
        rw [QuotientGroup.eq_one_iff]
        exact mem_piGroup_iff.mpr (Or.inr rfl)
      calc toProj Q g * toProj Q s
          = toProj Q (g * s) := by rw [map_mul]
        _ = toProj Q ((g * s * g⁻¹) * g) := by congr 1; group
        _ = toProj Q (g * s * g⁻¹) * toProj Q g := by rw [map_mul]
        _ = toProj Q (piOrth Q * s) * toProj Q g := by rw [h]
        _ = (toProj Q (piOrth Q) * toProj Q s) * toProj Q g := by rw [map_mul]
        _ = toProj Q s * toProj Q g := by rw [hpi, one_mul]

theorem map_centralizer_le_centralizer_toProj (s : OGroup Q) :
    (Subgroup.centralizer ({s} : Set (OGroup Q))).map (toProj Q) ≤
      Subgroup.centralizer ({toProj Q s} : Set (ProjOrth Q)) := by
  rintro x ⟨g, hg, rfl⟩
  refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
  have hg' : g * s = s * g := Subgroup.mem_centralizer_singleton_iff.mp hg
  rw [← map_mul, hg', map_mul]

theorem isConj_piOrth_mul_iff (hQ : Q.Nondegenerate) {s : OGroup Q} (hs : s * s = 1) :
    IsConj (piOrth Q * s) s ↔
      2 * invDim s = Module.finrank (ZMod 3) V ∧ quadSign Q = (-1) ^ invDim s := by
  rw [isConj_iff_invType_eq hQ (piOrth_mul_mul_self hs) hs, invType_piOrth_mul hQ hs]
  constructor
  · intro h
    have hfst : Module.finrank (ZMod 3) V - invDim s = invDim s := by
      have h' := congrArg Prod.fst h
      simpa only [invType] using h'
    have hsnd : quadSign Q * invSign s *
        (-1 : ℤˣ) ^ (invDim s * (Module.finrank (ZMod 3) V - invDim s)) = invSign s := by
      have h' := congrArg Prod.snd h
      simpa only [invType] using h'
    have hr := invDim_le (Q := Q) s
    refine ⟨by omega, ?_⟩
    have hpow : (-1 : ℤˣ) ^ (invDim s * (Module.finrank (ZMod 3) V - invDim s)) =
        (-1 : ℤˣ) ^ invDim s := by
      rw [hfst, aux_neg_one_pow_sq]
    rw [hpow] at hsnd
    exact aux_solve_sign hsnd (aux_unit_mul_self _) (aux_unit_mul_self _)
  · rintro ⟨h2r, hσ⟩
    apply Prod.ext
    · simp only [invType]
      have hr := invDim_le (Q := Q) s
      omega
    · show quadSign Q * invSign s *
          (-1 : ℤˣ) ^ (invDim s * (Module.finrank (ZMod 3) V - invDim s)) = invSign s
      have hnr : Module.finrank (ZMod 3) V - invDim s = invDim s := by
        have hr := invDim_le (Q := Q) s
        omega
      have hpow : (-1 : ℤˣ) ^ (invDim s * (Module.finrank (ZMod 3) V - invDim s)) =
          (-1 : ℤˣ) ^ invDim s := by
        rw [hnr, Nat.mul_comm, aux_neg_one_pow_sq]
      rw [hpow, hσ]
      exact aux_sandwich _ _ (aux_unit_mul_self _)

theorem centralizer_toProj_eq_map (hQ : Q.Nondegenerate) {s : OGroup Q} (hs : s * s = 1)
    (h : ¬ IsConj (piOrth Q * s) s) :
    Subgroup.centralizer ({toProj Q s} : Set (ProjOrth Q)) =
      (Subgroup.centralizer ({s} : Set (OGroup Q))).map (toProj Q) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (piGroup Q) x
    rw [toProj_mem_centralizer_iff hs g] at hx
    rcases hx with hgs | hgs
    · refine Subgroup.mem_map.mpr ⟨g, ?_, rfl⟩
      refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      calc g * s = (g * s * g⁻¹) * g := by group
        _ = s * g := by rw [hgs]
    · exact (h ((isConj_iff.mpr ⟨g, hgs⟩).symm)).elim
  · exact map_centralizer_le_centralizer_toProj s

end CFSG.OddStandard.SmallF3.Omega
