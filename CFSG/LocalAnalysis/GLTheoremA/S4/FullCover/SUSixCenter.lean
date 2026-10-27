module

public import CFSG.LieType.Universal.Unitary.Clause0

public section

namespace CFSG.LocalAnalysis.GLTheoremA.FullCover

open CFSG.Open Matrix

private theorem sixTwo_units_pow_three {K : Type} [Field K] (hK : Nat.card K = 4) (c : Kˣ) :
    c ^ 3 = 1 := by
  have h3 : Nat.card Kˣ = 3 := by rw [Nat.card_units, hK]
  have hd : orderOf c ∣ 3 := by
    have := orderOf_dvd_natCard c
    rwa [h3] at this
  exact orderOf_dvd_iff_pow_eq_one.mp hd

private theorem sixTwo_scalar_mem {K : Type} [Field K] {c : Kˣ} (hc : c ^ 3 = 1) :
    Matrix.GeneralLinearGroup.scalar (Fin 6) c ∈ StatedSU 6 2 K := by
  have hc3 : (c : K) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hc, Units.val_one]
  have hc6 : (c : K) ^ 6 = 1 := by
    have h : (c : K) ^ 6 = ((c : K) ^ 3) ^ 2 := by ring
    rw [h, hc3, one_pow]
  have hc' : (c : K) ^ 2 * (c : K) = 1 := by
    rw [← pow_succ]
    exact hc3
  apply Subgroup.subset_closure
  refine ⟨?_, ?_⟩
  · rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, det_diagonal,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact hc6
  · change ((Matrix.scalar (Fin 6) (c : K)).map (· ^ 2))ᵀ * Matrix.scalar (Fin 6) (c : K) = 1
    rw [Matrix.scalar_apply, diagonal_map (f := fun x : K => x ^ 2) (zero_pow (by norm_num)),
      diagonal_transpose, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    exact hc'

theorem isQuasisimple_statedSU_six_two {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4) :
    CFSG.Open.IsQuasisimple (StatedSU 6 2 K) ∧
      Subgroup.center (StatedSU 6 2 K) = (StatedScalars (Fin 6) K).subgroupOf (StatedSU 6 2 K) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hq, hc⟩ := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card
    (p := 2) (f := 1) (n := 6) (F := K) (by norm_num [hK]) (by norm_num) (by decide)
  exact ⟨⟨Group.isPerfect_def.mp hq.1, hq.2.1⟩, hc⟩

theorem card_center_statedSU_six_two {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4) :
    Nat.card (Subgroup.center ↥(StatedSU 6 2 K)) = 3 := by
  have hcen : Subgroup.center ↥(StatedSU 6 2 K) =
      (StatedScalars (Fin 6) K).subgroupOf (StatedSU 6 2 K) :=
    (isQuasisimple_statedSU_six_two hK).2
  let φ : Kˣ → Subgroup.center ↥(StatedSU 6 2 K) := fun c =>
    ⟨⟨Matrix.GeneralLinearGroup.scalar (Fin 6) c, sixTwo_scalar_mem (sixTwo_units_pow_three hK c)⟩,
      Subgroup.mem_center_iff.mpr fun g => Subtype.ext
        (Matrix.GeneralLinearGroup.scalar_commute c (g : Matrix.GeneralLinearGroup (Fin 6) K)).symm⟩
  have hφi : Function.Injective φ := fun c₁ c₂ h => by
    have h' := congrArg (fun z : Subgroup.center ↥(StatedSU 6 2 K) =>
      ((((z : ↥(StatedSU 6 2 K)) : Matrix.GeneralLinearGroup (Fin 6) K) :
        Matrix (Fin 6) (Fin 6) K) 0 0)) h
    simp only [φ, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      diagonal_apply_eq] at h'
    exact Units.ext h'
  have hφs : Function.Surjective φ := fun z => by
    have hz : (z : ↥(StatedSU 6 2 K)) ∈ (StatedScalars (Fin 6) K).subgroupOf (StatedSU 6 2 K) := by
      rw [← hcen]
      exact z.2
    rw [Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at hz
    obtain ⟨c, hc⟩ := hz
    exact ⟨c, Subtype.ext (Subtype.ext hc)⟩
  have hcard : Nat.card Kˣ = Nat.card (Subgroup.center ↥(StatedSU 6 2 K)) :=
    Nat.card_congr (Equiv.ofBijective φ ⟨hφi, hφs⟩)
  rw [← hcard, Nat.card_units, hK]

end CFSG.LocalAnalysis.GLTheoremA.FullCover
