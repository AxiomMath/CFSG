module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureUnitaryExcludedModel
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.UnitaryPairIndexFrame

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.UnitaryPairIndex.Model

open Matrix CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open CFSG.ShultStronglyClosedTI.TwoCoreGrowth CFSG.ShultStronglyClosedTI.UnitaryAutomorphism
open CFSG.ShultStronglyClosedTI.UnitaryHulls CFSG.ShultStronglyClosedTI.UnitaryExcluded
open CFSG.ProperTwoGeneratedCore.UnitaryPairIndex.Frame
open scoped LinearAlgebra.Projectivization

variable {K : Type} [Field K] {J : HermitianForm 3 K} {C : Subgroup J.specialSubgroup} [C.Normal]

theorem commute_torusL_of_swap (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hC : C ≤ scalarCenter J) {x : J.specialSubgroup ⧸ C}
    (h0 : coverToPGL J C hJ hC x • unitaryCoordinatePoint (K := K) 0 = unitaryCoordinatePoint 2)
    (h2 : coverToPGL J C hJ hC x • unitaryCoordinatePoint (K := K) 2 = unitaryCoordinatePoint 0)
    {y : J.specialSubgroup ⧸ C} (hy : y ∈ torusL J C hJ) : Commute x y := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective C x
  obtain ⟨c, rfl⟩ := hy
  change ProjGenLinGroup.mk (g : GL (Fin 3) K) • unitaryCoordinatePoint (K := K) 0 = _ at h0
  change ProjGenLinGroup.mk (g : GL (Fin 3) K) • unitaryCoordinatePoint (K := K) 2 = _ at h2
  have hc0 := (unitary_projective_coordinate_maps_iff (g : GL (Fin 3) K) 0 2).mp h0
  have hc2 := (unitary_projective_coordinate_maps_iff (g : GL (Fin 3) K) 2 0).mp h2
  have h00 := hc0 0 (by decide)
  have h10 := hc0 1 (by decide)
  have h12 := hc2 1 (by decide)
  have h22 := hc2 2 (by decide)
  obtain ⟨h01, h21⟩ := unitary_outer_plane_preserves_middle J hJ (g : GL (Fin 3) K)
    (J.specialSubgroup_le_unitarySubgroup g.2) h10 h12
  change ((QuotientGroup.mk' C) g) * ((QuotientGroup.mk' C) (torusHom J hJ c)) =
    ((QuotientGroup.mk' C) (torusHom J hJ c)) * ((QuotientGroup.mk' C) g)
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul, coe_torusHom, coe_diag3]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, h00, h10, h12, h22,
    h01, h21, mul_comm]

theorem pairStabilizerL_commute (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hC : C ≤ scalarCenter J) {x y : J.specialSubgroup ⧸ C}
    (hx : x ∈ pairStabilizerL J C hJ hC) (hy : y ∈ pairStabilizerL J C hJ hC) : Commute x y := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective C x
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective C y
  obtain ⟨hg0, hg2⟩ := (mem_pairStabilizerL hJ hC g).mp hx
  obtain ⟨hh0, hh2⟩ := (mem_pairStabilizerL hJ hC h).mp hy
  obtain ⟨hgd, -⟩ := diagonal_of_fix_outer hJ hg0 hg2
  obtain ⟨hhd, -⟩ := diagonal_of_fix_outer hJ hh0 hh2
  change ((QuotientGroup.mk' C) g) * ((QuotientGroup.mk' C) h) =
    ((QuotientGroup.mk' C) h) * ((QuotientGroup.mk' C) g)
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul]
  rw [hgd, hhd]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, mul_comm]

section Finite

variable [Finite K] [CharP K 2]

theorem mem_upperRootL_of_sq {f : ℕ} (hf : 2 ≤ f) (hcard : Nat.card K = (2 ^ f) ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) (hC : C ≤ scalarCenter J)
    {x : J.specialSubgroup ⧸ C}
    (hx : coverToPGL J C hJ hC x • unitaryCoordinatePoint (K := K) 0 = unitaryCoordinatePoint 0)
    (hxx : x * x = 1) : x ∈ upperRootL J C hJ := by
  obtain ⟨z, rfl⟩ := mem_range_heisL_of_pow_eq_one hf hcard hfixed hJ hC hx (k := 1)
    (by rw [pow_one, pow_two, hxx])
  rw [← map_mul, ← map_one (heisL J C hJ)] at hxx
  have hzz := heisL_injective hJ hC hxx
  have h2 : (z * z).1.2 = 0 := by rw [hzz]; rfl
  change z.1.2 + z.1.2 - z.1.1 * J.conj z.1.1 = 0 at h2
  rw [CharTwo.add_self_eq_zero, zero_sub, neg_eq_zero, mul_eq_zero] at h2
  have ha : z.1.1 = 0 := by
    rcases h2 with h | h
    · exact h
    · exact (map_eq_zero J.conj).mp h
  exact (mem_upperRootL_iff hJ _).mpr ⟨z, ha, rfl⟩

theorem card_scalarCenter {f : ℕ} (hf : 2 ≤ f) (hcard : Nat.card K = (2 ^ f) ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    Nat.card (scalarCenter J) = Nat.gcd 3 (2 ^ f + 1) := by
  obtain ⟨-, -, -, hcyc, hMcard, -⟩ :=
    unitary_central_cover_subline_automorphism_two_part J f hf hcard hfixed hJ (scalarCenter J)
      le_rfl
  set φ := (QuotientGroup.mk' (scalarCenter J)).comp (torusHom J hJ)
  have hker : φ.ker = (powMonoidHom 3 : normOne J →* normOne J).ker := by
    ext c
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, torusHom_mem_scalarCenter_iff, powMonoidHom_apply]
    constructor
    · intro h
      apply Subtype.ext
      apply Units.ext
      simpa using h
    · intro h
      have := congrArg (fun d : normOne J => ((d : Kˣ) : K)) h
      simpa using this
  have h1 : Nat.card (φ.ker.map (torusHom J hJ)) = Nat.card φ.ker :=
    Subgroup.card_map_of_injective (torusHom_injective hJ)
  rw [map_ker_torus_eq hJ le_rfl, hker, IsCyclic.card_powMonoidHom_ker, hMcard,
    Nat.gcd_comm] at h1
  exact h1

theorem card_torusL_scalarCenter {f : ℕ} (hf : 2 ≤ f) (hcard : Nat.card K = (2 ^ f) ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    Nat.card (torusL J (scalarCenter J) hJ) = (2 ^ f + 1) / Nat.gcd 3 (2 ^ f + 1) := by
  have hq : 2 < 2 ^ f := lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right two_pos hf)
  have h := card_torusL_mul_card (C := scalarCenter J) hJ le_rfl
  rw [card_normOne Nat.prime_two hq hcard hfixed, card_scalarCenter hf hcard hfixed hJ] at h
  exact (Nat.div_eq_of_eq_mul_left (Nat.gcd_pos_of_pos_left _ (by norm_num)) h.symm).symm

theorem center_eq_bot {f : ℕ} (hf : 2 ≤ f) (hcard : Nat.card K = (2 ^ f) ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    Subgroup.center (J.specialSubgroup ⧸ scalarCenter J) = ⊥ := by
  have hq : 2 < 2 ^ f := lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right two_pos hf)
  rw [center_eq_ker_coverToPSU hJ le_rfl (center_psu_eq_bot (2 ^ f) hq hcard hfixed hJ),
    eq_bot_iff]
  intro x hx
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective _ x
  have hg : g ∈ scalarCenter J := by
    rw [scalarCenter_eq_ker J hJ]
    exact hx
  exact (QuotientGroup.eq_one_iff g).mpr hg

end Finite

end CFSG.ProperTwoGeneratedCore.UnitaryPairIndex.Model
