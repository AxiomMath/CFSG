module

public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.Charts

public section

namespace CFSG.ClassicalGroups.Orthogonal.UnitaryOmega

open CFSG.ClassicalInvolution.PhanDn CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial CFSG.Timmesfeld.ClassicalOrders
open CFSG.SeitzReduction.UnitaryPilot CFSG.Permutation.ProperSupportMaps

variable {F K : Type} [Field F] [Field K] [Algebra F K] [Finite K] [CharP K 2] {f : ℕ}
  (E : QuadExt F K (unitaryInvolution K 2 f))

private theorem exists_anchorBlock_of_mem_normBlock_pair_three {x : normOmega E (3 + 1)}
    (hx : x ∈ normBlock E (3 + 1) {0, 1}) :
    ∃ z ∈ anchorBlock E (by norm_num : 2 ≤ 3), x = normOmegaCast E (Nat.le_succ 3) z := by
  have h01 : normBlock E (3 + 1) {0, 1} = anchorBlock E (by norm_num : 2 ≤ 3 + 1) := by
    rw [anchorBlock_eq_normBlock]
    rfl
  rw [h01] at hx
  obtain ⟨w, hw⟩ := MonoidHom.mem_range.mp hx
  refine ⟨normOmegaCast E (by norm_num : 2 ≤ 3) w, MonoidHom.mem_range.mpr ⟨w, rfl⟩, ?_⟩
  rw [← hw, ← MonoidHom.comp_apply, normOmegaCast_comp]

private theorem deletionChart_apply_of_coe_eq {H : Type} [Group H] {m : ℕ} (κ : normOmega E m →* H)
    (x : normBlock E (m + 1) (deletionSet (Fin.last m))) {z : normOmega E m}
    (hx : (x : normOmega E (m + 1)) = normOmegaCast E (Nat.le_succ m) z) :
    deletionChart E m κ x = κ z := by
  have hmem : normOmegaCast E (Nat.le_succ m) z ∈
      normBlock E (m + 1) (deletionSet (Fin.last m)) := by
    rw [← hx]
    exact x.2
  have hx' : x = ⟨normOmegaCast E (Nat.le_succ m) z, hmem⟩ := Subtype.ext hx
  rw [hx']
  exact deletionChart_apply E m κ z hmem

theorem deletionChart_pairCovariance_three {H : Type} [Group H]
    (t : Equiv.Perm (Fin (3 + 1)) →* H) (κ : normOmega E 3 →* H)
    (hT1 : t.comp (Equiv.Perm.viaEmbeddingHom Fin.castSuccEmb) = κ.comp (normPerm E le_rfl))
    (hC : ∀ y ∈ (anchorBlock E (by norm_num : 2 ≤ 3)).map κ, Commute (t (Equiv.swap 2 3)) y) :
    ∀ (P : Finset (Fin (3 + 1))) (σ : Equiv.Perm (Fin (3 + 1))) (hPcard : P.card = 2)
      (hPD : P ⊆ deletionSet (Fin.last 3)) (hPσD : P.image σ ⊆ deletionSet (Fin.last 3))
      (x : normBlock E (3 + 1) P),
        deletionChart E 3 κ (Subgroup.inclusion (normBlock_mono E (3 + 1) hPσD)
            (conjMapHom (map_normBlock_normPerm E (by norm_num : 3 ≤ 3 + 1)) σ P x)) =
          t σ * deletionChart E 3 κ (Subgroup.inclusion (normBlock_mono E (3 + 1) hPD) x) *
            (t σ)⁻¹ := by
  intro P σ hPcard hPD hPσD x
  have hn : 3 ≤ 3 + 1 := by norm_num
  have huv : (0 : Fin (3 + 1)) ≠ 1 := by decide
  have hcu : (2 : Fin (3 + 1)) ≠ 0 := by decide
  have hcv : (2 : Fin (3 + 1)) ≠ 1 := by decide
  have hdu : Fin.last 3 ≠ (0 : Fin (3 + 1)) := by decide
  have hdv : Fin.last 3 ≠ (1 : Fin (3 + 1)) := by decide
  have hcd : (2 : Fin (3 + 1)) ≠ Fin.last 3 := by decide
  have hineq : normBlock E (3 + 1) {0, 1} ≤ normBlock E (3 + 1) (deletionSet (Fin.last 3)) :=
    normBlock_mono E (3 + 1) (pair_subset_deletionSet hdu.symm hdv.symm)
  have hbase : ∀ (τ : Equiv.Perm (Fin (3 + 1))) (y : normBlock E (3 + 1) {0, 1}),
      τ 0 = 0 → τ 1 = 1 →
      normPerm E hn τ * (y : normOmega E (3 + 1)) =
        (y : normOmega E (3 + 1)) * normPerm E hn τ :=
    fun τ y h0 h1 => normPerm_commute_normBlock_pair E hn huv τ y h0 h1
  have hcross : ∀ y : normBlock E (3 + 1) {0, 1},
      t (Equiv.swap 2 (Fin.last 3)) * deletionChart E 3 κ (Subgroup.inclusion hineq y) =
        deletionChart E 3 κ (Subgroup.inclusion hineq y) * t (Equiv.swap 2 (Fin.last 3)) := by
    intro y
    obtain ⟨z, hz, hyz⟩ := exists_anchorBlock_of_mem_normBlock_pair_three E y.2
    have hval : deletionChart E 3 κ (Subgroup.inclusion hineq y) = κ z := by
      refine deletionChart_apply_of_coe_eq E κ _ ?_
      rw [Subgroup.coe_inclusion]
      exact hyz
    rw [hval]
    exact hC (κ z) (Subgroup.mem_map_of_mem κ hz)
  exact pairCovariance_of_cross (d := Fin.last 3) (u := 0) (v := 1) (c := 2)
    (B := normBlock E (3 + 1)) (hB := normBlock_mono E (3 + 1))
    (ρ := normPerm E hn) (t := t) (a := deletionChart E 3 κ)
    (hBmap := map_normBlock_normPerm E hn) huv hcu hcv hdu hdv hcd
    (deletionChart_common E le_rfl t κ hT1) hbase hcross
    P σ hPcard hPD hPσD x

end CFSG.ClassicalGroups.Orthogonal.UnitaryOmega
