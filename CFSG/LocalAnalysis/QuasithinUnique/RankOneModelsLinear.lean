module

public import CFSG.LocalAnalysis.QuasithinUnique.RankOneModelsBasic
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.LinearModelPointStructure

public section

namespace CFSG.QuasithinUnique

open CFSG.GorensteinWalter CFSG.Glauberman.Dickson CFSG.ShultStronglyClosedTI.LinearModel
open CFSG.BenderSuzuki.MatrixGroups
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K]

theorem linear_hasFieldScalarStructure {f : ℕ} (hcard : Nat.card K = 2 ^ f) :
    HasFieldScalarStructure (psl2UpperUnipotentSubgroup K) (2 ^ f) := by
  have hchar : CharP K 2 := charP_two_of_card hcard
  have hinj : Function.Injective (psl2UpperUnipotentHom K) :=
    (psl2QuotientMap_injective (K := K)).comp sl2UpperUnipotentHom_injective
  have hmem : ∀ a : Kˣ, splitTorusSLHom K a ∈ sl2Borel K := fun a =>
    (sl2_mem_stabilizer_infinity_iff _).mpr (by simp)
  have hconj : ∀ (a : Kˣ) (x : K), torusHom K a * psl2UpperUnipotentHom K (Multiplicative.ofAdd x) *
      (torusHom K a)⁻¹ = psl2UpperUnipotentHom K (Multiplicative.ofAdd (((a : K)) ^ 2 * x)) :=
    fun a x => by
      have h := sl2Borel_conj_upperUnipotent (hmem a) x
      change psl2QuotientMap K (splitTorusSLHom K a) * psl2QuotientMap K (sl2UpperUnipotent x) *
        (psl2QuotientMap K (splitTorusSLHom K a))⁻¹ =
          psl2QuotientMap K (sl2UpperUnipotent ((a : K) ^ 2 * x))
      rw [← map_inv, ← map_mul, ← map_mul, h]
      simp
  have h := hasFieldScalarStructure_of_regular_root (psl2ProjectiveInfinity K)
    (psl2UpperUnipotentSubgroup K) (torus K) K (psl2UpperUnipotentHom K) hinj le_rfl
    psl2UpperUnipotent_le_borel ?_ rootGroup_sup_torus.ge ?_ ?_ ?_
  · rw [hcard] at h
    exact h
  · intro ω u hu hω hfix
    have h1 := (rootGroup_regular hω hω).unique (y₁ := ⟨u, hu⟩) (y₂ := 1) hfix (one_smul _ _)
    exact congrArg Subtype.val h1
  · intro p hp x
    exact (rootGroup_commute hp ⟨Multiplicative.ofAdd x, rfl⟩).eq ▸ by group
  · rintro _ ⟨a, rfl⟩
    exact ⟨a ^ 2, fun x => by rw [hconj]; simp⟩
  · intro c
    obtain ⟨r, hr⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) (c : K)
    have hr0 : r ≠ 0 := fun h0 => c.ne_zero (by rw [hr, h0, mul_zero])
    refine ⟨torusHom K (Units.mk0 r hr0), ⟨_, rfl⟩, fun x => ?_⟩
    rw [hconj]
    simp [hr, sq]

end CFSG.QuasithinUnique
