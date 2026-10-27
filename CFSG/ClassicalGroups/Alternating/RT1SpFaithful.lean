module

public import CFSG.ClassicalGroups.Alternating.RT1SpBasic
public import CFSG.RankThree.PartOne.KC.SymplecticIsotypicFixed

public section

namespace CFSG.ClassicalGroups.Alternating

open LinearMap (BilinForm)
open Module

variable {K : Type} [Field K] {N : Type*} [AddCommGroup N] [Module K N] {BN : BilinForm K N}

theorem center_Gsp_eq_bot [CharP K 2] (hBN : BN.IsAlt) (hBNnd : BN.Nondegenerate) :
    Subgroup.center (Gsp BN) = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  refine Gsp.ext' fun x => ?_
  have h1 : z * Tsp hBN x 1 * z⁻¹ = Tsp hBN x 1 := by
    rw [← Subgroup.mem_center_iff.mp hz (Tsp hBN x 1), mul_assoc, mul_inv_cancel, mul_one]
  rw [Tsp_conj hBN z x 1] at h1
  rw [Tsp_injective_one hBN hBNnd h1, Gsp.app_one]

theorem isSimpleGroup_Gsp [CharP K 2] [FiniteDimensional K N] (hq : 4 ≤ Nat.card K)
    (hBN : BN.IsAlt) (hBNnd : BN.Nondegenerate) (hdim : 2 ≤ finrank K N) :
    IsSimpleGroup (Gsp BN) := by
  have hQ := CFSG.RankThree.PartOne.KCSpIsotypic.isQuasisimple_sesqUnitaryGroup_of_alt hBN hBNnd
    hdim (Or.inl hq)
  rw [← CFSG.RankThree.PartOne.KCSpIsotypic.bilinIsometryGroup_eq_sesqUnitaryGroup] at hQ
  haveI : IsSimpleGroup (Gsp BN ⧸ Subgroup.center (Gsp BN)) := hQ.2.1
  exact ((QuotientGroup.quotientMulEquivOfEq (center_Gsp_eq_bot hBN hBNnd)).trans
    QuotientGroup.quotientBot).symm.isSimpleGroup

theorem injective_of_apply_Tsp_ne_one [CharP K 2] [FiniteDimensional K N] (hq : 4 ≤ Nat.card K)
    (hBN : BN.IsAlt) (hBNnd : BN.Nondegenerate) (hdim : 2 ≤ finrank K N) {H : Type*} [Group H]
    (ρ : Gsp BN →* H) {v : N} {c : K} (h : ρ (Tsp hBN v c) ≠ 1) : Function.Injective ρ := by
  haveI := isSimpleGroup_Gsp hq hBN hBNnd hdim
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ρ.ker with hker | hker
  · exact (MonoidHom.ker_eq_bot_iff ρ).mp hker
  · exact absurd (MonoidHom.mem_ker.mp (hker ▸ Subgroup.mem_top (Tsp hBN v c))) h

end CFSG.ClassicalGroups.Alternating
