module

public import Mathlib.GroupTheory.PGroup
import CFSG.GroupTheory.CardMapInfKer
import CFSG.GroupTheory.CoprimeNormalizerSup
import CFSG.RankThree.OddKernel.OddLift

public section

namespace CFSG.GroupTheory

variable {G K : Type*} [Group G] [Group K] {Φ : G →* K}

theorem natCard_map_of_isPGroup_of_odd [Finite G] (hodd : Odd (Nat.card Φ.ker))
    {P : Subgroup G} (hP : IsPGroup 2 P) : Nat.card ↥(P.map Φ) = Nat.card ↥P :=
  CFSG.card_map_eq_card_of_inf_ker_eq_bot Φ
    (CFSG.RankThree.OddKernel.inf_eq_bot_of_odd hP hodd)

theorem le_of_map_le_map_of_odd [Finite G] (hcen : Φ.ker ≤ Subgroup.center G)
    (hodd : Odd (Nat.card Φ.ker)) {P Q : Subgroup G} (hP : IsPGroup 2 P)
    (h : P.map Φ ≤ Q.map Φ) : P ≤ Q := by
  have hPQ : P ≤ Q ⊔ Φ.ker := by
    calc P ≤ Subgroup.comap Φ (P.map Φ) := Subgroup.le_comap_map Φ P
      _ ≤ Subgroup.comap Φ (Q.map Φ) := Subgroup.comap_mono h
      _ = Q ⊔ Φ.ker := Subgroup.comap_map_eq Φ Q
  exact le_of_le_sup_of_isPGroup_of_not_dvd_card Nat.prime_two
    (hcen.trans (Subgroup.center_le_normalizer (Q : Set G))) hP hPQ
    (Odd.not_two_dvd_nat hodd)

theorem exists_isPGroup_map_eq_of_odd [Finite G] (hodd : Odd (Nat.card Φ.ker))
    {E : Subgroup K} (hE : E ≤ Φ.range) (hE2 : IsPGroup 2 E) :
    ∃ P : Subgroup G, IsPGroup 2 P ∧ P.map Φ = E ∧ Function.Injective (Φ.comp P.subtype) := by
  have hker : Odd (Nat.card Φ.rangeRestrict.ker) := by
    rw [MonoidHom.ker_rangeRestrict]
    exact hodd
  obtain ⟨P, hP2, hPmap, hPinj⟩ :=
    CFSG.RankThree.OddKernel.exists_two_subgroup_map_eq Φ.rangeRestrict
      (MonoidHom.rangeRestrict_surjective Φ) hker (E.subgroupOf Φ.range)
      (hE2.comap_of_injective Φ.range.subtype Φ.range.subtype_injective)
  refine ⟨P, hP2, ?_, ?_⟩
  · change P.map (Φ.range.subtype.comp Φ.rangeRestrict) = E
    rw [← Subgroup.map_map, hPmap, Subgroup.map_subgroupOf_eq_of_le hE]
  · have hcomp : Φ.comp P.subtype =
        Φ.range.subtype.comp (Φ.rangeRestrict.comp P.subtype) := rfl
    rw [hcomp]
    exact Φ.range.subtype_injective.comp hPinj

theorem ker_eq_center_of_centralizer_range_eq_bot (hcen : Φ.ker ≤ Subgroup.center G)
    (hC : Subgroup.centralizer (Φ.range : Set K) = ⊥) : Φ.ker = Subgroup.center G := by
  refine le_antisymm hcen fun z hz => ?_
  rw [MonoidHom.mem_ker]
  have hcent : Φ z ∈ Subgroup.centralizer (Φ.range : Set K) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨y, rfl⟩
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz y]
  rw [hC, Subgroup.mem_bot] at hcent
  exact hcent

theorem eq_of_forall_conj_eq {X : Subgroup K} (hC : Subgroup.centralizer (X : Set K) = ⊥)
    {w x : K} (h : ∀ y ∈ X, w * y * w⁻¹ = x * y * x⁻¹) : w = x := by
  have hz : x⁻¹ * w ∈ Subgroup.centralizer (X : Set K) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h' := h y hy
    calc y * (x⁻¹ * w) = x⁻¹ * (x * y * x⁻¹) * w := by group
      _ = x⁻¹ * (w * y * w⁻¹) * w := by rw [h']
      _ = (x⁻¹ * w) * y := by group
  have h1 : x⁻¹ * w = 1 := by simpa [hC] using hz
  exact (inv_mul_eq_one.mp h1).symm

end CFSG.GroupTheory
