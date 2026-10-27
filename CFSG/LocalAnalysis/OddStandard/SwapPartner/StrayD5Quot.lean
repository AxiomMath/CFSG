module

public import CFSG.LocalAnalysis.OddStandard.SwapPartner.AutProdLemmas
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup

open scoped commutatorElement

theorem comap_centralizer_map_eq {H : Type*} [Group H] (Z : Subgroup H) [Z.Normal]
    (hZ : Z ≤ center H) (A : Subgroup H) (hA : Group.IsPerfect A) :
    (centralizer ((A.map (QuotientGroup.mk' Z) : Subgroup (H ⧸ Z)) : Set (H ⧸ Z))).comap
      (QuotientGroup.mk' Z) = centralizer (A : Set H) := by
  apply le_antisymm
  · intro u hu
    rw [Subgroup.mem_comap] at hu
    rw [Subgroup.mem_centralizer_iff] at hu ⊢
    have hmemZ : ∀ a : ↥A, ⁅u, (a : H)⁆ ∈ Z := by
      intro a
      have hcomm : QuotientGroup.mk' Z u * QuotientGroup.mk' Z (a : H) =
          QuotientGroup.mk' Z (a : H) * QuotientGroup.mk' Z u :=
        (hu (QuotientGroup.mk' Z (a : H))
          (Subgroup.mem_map.mpr ⟨(a : H), a.2, rfl⟩)).symm
      rw [← QuotientGroup.ker_mk' Z, MonoidHom.mem_ker, map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr hcomm
    let φ : ↥A →* ↥(center H) :=
      { toFun := fun a => ⟨⁅u, (a : H)⁆, hZ (hmemZ a)⟩
        map_one' := by
          apply Subtype.ext
          simp
        map_mul' := by
          intro a b
          apply Subtype.ext
          have hb : ⁅u, (b : H)⁆ ∈ center H := hZ (hmemZ b)
          have hconj : (a : H) * ⁅u, (b : H)⁆ * (a : H)⁻¹ = ⁅u, (b : H)⁆ := by
            rw [Subgroup.mem_center_iff.mp hb (a : H), mul_assoc, mul_inv_cancel, mul_one]
          change u * ((a : H) * (b : H)) * u⁻¹ * ((a : H) * (b : H))⁻¹ =
            (u * (a : H) * u⁻¹ * (a : H)⁻¹) *
              (u * (b : H) * u⁻¹ * (b : H)⁻¹)
          calc u * ((a : H) * (b : H)) * u⁻¹ * ((a : H) * (b : H))⁻¹
              = ⁅u, (a : H) * (b : H)⁆ := rfl
            _ = ⁅u, (a : H)⁆ * (a : H) * ⁅u, (b : H)⁆ * (a : H)⁻¹ :=
                  commutatorElement_mul_right_eq_mul_conj u (a : H) (b : H)
            _ = ⁅u, (a : H)⁆ * ⁅u, (b : H)⁆ := by
                  conv_rhs => rw [← hconj]
                  group
            _ = (u * (a : H) * u⁻¹ * (a : H)⁻¹) *
                  (u * (b : H) * u⁻¹ * (b : H)⁻¹) := rfl }
    have hφker : φ.ker = ⊤ :=
      le_antisymm le_top (by
        rw [← hA.commutator_eq_top]
        exact Abelianization.commutator_subset_ker φ)
    have hφone (a : ↥A) : φ a = 1 := by
      have : a ∈ φ.ker := by rw [hφker]; trivial
      rwa [MonoidHom.mem_ker] at this
    intro a ha
    have h2 : ⁅u, a⁆ = 1 :=
      Subtype.ext_iff.mp (hφone ⟨a, ha⟩)
    exact (commutatorElement_eq_one_iff_mul_comm.mp h2).symm
  · intro u hu
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff] at *
    intro y hy
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hy
    rw [← map_mul, ← map_mul, hu a ha]

theorem card_le_four_of_card_le_eight {H : Type*} [Group H] [Finite H] (Z : Subgroup H)
    [Z.Normal] (hZ : Z ≤ center H) (hZ2 : Nat.card Z = 2) (A : Subgroup H)
    (hA : Group.IsPerfect A)
    (h8 : ∀ Q : Subgroup H, IsPGroup 2 Q → Q ≤ centralizer (A : Set H) → Nat.card Q ≤ 8)
    (U : Subgroup (H ⧸ Z)) (hU : IsPGroup 2 U)
    (hUA : U ≤ centralizer ((A.map (QuotientGroup.mk' Z) : Subgroup (H ⧸ Z)) : Set (H ⧸ Z))) :
    Nat.card U ≤ 4 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hB : U ≤ (QuotientGroup.mk' Z).range := by
    rw [QuotientGroup.range_mk']; exact le_top
  have hcard : Nat.card (U.comap (QuotientGroup.mk' Z)) = Nat.card U * 2 := by
    rw [card_comap_eq_of_le_range (QuotientGroup.mk' Z) U hB, QuotientGroup.ker_mk' Z, hZ2]
  have hleC : U.comap (QuotientGroup.mk' Z) ≤ centralizer (A : Set H) := by
    intro u hu
    rw [← comap_centralizer_map_eq Z hZ A hA]
    exact Subgroup.mem_comap.mpr (hUA (Subgroup.mem_comap.mp hu))
  obtain ⟨n, hn⟩ := hU.exists_card_eq
  have hP : IsPGroup 2 (U.comap (QuotientGroup.mk' Z)) := by
    apply IsPGroup.of_card (n := n + 1)
    rw [hcard, hn, pow_succ]
  have h8u := h8 (U.comap (QuotientGroup.mk' Z)) hP hleC
  omega

end CFSG.OddStandard.AltStdSec.SwapPartner
