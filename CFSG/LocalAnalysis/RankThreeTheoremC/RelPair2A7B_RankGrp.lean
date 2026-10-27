module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Frattini.Core
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConjAction
import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2A7B_RankMod

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open Subgroup CFSG
open scoped commutatorElement

variable {G : Type} [Group G]

theorem relIndex_eq_four_of_card [Finite G] {S₀ V : Subgroup G} (hS : S₀ ≤ V)
    (hcard : Nat.card V = 4 * Nat.card S₀) : S₀.relIndex V = 4 := by
  have h := Subgroup.relIndex_mul_card (H := S₀) (K := V)
  rw [inf_of_le_left hS] at h
  have hpos : 0 < Nat.card S₀ := Nat.card_pos
  rw [hcard] at h
  nlinarith

theorem sup_eq_of_relIndex_eq [Finite G] {X S₀ V : Subgroup G} (hXV : X ≤ V) (hS : S₀ ≤ V)
    (hcard : Nat.card V = 4 * Nat.card S₀) (hX : S₀.relIndex X = 4) : X ⊔ S₀ = V := by
  have hle : X ⊔ S₀ ≤ V := sup_le hXV hS
  have h1 : S₀.relIndex X ≤ S₀.relIndex (X ⊔ S₀) :=
    Subgroup.relIndex_le_of_le_right le_sup_left (Subgroup.index_ne_zero_of_finite)
  have h2 := Subgroup.relIndex_mul_card (H := S₀) (K := X ⊔ S₀)
  rw [inf_of_le_left le_sup_right] at h2
  have hpos : 0 < Nat.card S₀ := Nat.card_pos
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [hcard, ← h2]
  rw [hX] at h1
  nlinarith

theorem natCard_subgroupOf_eq_inf (U X : Subgroup G) :
    Nat.card (U.subgroupOf X) = Nat.card (U ⊓ X : Subgroup G) := by
  rw [← Subgroup.inf_subgroupOf_right]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv

theorem rank_step [Finite G] {M X S₀ U : Subgroup G} {z a b : G}
    (hX2 : IsPGroup 2 X) (hMX : M ≤ normalizer (X : Set G))
    (hzM : z ∈ M) (haM : a ∈ M) (hbM : b ∈ M)
    (hz : z = a * b * a⁻¹ * b⁻¹) (hz3 : z ^ 3 = 1) (hza : z * a = a * z) (hzb : z * b = b * z)
    (hznc : ∃ x ∈ X, z * x ≠ x * z) (hzS : z ∈ normalizer (S₀ : Set G)) (hUS : U ≤ S₀)
    (hcomm : ∀ s ∈ S₀, s * z * s⁻¹ * z⁻¹ ∈ U) (hidx : S₀.relIndex X ≤ 4)
    (hU : Nat.card U = 16) (hXU : X ≤ normalizer (U : Set G)) :
    S₀.relIndex X = 4 ∧ U ≤ X ∧ ∀ x ∈ X, ∀ u ∈ U, u * x = x * u := by
  let : MulDistribMulAction M X := Subgroup.conjMulDistribMulActionOfLeNormalizer M X hMX
  have hsmul : ∀ (g : M) (x : X), ((g • x : X) : G) = (g : G) * (x : G) * (g : G)⁻¹ :=
    fun _ _ => rfl
  obtain ⟨hidx4, hU16, hbot⟩ := rank_filtration_action (R := X) (A := M) hX2
    (a := ⟨a, haM⟩) (b := ⟨b, hbM⟩) (z := ⟨z, hzM⟩)
    (Subtype.ext hz) (Subtype.ext (by simpa using hz3)) (Subtype.ext hza) (Subtype.ext hzb)
    (by
      obtain ⟨x, hx, hne⟩ := hznc
      refine ⟨⟨x, hx⟩, fun h => hne ?_⟩
      have h' : z * x * z⁻¹ = x := by
        have := congrArg Subtype.val h
        rwa [hsmul] at this
      exact mul_inv_eq_iff_eq_mul.mp h')
    (U.subgroupOf X) (S₀.subgroupOf X) (fun r hr => hUS hr)
    (fun r hr => by
      have hr' : (r : G) ∈ S₀ := hr
      change (z * (r : G) * z⁻¹) ∈ S₀
      exact (mem_normalizer_iff.mp hzS _).mp hr')
    (fun r hr => by
      have hr' : (r : G) ∈ S₀ := hr
      change z * (r : G) * z⁻¹ * (r : G)⁻¹ ∈ U
      have := U.inv_mem (hcomm _ hr')
      convert this using 1
      group)
    hidx (by
      rw [← hU, natCard_subgroupOf_eq_inf]
      exact Subgroup.card_le_of_le inf_le_left)
  have hUX : U ≤ X := by
    have h : U ⊓ X = U := Subgroup.eq_of_le_of_card_ge inf_le_left
      (by rw [hU, ← natCard_subgroupOf_eq_inf, hU16])
    exact h ▸ inf_le_right
  refine ⟨hidx4, hUX, fun x hx u hu => ?_⟩
  have hu' : u ∈ X := hUX hu
  have hcU : u * x * u⁻¹ * x⁻¹ ∈ U := by
    have h1 : x * u⁻¹ * x⁻¹ ∈ U := (mem_normalizer_iff.mp (hXU hx) _).mp (U.inv_mem hu)
    have := U.mul_mem hu h1
    convert this using 1
    group
  have hmemΦ : (⟨u * x * u⁻¹ * x⁻¹, X.mul_mem (X.mul_mem (X.mul_mem hu' hx) (X.inv_mem hu'))
      (X.inv_mem hx)⟩ : X) ∈ frattini X := by
    have : Fact (IsPGroup 2 X) := ⟨hX2⟩
    refine commutator_le_frattini_of_isPGroup (p := 2) ?_
    have hc : (⟨u * x * u⁻¹ * x⁻¹, X.mul_mem (X.mul_mem (X.mul_mem hu' hx) (X.inv_mem hu'))
        (X.inv_mem hx)⟩ : X) = ⁅(⟨u, hu'⟩ : X), (⟨x, hx⟩ : X)⁆ := by
      apply Subtype.ext
      simp [commutatorElement_def]
    rw [hc, _root_.commutator_def]
    exact Subgroup.commutator_mem_commutator (mem_top _) (mem_top _)
  have h1 : (⟨u * x * u⁻¹ * x⁻¹, X.mul_mem (X.mul_mem (X.mul_mem hu' hx) (X.inv_mem hu'))
      (X.inv_mem hx)⟩ : X) ∈ U.subgroupOf X ⊓ frattini X := ⟨hcU, hmemΦ⟩
  rw [hbot, Subgroup.mem_bot] at h1
  have h2 : u * x * u⁻¹ * x⁻¹ = 1 := congrArg Subtype.val h1
  calc u * x = (u * x * u⁻¹ * x⁻¹) * x * u := by group
    _ = x * u := by rw [h2, one_mul]

end CFSG.LocalAnalysis.RankThreeTheoremC
