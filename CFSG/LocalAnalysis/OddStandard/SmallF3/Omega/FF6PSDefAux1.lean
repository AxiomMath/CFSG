module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFStarDef
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2FivePocket
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6PSylow

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

private theorem ffOutFF6PSDef_card_ffStar (hQ : Q.Nondegenerate)
    (hπ : piOrth Q ∉ omegaGroup hQ) {S : Subgroup (OGroup Q)} (hS : S ≤ omegaGroup hQ) :
    Nat.card ↥(ffStar hQ S) = Nat.card ↥S := by
  rw [ffStar, Subgroup.card_map_of_injective (omegaToProj_injective_of_not_mem hQ hπ)]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS).toEquiv

theorem ffOutFF6PSDef_lift_ffStar_of_le (hQ : Q.Nondegenerate)
    (hπ : piOrth Q ∉ omegaGroup hQ) {S : Subgroup (OGroup Q)} (hS : S ≤ omegaGroup hQ) :
    ffLift hQ (ffStar hQ S) = S := by
  apply le_antisymm
  · intro g hg
    rw [mem_ffLift_iff] at hg
    obtain ⟨hΩ, hU⟩ := hg
    rw [mem_ffStar_iff] at hU
    obtain ⟨s, hs, hse⟩ := hU
    have hgs : g = (s : OGroup Q) := congrArg Subtype.val
      (omegaToProj_injective_of_not_mem hQ hπ hse).symm
    rw [hgs]
    exact hs
  · intro g hg
    rw [mem_ffLift_iff]
    refine ⟨hS hg, ?_⟩
    rw [mem_ffStar_iff]
    exact ⟨⟨g, hS hg⟩, hg, rfl⟩

theorem ffOutFF6PSDef_lift_card (hQ : Q.Nondegenerate) (hπ : piOrth Q ∉ omegaGroup hQ)
    (U : Subgroup ↥(omegaProj hQ)) : Nat.card ↥(ffLift hQ U) = Nat.card ↥U := by
  have h := ffOutFF6PSDef_card_ffStar hQ hπ (ffLift_le_omega hQ U)
  rw [ffStar_ffLift hQ U] at h
  exact h.symm

theorem ffOutFF6PSDef_lift_normalE16 (hQ : Q.Nondegenerate)
    (hπ : piOrth Q ∉ omegaGroup hQ) (fr : PFrame Q (Option (Fin 5)) ffC)
    {U : Subgroup ↥(omegaProj hQ)}
    (hU : IsNormalE16In (ffStar hQ (ffP0p hQ fr)) U) :
    IsNormalE16In (ffP0p hQ fr) (ffLift hQ U) := by
  have hUle : U ≤ ffStar hQ (ffP0p hQ fr) := hU.1
  have hliftle : ffLift hQ U ≤ ffP0p hQ fr := by
    rw [← ffOutFF6PSDef_lift_ffStar_of_le hQ hπ (ffP0p_le_omega hQ fr)]
    intro g hg
    rw [mem_ffLift_iff] at hg ⊢
    exact ⟨hg.1, hUle hg.2⟩
  have hmul_comm : ∀ a b : ↥(ffLift hQ U), a * b = b * a := by
    intro a b
    have haΩ : (a : OGroup Q) ∈ omegaGroup hQ := ffLift_le_omega hQ U a.2
    have hbΩ : (b : OGroup Q) ∈ omegaGroup hQ := ffLift_le_omega hQ U b.2
    have haU : omegaToProj hQ ⟨(a : OGroup Q), haΩ⟩ ∈ U :=
      ((mem_ffLift_iff hQ).mp a.2).2
    have hbU : omegaToProj hQ ⟨(b : OGroup Q), hbΩ⟩ ∈ U :=
      ((mem_ffLift_iff hQ).mp b.2).2
    have hEq : (⟨(a : OGroup Q) * (b : OGroup Q),
        (omegaGroup hQ).mul_mem haΩ hbΩ⟩ : omegaGroup hQ)
        = ⟨(b : OGroup Q) * (a : OGroup Q), (omegaGroup hQ).mul_mem hbΩ haΩ⟩ := by
      apply omegaToProj_injective_of_not_mem hQ hπ
      change omegaToProj hQ (⟨(a : OGroup Q), haΩ⟩ * ⟨(b : OGroup Q), hbΩ⟩) =
        omegaToProj hQ (⟨(b : OGroup Q), hbΩ⟩ * ⟨(a : OGroup Q), haΩ⟩)
      rw [map_mul, map_mul]
      haveI : IsMulCommutative ↥U := hU.2.1.1.1
      exact congrArg Subtype.val (mul_comm' (⟨_, haU⟩ : U) (⟨_, hbU⟩ : U))
    exact Subtype.ext (congrArg (fun x : ↥(omegaGroup hQ) => (x : OGroup Q)) hEq)
  have hsq : ∀ x ∈ ffLift hQ U, x * x = 1 := by
    intro x hx
    have hxΩ : x ∈ omegaGroup hQ := ffLift_le_omega hQ U hx
    have hxU : omegaToProj hQ ⟨x, hxΩ⟩ ∈ U := ((mem_ffLift_iff hQ).mp hx).2
    have hsqU : omegaToProj hQ ⟨x, hxΩ⟩ * omegaToProj hQ ⟨x, hxΩ⟩ = 1 := by
      simpa [pow_two] using hU.2.1.1.2 _ hxU
    have hmap : omegaToProj hQ ⟨x * x, (omegaGroup hQ).mul_mem hxΩ hxΩ⟩ = 1 := by
      change omegaToProj hQ (⟨x, hxΩ⟩ * ⟨x, hxΩ⟩) = 1
      rw [map_mul]
      exact hsqU
    have h1 : (⟨x * x, (omegaGroup hQ).mul_mem hxΩ hxΩ⟩ : omegaGroup hQ) = 1 := by
      apply omegaToProj_injective_of_not_mem hQ hπ
      rw [map_one]
      exact hmap
    exact congrArg Subtype.val h1
  refine ⟨hliftle, ⟨⟨IsMulCommutative.of_comm hmul_comm, ?_⟩, ?_⟩, ?_⟩
  · intro x hx
    rw [pow_two]
    exact hsq x hx
  · rw [ffOutFF6PSDef_lift_card hQ hπ U, hU.2.1.2]
  · rw [Subgroup.normal_subgroupOf_iff hliftle]
    intro n g hn hg
    have hnΩ : n ∈ omegaGroup hQ := ffLift_le_omega hQ U hn
    have hgΩ : g ∈ omegaGroup hQ := ffP0p_le_omega hQ fr hg
    have hnU : omegaToProj hQ ⟨n, hnΩ⟩ ∈ U := ((mem_ffLift_iff hQ).mp hn).2
    have hgP : omegaToProj hQ ⟨g, hgΩ⟩ ∈ ffStar hQ (ffP0p hQ fr) := by
      rw [mem_ffStar_iff]
      exact ⟨⟨g, hgΩ⟩, hg, rfl⟩
    have hconjU : omegaToProj hQ ⟨g, hgΩ⟩ * omegaToProj hQ ⟨n, hnΩ⟩ *
        (omegaToProj hQ ⟨g, hgΩ⟩)⁻¹ ∈ U :=
      (Subgroup.normal_subgroupOf_iff hUle).mp hU.2.2 _ _ hnU hgP
    rw [mem_ffLift_iff]
    refine ⟨(omegaGroup hQ).mul_mem ((omegaGroup hQ).mul_mem hgΩ hnΩ)
      ((omegaGroup hQ).inv_mem hgΩ), ?_⟩
    rw [show (⟨g * n * g⁻¹, _⟩ : omegaGroup hQ) =
      ⟨g, hgΩ⟩ * ⟨n, hnΩ⟩ * (⟨g, hgΩ⟩)⁻¹ from rfl, map_mul, map_mul, map_inv]
    exact hconjU

end CFSG.OddStandard.SmallF3.Omega
