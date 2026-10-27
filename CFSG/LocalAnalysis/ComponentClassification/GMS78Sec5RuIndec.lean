module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuJ

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard CFSG.BenderSuzuki.PFAppendixIII
open CFSG.GMS78Ru CFSG.GMS78RuSim CFSG.GMS78RuQ

namespace Sec3.SzR.MaskCoords

variable {G : Type} [Group G] [Finite G] {L T R : Subgroup G} {μ : G → ℕ} {ν : G → Fin 8}
  (hM : MaskCoords L T R μ ν)
include hM

omit [Finite G] in
theorem mem_J_iff_of_mem_R {S X J : Subgroup G} {f : G} (hfA : f ∈ gmsA L T) (hRS : R ≤ S)
    (hX : ∀ x, x ∈ X ↔ x ∈ R ∧ μ x ∈ 0 :: RuQCode.ppOf (ν f))
    (hJ : ∀ v, v ∈ J ↔ v ∈ S ∧ ∀ x ∈ X, v * x * v⁻¹ * x⁻¹ = 1 ∨ v * x * v⁻¹ * x⁻¹ = f)
    {v : G} (hv : v ∈ R) : v ∈ J ↔ μ v ∈ RuQCode.jlOf (ν f) := by
  rw [hJ, RuQCode.mem_jlOf]
  constructor
  · rintro ⟨-, h⟩
    refine ⟨hM.lt v hv, fun m hm => ?_⟩
    obtain ⟨x, hx, hxm⟩ := hM.surj m (RuQCode.ppOf_lt _ _ hm)
    have hxX : x ∈ X := (hX x).mpr ⟨hx, by rw [hxm]; exact List.mem_cons_of_mem _ hm⟩
    rw [← hxm, RuQCode.bC_comm, ← hM.comm hv hx]
    rcases h x hxX with h1 | h1
    · left
      rw [h1, hM.ν_one]
    · right
      rw [h1]
  · rintro ⟨-, h⟩
    refine ⟨hRS hv, fun x hx => ?_⟩
    obtain ⟨hxR, hxm⟩ := (hX x).mp hx
    have hc := hM.comm hv hxR
    have hcA := hM.comm_mem _ hv _ hxR
    rcases List.mem_cons.mp hxm with h' | h'
    · left
      rw [h', RuQCode.bC_zero_right] at hc
      exact hM.ν_inj _ hcA hc
    · rw [RuQCode.bC_comm] at hc
      rcases h _ h' with h1 | h1
      · left
        exact hM.ν_inj _ hcA (hc.trans h1)
      · right
        exact hM.eq_of_ν_eq hcA hfA (hc.trans h1)

omit [Finite G] in
theorem card_J_inf_R {S X J : Subgroup G} {f : G} (hfA : f ∈ gmsA L T) (hf1 : f ≠ 1)
    (hRS : R ≤ S) (hX : ∀ x, x ∈ X ↔ x ∈ R ∧ μ x ∈ 0 :: RuQCode.ppOf (ν f))
    (hJ : ∀ v, v ∈ J ↔ v ∈ S ∧ ∀ x ∈ X, v * x * v⁻¹ * x⁻¹ = 1 ∨ v * x * v⁻¹ * x⁻¹ = f) :
    Nat.card (J ⊓ R : Subgroup G) = 2 ^ 9 := by
  classical
  have ht : ν f ≠ 0 := fun h => hf1 (hM.ν_inj f hfA h)
  have hparts := RuQCode.jCheck_parts ht
  have hJR : ∀ v ∈ R, v ∈ J ↔ μ v ∈ RuQCode.jlOf (ν f) := fun v hv =>
    hM.mem_J_iff_of_mem_R hfA hRS hX hJ hv
  have hAJR : gmsA L T ≤ J ⊓ R := by
    intro b hb
    have hbR := hM.le hb
    refine mem_inf.mpr ⟨(hJR b hbR).mpr ?_, hbR⟩
    rw [(hM.ker _ hbR).mpr hb, RuQCode.mem_jlOf]
    exact ⟨by norm_num, fun m _ => Or.inl (RuQCode.bC_zero_right m)⟩
  have h := card_eq_length_mul_card hAJR μ (RuQCode.jlOf (ν f)) (RuQCode.jlOf_nodup _)
    (fun a ha => (hJR a (mem_inf.mp ha).2).mp (mem_inf.mp ha).1)
    (fun c hc => by
      obtain ⟨x, hx, hxc⟩ := hM.surj c (RuQCode.mem_jlOf.mp hc).1
      exact ⟨x, mem_inf.mpr ⟨(hJR x hx).mpr (by rw [hxc]; exact hc), hx⟩, hxc⟩)
    (fun a ha b hb => by
      have haR := (mem_inf.mp ha).2
      have hbR := (mem_inf.mp hb).2
      rw [← hM.ker _ (mul_mem (inv_mem haR) hbR), hM.mul _ (inv_mem haR) _ hbR, hM.μ_inv haR]
      exact ⟨fun h => by rw [h]; exact Nat.xor_self _, RuQCode.nat_eq_of_xor_eq_zero⟩)
  rw [hparts.2.1, hM.card_gmsA] at h
  rw [h]
  norm_num

end Sec3.SzR.MaskCoords

end CFSG.ComponentClassification.GMS78
