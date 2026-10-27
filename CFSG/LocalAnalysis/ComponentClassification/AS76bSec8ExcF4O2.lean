module

public import CFSG.LieType.Chevalley.EvenOddCentralizerRadicalTwisted
public import CFSG.LieType.Chevalley.GraphFixedF4Group

public noncomputable section

namespace CFSG.ComponentClassification.RankTwoExceptional.F4Sec8

open Subgroup
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable {K : Type} [Field K]

theorem eq_bot_of_normal_centralizer_F4
    [Finite K] [CharP K 2] (S : Subgroup (adjointGroup .F4 K)) (hS : Odd (Nat.card S))
    (N : Subgroup (adjointGroup .F4 K))
    (hNC : N ≤ centralizer (S : Set (adjointGroup .F4 K)))
    (hNn : (N.subgroupOf (centralizer (S : Set (adjointGroup .F4 K)))).Normal)
    (hN2 : IsPGroup 2 N) : N = ⊥ := by
  have hK2 : ringChar K = 2 := ringChar.eq K 2
  obtain ⟨hΓ, -, -, -, ⟨Ψ, -⟩, -⟩ := even_E6_pure_graph_fixed_group_exact_F4 K hK2
  set Γ := twistedFixedGroup TwistTag.E6 K (RingHom.id K) with hΓdef
  set φ : adjointGroup .F4 K →* ModGL TwistTag.E6.tag K := Γ.subtype.comp Ψ.symm.toMonoidHom
    with hφ
  have hφinj : Function.Injective φ := Γ.subtype_injective.comp Ψ.symm.injective
  have hφΓ : ∀ c, φ c ∈ Γ := fun c => (Ψ.symm c).2
  have hΓφ : ∀ y ∈ Γ, ∃ c, φ c = y := fun y hy => ⟨Ψ ⟨y, hy⟩, by simp [hφ]⟩
  have hC₀ : graphFixedRootGroup .E6 K (RingEquiv.refl K).toRingHom = Γ := hΓ.symm
  have hSG : S.map φ ≤ graphFixedRootGroup .E6 K (RingEquiv.refl K).toRingHom := by
    rw [hC₀]
    rintro _ ⟨s, -, rfl⟩
    exact hφΓ s
  have hSodd : Odd (Nat.card (S.map φ)) := by
    rwa [Subgroup.card_map_of_injective hφinj]
  have hcent : ∀ c, φ c ∈ centralizer ((S.map φ : Subgroup _) : Set (ModGL TwistTag.E6.tag K)) ↔
      c ∈ centralizer (S : Set (adjointGroup .F4 K)) := fun c => by
    simp only [mem_centralizer_iff, SetLike.mem_coe, mem_map, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂]
    refine forall₂_congr fun s _ => ?_
    rw [← map_mul, ← map_mul]
    exact hφinj.eq_iff
  have hNC' : N.map φ ≤ graphFixedRootGroup .E6 K (RingEquiv.refl K).toRingHom ⊓
      centralizer ((S.map φ : Subgroup _) : Set (ModGL TwistTag.E6.tag K)) := by
    rintro _ ⟨n, hn, rfl⟩
    exact mem_inf.2 ⟨hC₀ ▸ hφΓ n, (hcent n).2 (hNC hn)⟩
  have hNn' : ((N.map φ).subgroupOf (graphFixedRootGroup .E6 K (RingEquiv.refl K).toRingHom ⊓
      centralizer ((S.map φ : Subgroup _) : Set (ModGL TwistTag.E6.tag K)))).Normal := by
    rw [normal_subgroupOf_iff hNC']
    rintro _ y ⟨n, hn, rfl⟩ hy
    obtain ⟨hyΓ, hyc⟩ := mem_inf.1 hy
    obtain ⟨c, rfl⟩ := hΓφ y (hC₀ ▸ hyΓ)
    have hc := (hcent c).1 hyc
    have h := (normal_subgroupOf_iff hNC).1 hNn n c hn hc
    exact ⟨c * n * c⁻¹, h, by simp [map_mul, map_inv]⟩
  have hN2' : IsPGroup 2 (N.map φ) := hN2.map φ
  have hσ : (RingEquiv.refl K) ^ TwistTag.E6.order = 1 := by
    rw [show TwistTag.E6.order = 2 from rfl, pow_two]
    rfl
  have h := EvenOddRadical.eq_bot_of_normal_centralizer_twistedE6 (RingEquiv.refl K) hσ hSG
    hSodd hNC' hNn' hN2'
  rw [eq_bot_iff]
  intro n hn
  have : φ n ∈ N.map φ := mem_map_of_mem φ hn
  rw [h, mem_bot] at this
  exact (mem_bot).2 (hφinj (this.trans (map_one φ).symm))

end CFSG.ComponentClassification.RankTwoExceptional.F4Sec8
