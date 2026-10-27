module

public import CFSG.LieType.Ree.SmallReeFrattiniTorusNormalizer
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiOppositeSylow

public section

namespace CFSG.LieType.Ree

open CFSG.LocalAnalysis.ComponentInitial CFSG.OrderReductions.FrattiniAutomorphisms
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

variable {G : Type*} [Group G]

theorem apply_mem_iff_of_map_eq {α : MulAut G} {H : Subgroup G} (hα : H.map α.toMonoidHom = H)
    (y : G) : α y ∈ H ↔ y ∈ H := by
  conv_lhs => rw [← hα]
  rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]

theorem apply_mem_normalizer_of_map_eq {α : MulAut G} {H : Subgroup G}
    (hα : H.map α.toMonoidHom = H) {t : G} (ht : t ∈ Subgroup.normalizer (H : Set G)) :
    α t ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at ht ⊢
  intro x
  have e : α t * x * (α t)⁻¹ = α (t * α.symm x * t⁻¹) := by
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  rw [e, apply_mem_iff_of_map_eq hα, ← ht, ← apply_mem_iff_of_map_eq hα (α.symm x),
    MulEquiv.apply_symm_apply]

theorem small_Ree_Sylow_torus_Schreier_criterion {Ω : Type*} [Finite G] [MulAction G Ω]
    [Finite Ω] [MulAction.IsPretransitive G Ω] [FaithfulSMul G Ω] (hΩ : 3 ≤ Nat.card Ω)
    (ξ : Ω) {p : ℕ} [Fact p.Prime] (U : Sylow p G)
    (hUξ : (U : Subgroup G) ≤ MulAction.stabilizer G ξ)
    (hUn : ((U : Subgroup G).subgroupOf (MulAction.stabilizer G ξ)).Normal)
    (htr : ∀ ω ω' : Ω, ω ≠ ξ → ω' ≠ ξ → ∃ u : (U : Subgroup G), (u : G) • ω = ω')
    (w : G) (hw : w • ξ ≠ ξ) {n : ℕ} (hn : 1 ≤ n) {K : Type*} [Field K]
    (hK : Nat.card K = p ^ n)
    (e : Additive ((U : Subgroup G) ⧸ frattini (U : Subgroup G)) ≃+ K)
    (hT : (((Subgroup.normalizer (((U : Subgroup G).map (MulAut.conj w).toMonoidHom :
        Subgroup G) : Set G)).subgroupOf (Subgroup.normalizer ((U : Subgroup G) : Set G))).map
          (U : Subgroup G).normalizerMonoidHom).map (frattiniScalarRep e) = scalarAddAut K) :
    Group.IsSolvable (Outer G) := by
  set V := (U : Subgroup G).map (MulAut.conj w).toMonoidHom with hV
  set Th : Subgroup (MulAut (U : Subgroup G)) :=
    ((Subgroup.normalizer (V : Set G)).subgroupOf
      (Subgroup.normalizer ((U : Subgroup G) : Set G))).map
        (U : Subgroup G).normalizerMonoidHom with hTh
  obtain ⟨-, hinj, hprod, -⟩ := Suzuki_opposite_Sylow_restriction hΩ ξ U hUξ hUn htr w hw
  set C := pairAutSubgroup (U : Subgroup G) V with hC
  set r := pairAutRestrict (U : Subgroup G) V with hr
  have hconj : ∀ (α : C) (t : Subgroup.normalizer ((U : Subgroup G) : Set G)),
      r α * (U : Subgroup G).normalizerMonoidHom t * (r α)⁻¹ =
        (U : Subgroup G).normalizerMonoidHom
          ⟨(α : MulAut G) t, apply_mem_normalizer_of_map_eq α.2.1 t.2⟩ := by
    intro α t
    refine MulEquiv.ext fun u => Subtype.ext ?_
    change (α : MulAut G) ((t : G) * (α : MulAut G).symm (u : G) * (t : G)⁻¹) =
      (α : MulAut G) t * u * ((α : MulAut G) t)⁻¹
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  have hmapTh : ∀ (α : C), ∀ φ ∈ Th, r α * φ * (r α)⁻¹ ∈ Th := by
    intro α φ hφ
    rw [hTh] at hφ ⊢
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 hφ
    rw [hconj]
    refine Subgroup.mem_map.2 ⟨⟨(α : MulAut G) t, apply_mem_normalizer_of_map_eq α.2.1 t.2⟩,
      ?_, rfl⟩
    rw [Subgroup.mem_subgroupOf] at ht ⊢
    exact apply_mem_normalizer_of_map_eq α.2.2 ht
  have hrN : ∀ α : C, r α ∈ Subgroup.normalizer (Th : Set (MulAut (U : Subgroup G))) := by
    intro α
    rw [Subgroup.mem_normalizer_iff]
    intro φ
    refine ⟨hmapTh α φ, fun h => ?_⟩
    have h2 := hmapTh α⁻¹ _ h
    rw [map_inv, inv_inv] at h2
    have h3 : (r α)⁻¹ * (r α * φ * (r α)⁻¹) * r α = φ := by group
    rwa [h3] at h2
  have hN := (small_Ree_Frattini_torus_normalizer_solvable p U.isPGroup' n hn hK e Th hT).2
  let r' : C →* Subgroup.normalizer (Th : Set (MulAut (U : Subgroup G))) := r.codRestrict _ hrN
  have hr' : Function.Injective r' := fun α β h => hinj (congrArg Subtype.val h)
  have hCsolv : Group.IsSolvable C := Group.isSolvable_of_isSolvable_injective hr'
  let π : C →* Outer G := (QuotientGroup.mk' (inner G)).comp C.subtype
  have hπ : Function.Surjective π := by
    intro q
    obtain ⟨α, rfl⟩ := QuotientGroup.mk'_surjective (inner G) q
    obtain ⟨g, β, hβ, rfl⟩ := hprod α
    refine ⟨⟨β, hβ⟩, ?_⟩
    change ((β : MulAut G) : Outer G) = ((MulAut.conj g * β : MulAut G) : Outer G)
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff (N := inner G) (MulAut.conj g)).2 ⟨g, rfl⟩,
      one_mul]
  exact Group.isSolvable_of_surjective hπ

end CFSG.LieType.Ree
