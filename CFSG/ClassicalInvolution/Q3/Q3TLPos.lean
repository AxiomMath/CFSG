module

public import CFSG.ClassicalInvolution.Q3.Q3TLSpin
public import CFSG.ClassicalInvolution.Q3.Q3TLFam
public import CFSG.ClassicalInvolution.SmallOrth.Orth3Split

public section

namespace CFSG.ClassicalInvolution.Q3.Q3T

open Module QuadraticMap CFSG.LieType.Universal.Spin CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalGroups.Orthogonal.Small
open CFSG.ClassicalInvolution.ModelFacts
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusBorel
open CFSG.ComponentClassification.CatalogueBOrthogonalSmallFamilyOrbit
open CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open scoped Pointwise

variable {K : Type} [Field K] [Finite K]

omit [Finite K] in
theorem finrank_plusEight : finrank K (Fin 4 ⊕ Fin 4 → K) = 8 := by
  rw [finrank_fintype_fun_eq_card]
  simp

theorem fixFam_point_of_sq_eq_one (hK : Nat.card K = 3) (g : StatedOmega (StatedQuadPlus 4 K))
    (hg2 : toLinEquiv _ K g.val * toLinEquiv _ K g.val = 1) :
    FixFam (statedPointFamily (coe_quadPlus 4 K))
      (Subgroup.zpowers (QuotientGroup.mk g : StatedProj (StatedOmega (StatedQuadPlus 4 K)))) := by
  obtain ⟨-, h2⟩ := three_eq_zero_two_ne_zero_of_card_eq_three hK
  obtain ⟨G, hG⟩ : ∃ G, G = toLinEquiv _ K g.val := ⟨_, rfl⟩
  rw [← hG] at hg2
  have hsum := Submodule.finrank_add_eq_of_isCompl (isCompl_plusSp_minusSp h2 hg2)
  rw [finrank_plusEight] at hsum
  obtain ⟨w, hw0, hwQ, hGw⟩ : ∃ w, w ≠ 0 ∧ quadPlus 4 K w = 0 ∧ (G w = w ∨ G w = -w) := by
    by_cases h3 : 3 ≤ finrank K (plusSp G)
    · obtain ⟨w, hw, hw0, hwQ⟩ := exists_singular_of_three_le_finrank hK (plusSp G) h3
      exact ⟨w, hw0, hwQ, Or.inl (mem_plusSp.mp hw)⟩
    · obtain ⟨w, hw, hw0, hwQ⟩ := exists_singular_of_three_le_finrank hK (minusSp G) (by omega)
      exact ⟨w, hw0, hwQ, Or.inr (mem_minusSp.mp hw)⟩
  refine fixFam_point_of_le hw0 hwQ (Subgroup.zpowers_le.mpr ?_)
  rw [mk_mem_stabilizer_iff, ← hG, Submodule.map_span, Set.image_singleton, LinearEquiv.coe_coe]
  rcases hGw with h | h
  · rw [h]
  · rw [h, ← Set.neg_singleton, Submodule.span_neg]

theorem smul_eq_or_solid_of_sq_eq_one (hK : Nat.card K = 3)
    (β : MulAut (StatedProj (StatedOmega (StatedQuadPlus 4 K)))) {k : ℕ} (hβk : β ^ (3 ^ k) = 1)
    (g : StatedOmega (StatedQuadPlus 4 K))
    (hg2 : toLinEquiv _ K g.val * toLinEquiv _ K g.val = 1)
    (hβg : β (QuotientGroup.mk g) = QuotientGroup.mk g) :
    β • statedPointFamily (coe_quadPlus 4 K) = statedPointFamily (coe_quadPlus 4 K) ∨
      ∃ S ∈ singularSubspaces (quadPlus 4 K) 4,
        S.map (toLinEquiv _ K g.val).toLinearMap = S := by
  by_cases hX : FixFam (conjugacyFamily
      (statedProjectiveSubspaceStabilizer (StatedQuadPlus 4 K) (flag 4 K 4)))
      (Subgroup.zpowers (QuotientGroup.mk g : StatedProj (StatedOmega (StatedQuadPlus 4 K))))
  · right
    obtain ⟨S, hS, hle⟩ := exists_of_fixFam_solid hX
    exact ⟨S, hS, (mk_mem_stabilizer_iff g S).mp (hle (Subgroup.mem_zpowers _))⟩
  · left
    refine smul_eq_of_fixFam_point β hβk ?_ (fixFam_point_of_sq_eq_one hK g hg2) hX
    rw [MonoidHom.map_zpowers]
    exact congrArg Subgroup.zpowers hβg

theorem root_of_solid (hK : Nat.card K = 3) (g : StatedOmega (StatedQuadPlus 4 K))
    (hg2 : toLinEquiv _ K g.val * toLinEquiv _ K g.val = 1)
    (hgs : toLinEquiv _ K g.val ∉ scalars K (Fin 4 ⊕ Fin 4 → K))
    {S : Submodule K (Fin 4 ⊕ Fin 4 → K)} (hS : S ∈ singularSubspaces (quadPlus 4 K) 4)
    (hinv : S.map (toLinEquiv _ K g.val).toLinearMap = S) :
    finrank K (plusSp (toLinEquiv _ K g.val)) = 4 ∧
      finrank K (minusSp (toLinEquiv _ K g.val)) = 4 ∧
      finrank K ↥(S ⊓ plusSp (toLinEquiv _ K g.val)) = 2 ∧
      finrank K ↥(S ⊓ minusSp (toLinEquiv _ K g.val)) = 2 := by
  obtain ⟨-, h2⟩ := three_eq_zero_two_ne_zero_of_card_eq_three hK
  obtain ⟨G, hG⟩ : ∃ G, G = toLinEquiv _ K g.val := ⟨_, rfl⟩
  rw [← hG] at hg2 hgs hinv ⊢
  have hQ := nondegenerate_polarBilin_quadPlus 4 K
  have hGO : G ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 K) :=
    hG ▸ toLinEquiv_mem_orthogonalGroup g.2
  have hGE : G ∈ elementaryGroup (quadPlus 4 K) := hG ▸ toLinEquiv_mem_elementaryGroup g.2
  have hSG : ∀ v ∈ S, G v ∈ S := fun v hv => by
    rw [← hinv]
    exact ⟨v, hv, rfl⟩
  obtain ⟨ha, hb⟩ := two_mul_finrank_inf_eq hQ h2 hGO hg2 hSG hS.2
    (by rw [hS.1, finrank_plusEight])
  have hsum := Submodule.finrank_add_eq_of_isCompl (isCompl_plusSp_minusSp h2 hg2)
  rw [finrank_plusEight] at hsum
  have hP0 : plusSp G ≠ ⊥ := fun h => hgs (mem_scalars_of_plusSp_eq_bot h2 hg2 h)
  have hM0 : minusSp G ≠ ⊥ := fun h => hgs (mem_scalars_of_minusSp_eq_bot h2 hg2 h)
  have hP1 : finrank K (plusSp G) ≠ 0 := fun h => hP0 (Submodule.finrank_eq_zero.mp h)
  have hM1 : finrank K (minusSp G) ≠ 0 := fun h => hM0 (Submodule.finrank_eq_zero.mp h)
  have hev := even_of_mem_elementaryGroup hK hQ (plusPair_orth (K := K) (by decide :
    (0 : Fin 4) ≠ 1)) (plusPair_orth (by decide : (0 : Fin 4) ≠ 2))
    (plusPair_orth (by decide : (1 : Fin 4) ≠ 2)) hGE hg2 hb.symm (U := S ⊓ minusSp G)
    inf_le_right (fun x hx => hS.2 x hx.1) le_rfl
  obtain ⟨c, hc⟩ := hev
  omega

end CFSG.ClassicalInvolution.Q3.Q3T
