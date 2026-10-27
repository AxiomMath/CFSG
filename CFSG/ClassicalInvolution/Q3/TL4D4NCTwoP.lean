module

public import CFSG.ClassicalInvolution.Q3.TL4D4NCTwo
public import CFSG.ClassicalInvolution.Q3.TL4D4NCOneP

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open QuadraticMap CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
open CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalGroups.Orthogonal.Small
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusBorel
open CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
open CFSG.ComponentClassification.CatalogueBOrthogonalPointAction
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open scoped Pointwise

variable {K : Type} [Field K]

theorem mul_self_add_one_ne_zero [Finite K] (hK : Nat.card K = 3) (c : K) : c * c + 1 ≠ 0 := by
  obtain ⟨-, h2⟩ := three_eq_zero_two_ne_zero_of_card_eq_three hK
  have : Fintype K := Fintype.ofFinite K
  have hc3 : c ^ 3 = c := by
    have h := FiniteField.pow_card c
    rwa [Fintype.card_eq_nat_card, hK] at h
  intro h
  have hcc : c * c = -1 := eq_neg_of_add_eq_zero_left h
  have hneg : c = -c := by
    calc c = c ^ 3 := hc3.symm
      _ = c * (c * c) := by ring
      _ = -c := by rw [hcc]; ring
  have h2c : (2 : K) * c = 0 := by linear_combination hneg
  have hc0 : c = 0 := (mul_eq_zero.mp h2c).resolve_left h2
  rw [hc0, mul_zero] at hcc
  exact one_ne_zero (neg_eq_zero.mp hcc.symm)

theorem typeII_smul [Finite K] (hK : Nat.card K = 3) (β : MulAut (D4P K))
    (hodd : Odd (orderOf β)) (g : StatedOmega (StatedQuadPlus 4 K))
    (hg2 : ∀ x, toLinEquiv _ K g.val (toLinEquiv _ K g.val x) = -x)
    (hβ : β (QuotientGroup.mk' _ g) = QuotientGroup.mk' _ g) :
    β • statedPointFamily (coe_quadPlus 4 K) = statedPointFamily (coe_quadPlus 4 K) := by
  obtain ⟨h3, h2⟩ := three_eq_zero_two_ne_zero_of_card_eq_three hK
  set φ := toLinEquiv _ K g.val with hφ
  have hφO : φ ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 K) :=
    toLinEquiv_mem_orthogonalGroup g
  have hQ := nondegenerate_polarBilin_quadPlus 4 K
  obtain ⟨m, hm, ⟨ab⟩⟩ := exists_adaptedBasis hK hQ hφO hg2
  rw [finrank_d4] at hm
  obtain rfl : m = 4 := by omega
  have hU : AB.U₀ ab ∈ singularSubspaces (quadPlus 4 K) 4 :=
    ⟨AB.finrank_U₀ ab, AB.U₀_singular ab h3 h2⟩
  obtain ⟨-, -, -, -, hor, -⟩ :=
    orthogonal_geometry_split_maximal_family_orbits (K := K) (r := 4) (by norm_num)
  have hno : ∀ L : Points (quadPlus 4 K),
      statedPointAction (coe_quadPlus 4 K) (QuotientGroup.mk' _ g) L ≠ L := by
    intro L hL
    obtain ⟨x, hx, hQx, rfl⟩ := exists_eq_pointMk L
    have h := congrArg Subtype.val hL
    rw [statedPointAction_mk_submodule, pointMk_submodule] at h
    have hφx : φ x ∈ Submodule.span K {x} := by
      rw [← h]
      exact ⟨x, Submodule.mem_span_singleton_self x, rfl⟩
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hφx
    have hφφ : φ (φ x) = (c * c) • x := by rw [← hc, map_smul, ← hc, smul_smul]
    rw [hg2] at hφφ
    have h0 : (c * c + 1) • x = 0 := by rw [add_smul, one_smul, ← hφφ, neg_add_cancel]
    rcases smul_eq_zero.mp h0 with h0 | h0
    · exact mul_self_add_one_ne_zero hK c h0
    · exact hx h0
  obtain ⟨Z, hZX, u, hu⟩ : ∃ Z : Submodule K (Fin 4 ⊕ Fin 4 → K),
      (Z = flag 4 K 4 ∨ Z = Xstar 4 K (by norm_num)) ∧
        ∃ u : orthElementaryGroup (quadPlus 4 K), u • Z = AB.U₀ ab := by
    rcases hor _ hU with h | h
    · exact ⟨_, Or.inl rfl, MulAction.mem_orbit_iff.mp h⟩
    · exact ⟨_, Or.inr rfl, MulAction.mem_orbit_iff.mp h⟩
  have huΩ : (toLinEquiv _ K).symm (u : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) ∈
      StatedOmega (StatedQuadPlus 4 K) := by
    refine symm_mem_statedOmega ?_
    rw [CFSG.ClassicalGroups.Orthogonal.commutator_orthogonalGroup_quadPlus (by norm_num)]
    exact u.2
  have hact : statedProjectiveSubspaceAction (StatedQuadPlus 4 K)
      (QuotientGroup.mk' _ ⟨_, huΩ⟩) Z = AB.U₀ ab := by
    rw [statedProjectiveSubspaceAction_mk_apply, ← hu]
    simp only [MulEquiv.apply_symm_apply]
    rfl
  refine smul_pointFamily_of_fixMax β hodd (QuotientGroup.mk' _ g)
    (QuotientGroup.mk' _ ⟨_, huΩ⟩) hβ Z hZX ?_ hno
  rw [hact, statedProjectiveSubspaceAction_mk_apply]
  exact AB.map_U₀ ab hg2

end CFSG.ClassicalInvolution.Q3.TL4
