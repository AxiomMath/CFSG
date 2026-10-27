module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.RootAutomorphismLayerKernel
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.LinearModelPointStructureTransport
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.RootCenterAutomorphismBasic

public section

namespace CFSG.ProperTwoGeneratedCore.RootCenter

open CFSG.ShultStronglyClosedTI CFSG.ShultStronglyClosedTI.LinearModel
open CFSG.BenderSuzuki.MatrixGroups

universe u

theorem linear_rank_one_Sylow_layer_kernel_of_mulEquiv {G : Type*} [Group G] {K : Type u}
    [Field K] [Finite K] {f : ℕ} (hf : 2 ≤ f) (hcard : Nat.card K = 2 ^ f)
    (e : G ≃* PSL2MatrixGroup K) (Q : Sylow 2 G) (V : Subgroup G)
    (hV : V = (CFSG.omega₁ (G := (Q : Subgroup G)) (p := 2)).map (Q : Subgroup G).subtype)
    (γ : MulAut G) (hγQ : (Q : Subgroup G).map γ.toMonoidHom = Q)
    (hγV : ∀ v ∈ V, γ v = v) (hγQV : ∀ x ∈ (Q : Subgroup G), x⁻¹ * γ x ∈ V) :
    ∃ b ∈ (Q : Subgroup G), γ = MulAut.conj b := by
  have : Finite G := Finite.of_equiv _ e.symm.toEquiv
  obtain ⟨T, β, h, hfaith⟩ := linearPointAction_cosets_of_mulEquiv hcard e Q
  have hVQ : V = Q := hV.trans (map_omega₁_eq_of_isElemAbelian h.isElemAbelian)
  subst hVQ
  have : MulAction.IsMultiplyPretransitive G
      (G ⧸ Subgroup.normalizer ((Q : Subgroup G) : Set G)) 2 := h.isMultiplyPretransitive
  have : MulAction.IsPretransitive G (G ⧸ Subgroup.normalizer ((Q : Subgroup G) : Set G)) :=
    MulAction.isPretransitive_of_is_two_pretransitive
  have : ((Q : Subgroup G).subgroupOf (Q : Subgroup G)).Characteristic := by
    rw [Subgroup.subgroupOf_self]
    infer_instance
  have hΩ : 3 ≤ Nat.card (G ⧸ Subgroup.normalizer ((Q : Subgroup G) : Set G)) := by
    rw [h.card_eq]
    have : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    omega
  have hcomm : ∀ v ∈ (Q : Subgroup G), ∀ x ∈ (Q : Subgroup G), v * x = x * v :=
    fun v hv x hx => congrArg Subtype.val (h.isElemAbelian.1.is_comm.comm ⟨v, hv⟩ ⟨x, hx⟩)
  refine regular_root_automorphism_layer_kernel hΩ h.ne Q h.le_stabilizer_left
    ((Subgroup.normal_subgroupOf_iff_le_normalizer h.le_stabilizer_left).2
      h.stabilizer_le_normalizer)
    (fun ω ω' h1 h2 => (h.regular ω ω' h1 h2).exists) (Q : Subgroup G) le_rfl hcomm
    (fun x y => ?_) (Or.inl rfl) γ hγQ hγV hγQV
  induction x using QuotientGroup.induction_on with | H x => ?_
  induction y using QuotientGroup.induction_on with | H y => ?_
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
    show x * y = y * x from Subtype.ext (hcomm _ x.2 _ y.2)]

theorem linear_rank_one_Sylow_layer_kernel {K : Type u} [Field K] [Finite K] (f : ℕ)
    (hf : 2 ≤ f) (hcard : Nat.card K = 2 ^ f) (Q : Sylow 2 (PSL2MatrixGroup K))
    (V : Subgroup (PSL2MatrixGroup K))
    (hV : V = (CFSG.omega₁ (G := (Q : Subgroup (PSL2MatrixGroup K))) (p := 2)).map
      (Q : Subgroup (PSL2MatrixGroup K)).subtype)
    (γ : MulAut (PSL2MatrixGroup K))
    (hγQ : (Q : Subgroup (PSL2MatrixGroup K)).map γ.toMonoidHom = Q)
    (hγV : ∀ v ∈ V, γ v = v) (hγQV : ∀ x ∈ (Q : Subgroup (PSL2MatrixGroup K)), x⁻¹ * γ x ∈ V) :
    ∃ b ∈ (Q : Subgroup (PSL2MatrixGroup K)), γ = MulAut.conj b :=
  linear_rank_one_Sylow_layer_kernel_of_mulEquiv hf hcard (MulEquiv.refl _) Q V hV γ hγQ hγV
    hγQV

theorem linear_rank_one_Sylow_layer_kernel_of_mulEquiv_psl2Binary {G : Type*} [Group G]
    {f : ℕ} (hf : 2 ≤ f) (e : G ≃* PSL2BinaryMatrixGroup f) (Q : Sylow 2 G) (V : Subgroup G)
    (hV : V = (CFSG.omega₁ (G := (Q : Subgroup G)) (p := 2)).map (Q : Subgroup G).subtype)
    (γ : MulAut G) (hγQ : (Q : Subgroup G).map γ.toMonoidHom = Q)
    (hγV : ∀ v ∈ V, γ v = v) (hγQV : ∀ x ∈ (Q : Subgroup G), x⁻¹ * γ x ∈ V) :
    ∃ b ∈ (Q : Subgroup G), γ = MulAut.conj b :=
  linear_rank_one_Sylow_layer_kernel_of_mulEquiv hf (GaloisField.card 2 f (by omega)) e Q V hV
    γ hγQ hγV hγQV

end CFSG.ProperTwoGeneratedCore.RootCenter
