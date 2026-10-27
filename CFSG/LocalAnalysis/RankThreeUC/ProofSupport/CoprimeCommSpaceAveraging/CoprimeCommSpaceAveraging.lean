module

public import CFSG.LinearAlgebra.CoprimeActions.CommSpaceSubrepresentation

public section

namespace CFSG.LocalAnalysis.RankThreeUC.ProofSupport.CoprimeCommSpaceAveraging

open CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations CFSG.LinearAlgebra.CoprimeActions.CommSpaceSubrepresentation

variable {G : Type} [Group G] {p : ℕ} [Fact (Nat.Prime p)] {W : Type*} [AddCommGroup W]
  [Module (ZMod p) W]

private theorem card_cast {Z : Subgroup G} [Finite Z] [Fintype Z]
    (hc : ((Nat.card Z : ℕ) : ZMod p) ≠ 0) : ((Fintype.card Z : ℕ) : ZMod p) ≠ 0 := by
  rwa [← Nat.card_eq_fintype_card]

private theorem sub_mem_comm (ρ : Representation (ZMod p) G W) (Z : Subgroup G) [Fintype Z]
    (hc : ((Fintype.card Z : ℕ) : ZMod p) ≠ 0) (v : W) :
    v - ((Fintype.card Z : ℕ) : ZMod p)⁻¹ • normOp ρ Z v ∈ commSpace ρ Z := by
  have hs : ∑ z : Z, (ρ z v - v) ∈ commSpace ρ Z :=
    Submodule.sum_mem _ (fun z _ => Submodule.subset_span ⟨(z : G), z.2, v, rfl⟩)
  have he : v - ((Fintype.card Z : ℕ) : ZMod p)⁻¹ • normOp ρ Z v =
      -(((Fintype.card Z : ℕ) : ZMod p)⁻¹ • ∑ z : Z, (ρ z v - v)) := by
    rw [normOp_apply, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      ← Nat.cast_smul_eq_nsmul (ZMod p), smul_sub, smul_smul, inv_mul_cancel₀ hc, one_smul]
    simp
  rw [he]
  exact Submodule.neg_mem _ (Submodule.smul_mem _ _ hs)

theorem split [Finite G] (ρ : Representation (ZMod p) G W) (Z : Subgroup G)
    (_hZ : IsMulCommutative Z) (hc : ((Nat.card Z : ℕ) : ZMod p) ≠ 0) :
    commSpace ρ Z ⊔ fixedSpace ρ Z = ⊤ := by
  classical
  haveI : Fintype Z := Fintype.ofFinite _
  have hc' := card_cast (Z := Z) hc
  rw [eq_top_iff]
  intro v _
  have : v = (v - ((Fintype.card Z : ℕ) : ZMod p)⁻¹ • normOp ρ Z v) +
      ((Fintype.card Z : ℕ) : ZMod p)⁻¹ • normOp ρ Z v := by abel
  rw [this]
  exact Submodule.add_mem_sup (sub_mem_comm ρ Z hc' v)
    (Submodule.smul_mem _ _ (mem_fixedSpace_normOp ρ Z v))

theorem restricted_commSpace_eq_top [Finite G] (ρ : Representation (ZMod p) G W) (Z : Subgroup G)
    (hZ : IsMulCommutative Z) (hc : ((Nat.card Z : ℕ) : ZMod p) ≠ 0)
    (hcentral : ∀ k ∈ Z, ∀ z ∈ Z, k * z = z * k) :
    commSpace (restrictedRepresentation ρ Z Z hcentral) (⊤ : Subgroup Z) = ⊤ := by
  classical
  haveI : Fintype Z := Fintype.ofFinite _
  have hc' := card_cast (Z := Z) hc
  rw [eq_top_iff]
  intro u _
  have hN := normOp_commSpace ρ Z u.2
  have key : u = -(((Fintype.card Z : ℕ) : ZMod p)⁻¹ •
      ∑ b : Z, (restrictedRepresentation ρ Z Z hcentral b u - u)) := by
    apply Subtype.ext
    simp only [Submodule.coe_neg, Submodule.coe_smul, Submodule.coe_sum, Submodule.coe_sub,
      restrictedRepresentation_apply_coe, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ]
    rw [← normOp_apply, hN, ← Nat.cast_smul_eq_nsmul (ZMod p), smul_sub]
    simp only [Submodule.coe_smul, smul_smul, inv_mul_cancel₀ hc', one_smul, smul_zero]
    simp
  rw [key]
  refine Submodule.neg_mem _ (Submodule.smul_mem _ _ (Submodule.sum_mem _ fun b _ => ?_))
  exact Submodule.subset_span ⟨b, Subgroup.mem_top _, u, rfl⟩

end CFSG.LocalAnalysis.RankThreeUC.ProofSupport.CoprimeCommSpaceAveraging
