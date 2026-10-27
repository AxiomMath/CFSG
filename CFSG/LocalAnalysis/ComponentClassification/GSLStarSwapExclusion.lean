module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitChainWeak
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitElemAb
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitWeakMaximalDef
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ComponentClassification.Foote5.SolMax

open CFSG Subgroup CFSG.ComponentClassification CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.GrSLit

variable {G : Type} [Group G] [Finite G]

theorem gsWeakReach_conjugate {J K : Subgroup G} (h : GSWeakReach J K) (g : G) :
    GSWeakReach (conjugate J g) (conjugate K g) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hst ih =>
    obtain ⟨a, b, hC⟩ := hst
    exact Relation.ReflTransGen.tail ih ⟨_, _, gsWeakCorr_conjugate hC g⟩

theorem gsWeakCorr_self {a : G} {J : Subgroup G} (ha : orderOf a = 2)
    (hJa : J ≤ centralizer ({a} : Set G))
    (hJp : IsPComponent 2 (J.subgroupOf (centralizer ({a} : Set G)))) : GSWeakCorr a J a J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcomm : ∀ j ∈ J, j * a = a * j := fun j hj =>
    (mem_centralizer_singleton_iff.mp (hJa hj))
  refine ⟨ha, ha, rfl, hJa, hJp, hJa, hJp, ?_, ?_, ?_⟩
  · rw [mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      have := hcomm y hy
      rw [show a * y * a⁻¹ = y by rw [← this, mul_assoc, mul_inv_cancel, mul_one]]
      exact hy
    · intro hy
      have h1 : a * y * a⁻¹ ∈ J := hy
      have h2 := hcomm _ h1
      have hy' : y = a⁻¹ * (a * y * a⁻¹ * a) := by group
      rw [hy', h2, show a⁻¹ * (a * (a * y * a⁻¹)) = a * y * a⁻¹ by group]
      exact h1
  · intro j hj
    have := hcomm j hj
    have h1 : j⁻¹ * a⁻¹ * j * a = 1 := by
      calc j⁻¹ * a⁻¹ * j * a = j⁻¹ * a⁻¹ * (j * a) := by group
        _ = j⁻¹ * a⁻¹ * (a * j) := by rw [this]
        _ = 1 := by group
    rw [h1]; exact one_mem _
  · exact (UnbalancedGS.gsFixedLayer_le_inf J a).trans (inf_le_left.trans le_sup_left)

theorem gsWeakMaximalComponent_conjugate {J : Subgroup G} (hJ : GSWeakMaximalComponent J)
    (g : G) : GSWeakMaximalComponent (conjugate J g) := by
  obtain ⟨⟨a, ha, hJa, hJp⟩, hmax⟩ := hJ
  obtain ⟨ha', -, -, hJa', hJp', -⟩ := gsWeakCorr_conjugate (gsWeakCorr_self ha hJa hJp) g
  refine ⟨⟨_, ha', hJa', hJp'⟩, fun M hM => ?_⟩
  have hR : GSWeakReach J (conjugate M g⁻¹) := by
    have := gsWeakReach_conjugate hM g⁻¹
    rwa [conjugate_conjugate_inv] at this
  obtain ⟨e₁⟩ := hmax _ hR
  obtain ⟨e₀⟩ := nonempty_fusionZStar_equiv_conjugate J g
  obtain ⟨e₂⟩ := nonempty_fusionZStar_equiv_conjugate (conjugate M g⁻¹) g
  rw [conjugate_conjugate, inv_mul_cancel, conjugate_one] at e₂
  exact ⟨e₀.symm.trans (e₁.trans e₂)⟩

end CFSG.ComponentClassification.Foote5.SolMax
