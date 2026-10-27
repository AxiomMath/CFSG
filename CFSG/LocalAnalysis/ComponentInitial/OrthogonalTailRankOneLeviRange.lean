module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailRankOneLeviRoot
public import CFSG.CGT.PushingUpLit.CGT6.EmbModule.NatSL2Mat

public section

namespace CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail

open Matrix QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open scoped Pointwise

variable {K : Type} [Field K] {A : Type} [AddCommGroup A] [Module K A] {r : ℕ}
  {qA : QuadraticForm K A} {a₀ : A}

theorem tailLeviHom_tailUpperRoot {i : Fin r} (hi : i.val + 1 < r) (s : K) :
    tailLeviHom qA hi ⟨tailUpperRoot qA hi s, tailUpperRoot_mem_tailLeviDom hi s⟩ =
      tailLeviSL2Embed K A r i (CFSG.SL2MinimalFaithful.unipotent s) := by
  rw [tailLeviHom_apply, tailLeviSL2Embed_apply]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · apply Units.ext
    rw [coe_tailLeviBlkHom, tailLeviBlk_tailUpperRoot,
      Matrix.SpecialLinearGroup.coe_GL_coe_matrix, CFSG.SL2MinimalFaithful.coe_unipotent]
  · funext j
    apply Units.ext
    rw [coe_tailLeviMidHom]
    simpa using tailCoeff_diag_tailUpperRoot (qA := qA) hi s j.2
  · apply Units.ext
    rw [coe_tailLeviAutHom, tailABlock_tailUpperRoot]
    simp

theorem tailLeviHom_tailLowerRoot {i : Fin r} (hi : i.val + 1 < r) (s : K) :
    tailLeviHom qA hi ⟨tailLowerRoot qA hi s, tailLowerRoot_mem_tailLeviDom hi s⟩ =
      tailLeviSL2Embed K A r i (CFSG.CGT.PushingUpLit.CGT6.TwoThree.lowerUni s) := by
  rw [tailLeviHom_apply, tailLeviSL2Embed_apply]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · apply Units.ext
    rw [coe_tailLeviBlkHom, tailLeviBlk_tailLowerRoot,
      Matrix.SpecialLinearGroup.coe_GL_coe_matrix, CFSG.CGT.PushingUpLit.CGT6.TwoThree.coe_lowerUni]
  · funext j
    apply Units.ext
    rw [coe_tailLeviMidHom]
    simpa using tailCoeff_diag_tailLowerRoot (qA := qA) hi s j.2
  · apply Units.ext
    rw [coe_tailLeviAutHom, tailABlock_tailLowerRoot]
    simp

theorem tailUpperRoot_mem_tailRankOneParabolic [FiniteDimensional K A] {i : Fin r}
    (hi : i.val + 1 < r) (hani : qA.Anisotropic) (ha₀ : a₀ ≠ 0) (s : K) :
    tailUpperRoot qA hi s ∈ tailRankOneParabolic qA a₀ i := by
  rw [tailRankOneParabolic_eq_tailLeviDom hi hani ha₀]
  exact tailUpperRoot_mem_tailLeviDom hi s

theorem tailLowerRoot_mem_tailRankOneParabolic [FiniteDimensional K A] {i : Fin r}
    (hi : i.val + 1 < r) (hani : qA.Anisotropic) (ha₀ : a₀ ≠ 0) (s : K) :
    tailLowerRoot qA hi s ∈ tailRankOneParabolic qA a₀ i := by
  rw [tailRankOneParabolic_eq_tailLeviDom hi hani ha₀]
  exact tailLowerRoot_mem_tailLeviDom hi s

theorem tailRankOneLeviHom_tailUpperRoot [FiniteDimensional K A] {i : Fin r}
    (hi : i.val + 1 < r) (hani : qA.Anisotropic) (ha₀ : a₀ ≠ 0) (s : K) :
    tailRankOneLeviHom hi hani ha₀
        ⟨tailUpperRoot qA hi s, tailUpperRoot_mem_tailRankOneParabolic hi hani ha₀ s⟩ =
      tailLeviSL2Embed K A r i (CFSG.SL2MinimalFaithful.unipotent s) := by
  rw [tailRankOneLeviHom_apply]
  exact tailLeviHom_tailUpperRoot (qA := qA) hi s

theorem tailRankOneLeviHom_tailLowerRoot [FiniteDimensional K A] {i : Fin r}
    (hi : i.val + 1 < r) (hani : qA.Anisotropic) (ha₀ : a₀ ≠ 0) (s : K) :
    tailRankOneLeviHom hi hani ha₀
        ⟨tailLowerRoot qA hi s, tailLowerRoot_mem_tailRankOneParabolic hi hani ha₀ s⟩ =
      tailLeviSL2Embed K A r i (CFSG.CGT.PushingUpLit.CGT6.TwoThree.lowerUni s) := by
  rw [tailRankOneLeviHom_apply]
  exact tailLeviHom_tailLowerRoot (qA := qA) hi s

theorem tailLeviSL2Embed_mem_range [FiniteDimensional K A] {i : Fin r} (hi : i.val + 1 < r)
    (hani : qA.Anisotropic) (ha₀ : a₀ ≠ 0) (M : SpecialLinearGroup (Fin 2) K) :
    tailLeviSL2Embed K A r i M ∈ (tailRankOneLeviHom hi hani ha₀).range := by
  let H : Subgroup (SpecialLinearGroup (Fin 2) K) :=
    (tailRankOneLeviHom hi hani ha₀).range.comap (tailLeviSL2Embed K A r i)
  have huni : ∀ s : K, CFSG.SL2MinimalFaithful.unipotent s ∈ H := by
    intro s
    rw [Subgroup.mem_comap, MonoidHom.mem_range]
    exact ⟨⟨tailUpperRoot qA hi s, tailUpperRoot_mem_tailRankOneParabolic hi hani ha₀ s⟩,
      tailRankOneLeviHom_tailUpperRoot hi hani ha₀ s⟩
  have hlow : ∀ s : K, CFSG.CGT.PushingUpLit.CGT6.TwoThree.lowerUni s ∈ H := by
    intro s
    rw [Subgroup.mem_comap, MonoidHom.mem_range]
    exact ⟨⟨tailLowerRoot qA hi s, tailLowerRoot_mem_tailRankOneParabolic hi hani ha₀ s⟩,
      tailRankOneLeviHom_tailLowerRoot hi hani ha₀ s⟩
  have htop : H = ⊤ := by
    rw [eq_top_iff, ← CFSG.CGT.PushingUpLit.CGT6.TwoThree.closure_unipotent_lowerUni (K := K)]
    rw [Subgroup.closure_le]
    rintro x (hx | hx)
    · obtain ⟨s, rfl⟩ := hx
      exact huni s
    · obtain ⟨s, rfl⟩ := hx
      exact hlow s
  have hM : M ∈ H := by rw [htop]; exact Subgroup.mem_top M
  simpa only [H, Subgroup.mem_comap] using hM

end CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
