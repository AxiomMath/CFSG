module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailRankOneLeviABlockComm

public section

namespace CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail

open Matrix QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open scoped Pointwise commutatorElement

variable {K : Type} [Field K] {A : Type} [AddCommGroup A] [Module K A] {r : ℕ}
  {qA : QuadraticForm K A} {a₀ : A}

theorem commutatorElement_mem_range_tailLeviSL2Embed {i : Fin r} {x y : TailLeviTarget K A r i}
    (h : x.2.2 * y.2.2 = y.2.2 * x.2.2) : ⁅x, y⁆ ∈ (tailLeviSL2Embed K A r i).range := by
  have h1 : ⁅x, y⁆.1 = ⁅x.1, y.1⁆ :=
    map_commutatorElement (MonoidHom.fst (GL (Fin 2) K)
      (({j : Fin r // j.val ≠ i.val ∧ j.val ≠ i.val + 1} → Kˣ) ×
        LinearMap.GeneralLinearGroup K A)) (g₁ := x) (g₂ := y)
  have hsnd : ⁅x, y⁆.2 = ⁅x.2, y.2⁆ :=
    map_commutatorElement (MonoidHom.snd (GL (Fin 2) K)
      (({j : Fin r // j.val ≠ i.val ∧ j.val ≠ i.val + 1} → Kˣ) ×
        LinearMap.GeneralLinearGroup K A)) (g₁ := x) (g₂ := y)
  have h2 : ⁅x, y⁆.2.1 = ⁅x.2.1, y.2.1⁆ := by
    rw [hsnd]
    exact map_commutatorElement (MonoidHom.fst
      ({j : Fin r // j.val ≠ i.val ∧ j.val ≠ i.val + 1} → Kˣ)
      (LinearMap.GeneralLinearGroup K A)) (g₁ := x.2) (g₂ := y.2)
  have h3 : ⁅x, y⁆.2.2 = ⁅x.2.2, y.2.2⁆ := by
    rw [hsnd]
    exact map_commutatorElement (MonoidHom.snd
      ({j : Fin r // j.val ≠ i.val ∧ j.val ≠ i.val + 1} → Kˣ)
      (LinearMap.GeneralLinearGroup K A)) (g₁ := x.2) (g₂ := y.2)
  have hmid : ⁅x.2.1, y.2.1⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm x.2.1 y.2.1)
  have hlast : ⁅x.2.2, y.2.2⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr h
  have hxy : ⁅x, y⁆ = (⁅x.1, y.1⁆, (1, 1)) := by
    apply Prod.ext
    · exact h1
    · apply Prod.ext
      · exact h2.trans hmid
      · exact h3.trans hlast
  have hdet : Matrix.GeneralLinearGroup.det ⁅x.1, y.1⁆ = 1 := by
    rw [map_commutatorElement (Matrix.GeneralLinearGroup.det) (g₁ := x.1) (g₂ := y.1),
      commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm _ _
  obtain ⟨M, hM⟩ : ⁅x.1, y.1⁆ ∈
      (Matrix.SpecialLinearGroup.toGL (n := Fin 2) (R := K)).range := by
    rw [Matrix.SpecialLinearGroup.range_toGL_eq_ker_det]
    exact MonoidHom.mem_ker.mpr hdet
  refine MonoidHom.mem_range.mpr ⟨M, ?_⟩
  rw [tailLeviSL2Embed_apply i M, hxy, hM]

theorem commutator_range_tailRankOneLeviHom_le [FiniteDimensional K A] {i : Fin r}
    (hi : i.val + 1 < r) (hani : qA.Anisotropic) (ha₀ : a₀ ≠ 0)
    (hcomm : ∀ b₁ ∈ tailBorel r qA, ∀ b₂ ∈ tailBorel r qA, ⁅b₁, b₂⁆ ∈ tailUnipotent r qA) :
    ⁅(tailRankOneLeviHom hi hani ha₀).range, (tailRankOneLeviHom hi hani ha₀).range⁆ ≤
      (tailLeviSL2Embed K A r i).range := by
  rw [Subgroup.commutator_le]
  intro g₁ hg₁ g₂ hg₂
  obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hg₁
  obtain ⟨y, rfl⟩ := MonoidHom.mem_range.mp hg₂
  exact commutatorElement_mem_range_tailLeviSL2Embed
    (tailRankOneLeviHom_aut_comm hi hani ha₀ hcomm x y)

end CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
