module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailRankOneLeviHom
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailSylow

public section

namespace CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail

open Matrix QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open scoped Pointwise

variable {K : Type} [Field K] {A : Type} [AddCommGroup A] [Module K A] {r : ℕ}
  {qA : QuadraticForm K A} {a₀ : A}

private theorem tailCoeff_eq_zero_of_tailLeviHom_eq_one_H07 {i : Fin r} (hi : i.val + 1 < r)
    {g : ↥(tailLeviDom r qA i)} (hg : tailLeviHom qA hi g = 1)
    {a b : Fin r} (hba : b.val < a.val) : tailCoeff (g : TailModel K A r) a b = 0 := by
  by_cases hne : b.val = i.val ∧ a.val = i.val + 1
  · obtain ⟨hb, ha⟩ := hne
    have hblk : tailLeviBlkHom qA hi g = 1 := by
      simpa [tailLeviHom] using congrArg Prod.fst hg
    have hmat : tailLeviBlk hi (g : TailModel K A r) = 1 := by
      rw [← coe_tailLeviBlkHom hi g, hblk]
      simp
    have haeq : a = tailPair hi 1 := by
      apply Fin.ext
      rw [tailPair_val]
      simpa using ha
    have hbeq : b = tailPair hi 0 := by
      apply Fin.ext
      rw [tailPair_val]
      simpa using hb
    rw [haeq, hbeq, ← tailLeviBlk_apply hi (g : TailModel K A r), hmat]
    exact Matrix.one_apply_ne (by decide)
  · exact tailCoeff_eq_zero_of_mem_tailLeviDom hi g.2 hba hne

private theorem map_hypVec_inl_mem_tailFlag_succ_H07 {i : Fin r} (hi : i.val + 1 < r)
    {g : ↥(tailLeviDom r qA i)} (hg : tailLeviHom qA hi g = 1)
    {j : Fin r} (hj : j.val < i.val + 1) :
    (g : TailModel K A r) (hypVec K A (.inl j)) ∈ tailFlag K A r (i.val + 1) := by
  rw [tailLeviDom_apply_hypVec_inl hi g.2 j]
  refine Submodule.sum_mem _ fun k _ => ?_
  by_cases hk : k.val < i.val + 1
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, hk, rfl⟩)
  · have hz : tailCoeff (g : TailModel K A r) k j = 0 :=
      tailCoeff_eq_zero_of_tailLeviHom_eq_one_H07 hi hg (by omega)
    rw [hz, zero_smul]
    exact Submodule.zero_mem _

private theorem map_tailFlag_succ_le_H07 {i : Fin r} (hi : i.val + 1 < r)
    {g : ↥(tailLeviDom r qA i)} (hg : tailLeviHom qA hi g = 1) :
    (tailFlag K A r (i.val + 1)).map
        ((g : TailModel K A r) : ((Fin r ⊕ Fin r → K) × A) →ₗ[K] _) ≤
      tailFlag K A r (i.val + 1) := by
  rw [tailFlag, Submodule.map_span_le]
  rintro v ⟨j, hj, rfl⟩
  exact map_hypVec_inl_mem_tailFlag_succ_H07 hi hg hj

theorem mem_tailFlagStab_of_tailLeviHom_eq_one {i : Fin r} (hi : i.val + 1 < r)
    {g : ↥(tailLeviDom r qA i)} (hg : tailLeviHom qA hi g = 1) :
    (g : TailModel K A r) ∈ tailFlagStab r qA := by
  refine mem_tailFlagStab.2 ⟨orthElementaryGroup_le _ (tailLeviDom_le i g.2), ?_⟩
  intro k hk1 hkr
  by_cases hki : k = i.val + 1
  · rw [hki]
    refine le_antisymm (map_tailFlag_succ_le_H07 hi hg) ?_
    have hginv : tailLeviHom qA hi g⁻¹ = 1 := by rw [map_inv, hg, inv_one]
    have hinv := map_tailFlag_succ_le_H07 hi hginv
    intro x hx
    refine Submodule.mem_map.2 ⟨((g⁻¹ : ↥(tailLeviDom r qA i)) : TailModel K A r) x,
      hinv (Submodule.mem_map_of_mem hx), ?_⟩
    have hprod : (g : TailModel K A r) * ((g⁻¹ : ↥(tailLeviDom r qA i)) : TailModel K A r)
        = 1 := by rw [← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one]
    show ((g : TailModel K A r) * ((g⁻¹ : ↥(tailLeviDom r qA i)) : TailModel K A r)) x = x
    rw [hprod]
    rfl
  · exact (mem_tailLeviDom.1 g.2).2 k hk1 hkr hki

private theorem stabDiag_eq_one_of_tailLeviHom_eq_one_H07 {i : Fin r} (hi : i.val + 1 < r)
    {g : ↥(tailLeviDom r qA i)} (hg : tailLeviHom qA hi g = 1) :
    stabDiag (g : TailModel K A r) = 1 := by
  have hblk : tailLeviBlkHom qA hi g = 1 := by
    simpa [tailLeviHom] using congrArg Prod.fst hg
  have hmid : tailLeviMidHom qA hi g = 1 := by
    simpa [tailLeviHom] using congrArg (fun x => x.2.1) hg
  have haut : tailLeviAutHom qA hi g = 1 := by
    simpa [tailLeviHom] using congrArg (fun x => x.2.2) hg
  have hmat : tailLeviBlk hi (g : TailModel K A r) = 1 := by
    rw [← coe_tailLeviBlkHom hi g, hblk]
    simp
  refine Prod.ext ?_ ?_
  · funext j
    show tailCoeff (g : TailModel K A r) j j = 1
    by_cases hj : j.val ≠ i.val ∧ j.val ≠ i.val + 1
    · have h1 : tailLeviMidHom qA hi g ⟨j, hj⟩ = 1 := by
        simpa using congrFun hmid ⟨j, hj⟩
      have h2 := coe_tailLeviMidHom hi g ⟨j, hj⟩
      rw [h1] at h2
      simpa using h2.symm
    · have hcase : j.val = i.val ∨ j.val = i.val + 1 := by
        by_contra hcon
        rw [not_or] at hcon
        exact hj hcon
      rcases hcase with h | h
      · have hjeq : j = tailPair hi 0 := by
          apply Fin.ext
          rw [tailPair_val]
          simpa using h
        rw [hjeq, ← tailLeviBlk_apply hi (g : TailModel K A r), hmat]
        exact Matrix.one_apply_eq 0
      · have hjeq : j = tailPair hi 1 := by
          apply Fin.ext
          rw [tailPair_val]
          simpa using h
        rw [hjeq, ← tailLeviBlk_apply hi (g : TailModel K A r), hmat]
        exact Matrix.one_apply_eq 1
  · show tailABlock (g : TailModel K A r) = 1
    have h2 := coe_tailLeviAutHom hi g
    rw [haut] at h2
    simpa using h2.symm

theorem mem_tailUnipotent_of_tailRankOneLeviHom_eq_one [FiniteDimensional K A] {i : Fin r}
    (hi : i.val + 1 < r) (hani : qA.Anisotropic) (ha₀ : a₀ ≠ 0)
    {g : ↥(tailRankOneParabolic qA a₀ i)} (hg : tailRankOneLeviHom hi hani ha₀ g = 1) :
    (g : TailModel K A r) ∈ tailUnipotent r qA := by
  have hlevi : (g : TailModel K A r) ∈ tailLeviDom r qA i :=
    tailRankOneParabolic_le_tailLeviDom hi hani ha₀ g.2
  have hg' : tailLeviHom qA hi ⟨(g : TailModel K A r), hlevi⟩ = 1 := by
    rw [← tailRankOneLeviHom_apply hi hani ha₀ g]
    exact hg
  have hmem : (g : TailModel K A r) ∈ tailFlagStab r qA :=
    mem_tailFlagStab_of_tailLeviHom_eq_one hi hg'
  refine (mem_tailUnipotent_iff_ker (g := (g : TailModel K A r)) hani).2 ⟨hmem, ?_⟩
  show stabDiag (g : TailModel K A r) = 1
  exact stabDiag_eq_one_of_tailLeviHom_eq_one_H07 hi hg'

theorem isPGroup_ker_tailRankOneLeviHom [Finite K] [FiniteDimensional K A] [CharP K 2]
    {i : Fin r} (hi : i.val + 1 < r) (hani : qA.Anisotropic) (ha₀ : a₀ ≠ 0) :
    IsPGroup 2 (tailRankOneLeviHom hi hani ha₀).ker := by
  have hU : ∀ x : ↥(tailRankOneParabolic qA a₀ i),
      tailRankOneLeviHom hi hani ha₀ x = 1 → (x : TailModel K A r) ∈ tailUnipotent r qA :=
    fun x hx => mem_tailUnipotent_of_tailRankOneLeviHom_eq_one hi hani ha₀ hx
  have hE : ∀ x : ↥(tailRankOneParabolic qA a₀ i),
      (x : TailModel K A r) ∈ orthElementaryGroup (quadTail r qA) :=
    fun x => tailRankOneParabolic_le_orthElementaryGroup i x.2
  let φ : (tailRankOneLeviHom hi hani ha₀).ker →*
      ↥((tailUnipotent r qA).subgroupOf (orthElementaryGroup (quadTail r qA))) :=
    { toFun := fun x =>
        ⟨⟨(x.1 : TailModel K A r), hE x.1⟩, hU x.1 (MonoidHom.mem_ker.1 x.2)⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun x y => Subtype.ext rfl }
  refine (isPGroup_tailUnipotent (p := 2) hani).of_injective φ ?_
  intro x y hxy
  have h1 : (φ x).1.1 = (φ y).1.1 := congrArg (fun z => z.1.1) hxy
  have h : (x.1 : TailModel K A r) = (y.1 : TailModel K A r) := h1
  exact Subtype.ext (Subtype.ext h)

end CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
