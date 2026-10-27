module

public import CFSG.GH74.Generic.S45.LUniLift
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4StabU

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace DiagU

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  UnitaryOut UnitaryConj HBlocks StabU ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

abbrev thU (p f : ℕ) (K : Type) [Field K] :
    unitarySU p f K 4 →* StatedProj (StatedSU 4 (p ^ f) K) :=
  QuotientGroup.mk' (scal p f K)

theorem thU_surjective : Function.Surjective (thU p f K) := QuotientGroup.mk'_surjective _

theorem mem_uMat_of_mem_SU (g : unitarySU p f K 4) : (g : GL (Fin 4) K) ∈ uMat h 4 :=
  (mem_uMat h).2 ((mem_unitarySU_iff h).1 g.2).2

theorem conj_mem_SU {A : GL (Fin 4) K} (hA : A ∈ uMat h 4) (g : unitarySU p f K 4) :
    A * (g : GL (Fin 4) K) * A⁻¹ ∈ unitarySU p f K 4 := by
  rw [mem_unitarySU_iff h]
  refine ⟨?_, (mem_uMat h).1 (mul_mem (mul_mem hA (mem_uMat_of_mem_SU h g)) (inv_mem hA))⟩
  rw [Units.val_mul, Units.val_mul, det_mul, det_mul, ((mem_unitarySU_iff h).1 g.2).1, mul_one,
    ← det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, det_one]

theorem thU_conj_eq {C : GL (Fin 4) K} {a b a' b' : unitarySU p f K 4}
    (hab : thU p f K a = thU p f K b) (ha : (a' : GL (Fin 4) K) = C * a * C⁻¹)
    (hb : (b' : GL (Fin 4) K) = C * b * C⁻¹) : thU p f K a' = thU p f K b' := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hab ⊢
  have hab' : ((a⁻¹ * b : unitarySU p f K 4) : GL (Fin 4) K) ∈ StatedScalars (Fin 4) K := hab
  obtain ⟨c, hc⟩ := hab'
  have hcen : GeneralLinearGroup.scalar (Fin 4) c ∈ Subgroup.center (GL (Fin 4) K) := by
    rw [GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨c, rfl⟩
  change ((a'⁻¹ * b' : unitarySU p f K 4) : GL (Fin 4) K) ∈ StatedScalars (Fin 4) K
  refine ⟨c, ?_⟩
  rw [Subgroup.coe_mul, Subgroup.coe_inv, ha, hb]
  have e : (C * (a : GL (Fin 4) K) * C⁻¹)⁻¹ * (C * (b : GL (Fin 4) K) * C⁻¹) =
      C * ((a⁻¹ * b : unitarySU p f K 4) : GL (Fin 4) K) * C⁻¹ := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv]; group
  rw [e, ← hc, Subgroup.mem_center_iff.mp hcen C, mul_assoc, mul_inv_cancel, mul_one]

@[expose] def IsCU (A : GL (Fin 4) K) (α : MulAut (StatedProj (StatedSU 4 (p ^ f) K))) : Prop :=
  A ∈ uMat h 4 ∧ ∀ g g' : unitarySU p f K 4, (g' : GL (Fin 4) K) = A * g * A⁻¹ →
    α (thU p f K g) = thU p f K g'

theorem IsCU.apply {A : GL (Fin 4) K} {α : MulAut (StatedProj (StatedSU 4 (p ^ f) K))}
    (hα : IsCU h A α) (g : unitarySU p f K 4) :
    α (thU p f K g) = thU p f K ⟨_, conj_mem_SU h hα.1 g⟩ :=
  hα.2 g _ rfl

theorem isCU_one : IsCU h (1 : GL (Fin 4) K) 1 :=
  ⟨one_mem _, fun g g' hg => by
    rw [MulAut.one_apply]
    congr 1
    exact Subtype.ext (by rw [hg]; group)⟩

theorem IsCU.mul {A B : GL (Fin 4) K} {α β : MulAut (StatedProj (StatedSU 4 (p ^ f) K))}
    (hα : IsCU h A α) (hβ : IsCU h B β) : IsCU h (A * B) (α * β) := by
  refine ⟨mul_mem hα.1 hβ.1, fun g g' hg => ?_⟩
  rw [MulAut.mul_apply, hβ.apply h g, hα.apply h]
  congr 1
  apply Subtype.ext
  change A * (B * (g : GL (Fin 4) K) * B⁻¹) * A⁻¹ = _
  rw [hg]; group

theorem IsCU.inv {A : GL (Fin 4) K} {α : MulAut (StatedProj (StatedSU 4 (p ^ f) K))}
    (hα : IsCU h A α) : IsCU h A⁻¹ α⁻¹ := by
  refine ⟨inv_mem hα.1, fun g g' hg => ?_⟩
  have h1 : α (thU p f K g') = thU p f K g := hα.2 g' g (by rw [hg]; group)
  rw [← h1, ← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]

theorem IsCU.commutator {A B : GL (Fin 4) K} {α β : MulAut (StatedProj (StatedSU 4 (p ^ f) K))}
    (hα : IsCU h A α) (hβ : IsCU h B β) : IsCU h ⁅A, B⁆ ⁅α, β⁆ := by
  rw [commutatorElement_def, commutatorElement_def]
  exact ((hα.mul h hβ).mul h hα.inv).mul h hβ.inv

theorem IsCU.unique {A : GL (Fin 4) K} {α β : MulAut (StatedProj (StatedSU 4 (p ^ f) K))}
    (hα : IsCU h A α) (hβ : IsCU h A β) : α = β := by
  apply MulEquiv.ext
  intro x
  obtain ⟨g, rfl⟩ := thU_surjective x
  rw [hα.apply h, hβ.apply h]

theorem isCU_conj (s : unitarySU p f K 4) :
    IsCU h (s : GL (Fin 4) K) (MulAut.conj (thU p f K s)) := by
  refine ⟨mem_uMat_of_mem_SU h s, fun g g' hg => ?_⟩
  rw [MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (by rw [hg]; rfl)

theorem IsCU.eq_conj {s : GL (Fin 4) K} (hs : s ∈ unitarySU p f K 4)
    {α : MulAut (StatedProj (StatedSU 4 (p ^ f) K))} (hα : IsCU h s α) :
    α = MulAut.conj (thU p f K ⟨s, hs⟩) :=
  hα.unique h (isCU_conj h ⟨s, hs⟩)

variable (p f K) in
@[expose] def InnU : Subgroup (MulAut (StatedProj (StatedSU 4 (p ^ f) K))) where
  carrier := {α | ∃ A, IsCU h A α}
  one_mem' := ⟨1, isCU_one h⟩
  mul_mem' := fun ⟨A, hA⟩ ⟨B, hB⟩ => ⟨A * B, hA.mul h hB⟩
  inv_mem' := fun ⟨A, hA⟩ => ⟨A⁻¹, hA.inv h⟩

theorem mem_InnU {α : MulAut (StatedProj (StatedSU 4 (p ^ f) K))} :
    α ∈ InnU p f K h ↔ ∃ A, IsCU h A α := Iff.rfl

theorem commutator_mem_InnU (hp2 : p ≠ 2) (u v : MulAut (StatedProj (StatedSU 4 (p ^ f) K))) :
    ⁅u, v⁆ ∈ InnU p f K h := by
  classical
  have : Finite K := h.finite
  have hker : (thU p f K).ker ≤ Subgroup.center (unitarySU p f K 4) := by
    rw [QuotientGroup.ker_mk']
    intro z hz
    exact mem_center_of_mem_scal hz
  obtain ⟨A, φ, hA, hAu, hu, -⟩ := CFSG.GH74.Generic.S45.exists_lift_unitarySU' h hp2 (d := 4)
    (by norm_num) (thU p f K) thU_surjective hker u
  obtain ⟨B, ψ, hB, hBu, hv, -⟩ := CFSG.GH74.Generic.S45.exists_lift_unitarySU' h hp2 (d := 4)
    (by norm_num) (thU p f K) thU_surjective hker v
  have hAU : A ∈ uMat h 4 := (mem_uMat h).2 hAu
  have hBU : B ∈ uMat h 4 := (mem_uMat h).2 hBu
  set M₁ := A * glAut φ B with hM₁
  set M₂ := B * glAut ψ A with hM₂
  set C := M₁ * M₂⁻¹ with hC
  have hCU : C ∈ uMat h 4 := mul_mem (mul_mem hAU (glAut_mem_uMat h φ hBU))
    (inv_mem (mul_mem hBU (glAut_mem_uMat h ψ hAU)))
  have hgl : ∀ g : GL (Fin 4) K, glAut φ (glAut ψ g) = glAut ψ (glAut φ g) := by
    intro g
    have h1 : (glAut φ * glAut ψ : MulAut (GL (Fin 4) K)) = glAut ψ * glAut φ := by
      rw [← map_mul, ← map_mul, ringAut_mul_comm K φ ψ]
    exact congrArg (fun χ : MulAut (GL (Fin 4) K) => χ g) h1
  have huv : ∀ g : unitarySU p f K 4, ∃ w : unitarySU p f K 4,
      (w : GL (Fin 4) K) = M₁ * glAut φ (glAut ψ (g : GL (Fin 4) K)) * M₁⁻¹ ∧
        (u * v) (thU p f K g) = thU p f K w := by
    intro g
    refine ⟨ClassicalInvolution.ModelFacts.UnitaryAut.unitaryConjHom A φ hA
      (ClassicalInvolution.ModelFacts.UnitaryAut.unitaryConjHom B ψ hB g), ?_, ?_⟩
    · rw [ClassicalInvolution.ModelFacts.UnitaryAut.coe_unitaryConjHom,
        ClassicalInvolution.ModelFacts.UnitaryAut.coe_unitaryConjHom, map_mul, map_mul, map_inv,
        hM₁]
      group
    · rw [MulAut.mul_apply, ← hv, ← hu]
  have hvu : ∀ g : unitarySU p f K 4, ∃ w : unitarySU p f K 4,
      (w : GL (Fin 4) K) = M₂ * glAut ψ (glAut φ (g : GL (Fin 4) K)) * M₂⁻¹ ∧
        (v * u) (thU p f K g) = thU p f K w := by
    intro g
    refine ⟨ClassicalInvolution.ModelFacts.UnitaryAut.unitaryConjHom B ψ hB
      (ClassicalInvolution.ModelFacts.UnitaryAut.unitaryConjHom A φ hA g), ?_, ?_⟩
    · rw [ClassicalInvolution.ModelFacts.UnitaryAut.coe_unitaryConjHom,
        ClassicalInvolution.ModelFacts.UnitaryAut.coe_unitaryConjHom, map_mul, map_mul, map_inv,
        hM₂]
      group
    · rw [MulAut.mul_apply, ← hu, ← hv]
  refine ⟨C, hCU, fun g g' hg => ?_⟩
  obtain ⟨g₀, hg₀⟩ := thU_surjective ((v * u)⁻¹ (thU p f K g))
  have h1 : (v * u) (thU p f K g₀) = thU p f K g := by
    rw [hg₀, ← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]
  obtain ⟨w₂, hw₂, hw₂'⟩ := hvu g₀
  obtain ⟨w₁, hw₁, hw₁'⟩ := huv g₀
  have hcomm : ⁅u, v⁆ = (u * v) * (v * u)⁻¹ := by rw [commutatorElement_def]; group
  rw [hcomm, MulAut.mul_apply, ← hg₀, hw₁']
  have h2 : thU p f K w₂ = thU p f K g := by rw [← hw₂', h1]
  refine thU_conj_eq h2 (C := C) ?_ hg
  rw [hw₁, hw₂, hgl, hC]
  group

theorem InnU_normal (hp2 : p ≠ 2) : (InnU p f K h).Normal := by
  constructor
  intro α hα σ
  have e : σ * α * σ⁻¹ = ⁅σ, α⁆ * α := by rw [commutatorElement_def]; group
  rw [e]
  exact mul_mem (commutator_mem_InnU h hp2 σ α) hα

theorem commutator_mem_SU {A B : GL (Fin 4) K} (hA : A ∈ uMat h 4) (hB : B ∈ uMat h 4) :
    ⁅A, B⁆ ∈ unitarySU p f K 4 := by
  rw [mem_unitarySU_iff h]
  refine ⟨?_, (mem_uMat h).1 (by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hA hB) (inv_mem hA)) (inv_mem hB))⟩
  rw [← GeneralLinearGroup.val_det_apply, map_commutatorElement,
    commutatorElement_eq_one_iff_mul_comm.2 (mul_comm _ _), Units.val_one]

include h in
theorem le_range_conj_of_perfect_U (hp2 : p ≠ 2)
    {J : Subgroup (MulAut (StatedProj (StatedSU 4 (p ^ f) K)))} (hJ : ⁅J, J⁆ = J) :
    J ≤ (MulAut.conj : StatedProj (StatedSU 4 (p ^ f) K) →*
      MulAut (StatedProj (StatedSU 4 (p ^ f) K))).range := by
  have h1 : J ≤ InnU p f K h := by
    rw [← hJ, Subgroup.commutator_le]
    intro u _ v _
    exact commutator_mem_InnU h hp2 u v
  rw [← hJ, Subgroup.commutator_le]
  intro u hu v hv
  obtain ⟨A, hA⟩ := h1 hu
  obtain ⟨B, hB⟩ := h1 hv
  have hs := commutator_mem_SU h hA.1 hB.1
  exact ⟨_, ((hA.commutator h hB).eq_conj h hs).symm⟩

end DiagU

end CFSG.ComponentClassification.CatFactsL4U4
