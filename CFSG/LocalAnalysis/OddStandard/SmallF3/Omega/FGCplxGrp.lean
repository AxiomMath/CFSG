module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGCommutant
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGLiftComm
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2OutDefs
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFShapesAux

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup
open scoped commutatorElement

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem fg_polar_isom_of_mem {g : V ≃ₗ[ZMod 3] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (x y : V) :
    Q.polarBilin (g x) (g y) = Q.polarBilin x y := by
  have hg' := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hg
  have h := hg' (x + y)
  rw [map_add] at h
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar]
  rw [h, hg' x, hg' y]

theorem fg_mem_orthogonalGroup_of_polar {g : V ≃ₗ[ZMod 3] V}
    (hg : ∀ x y, Q.polarBilin (g x) (g y) = Q.polarBilin x y) :
    g ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro v
  have h := hg v v
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self, two_nsmul] at h
  have h3 : ∀ a b : ZMod 3, a + a = b + b → a = b := by decide
  exact h3 _ _ h

theorem fg_cplxGroup_commutator {ρ : ↥(simGroup Q)} {lam : ZMod 3}
    (hρ : FGCplx Q.polarBilin (ρ : V ≃ₗ[ZMod 3] V).toLinearMap lam) :
    FGCplxGroup Q.polarBilin (ρ : V ≃ₗ[ZMod 3] V).toLinearMap
      (⁅fixSub (simAct Q ρ), fixSub (simAct Q ρ)⁆.map
        (TauCeti.QuadraticMap.orthogonalGroup Q).subtype) := by
  let C : Subgroup (OGroup Q) := fixSub (simAct Q ρ)
  have hCρ : ∀ j ∈ C, ∀ x, ρ.1 (((j : OGroup Q) : V ≃ₗ[ZMod 3] V) x) =
      ((j : OGroup Q) : V ≃ₗ[ZMod 3] V) (ρ.1 x) :=
    fun j hj x => fg_apply_comm_of_simAct ρ (mem_fixSub_iff.mp hj) x
  have hPC : ⁅C, C⁆ ≤ C := by
    rw [Subgroup.commutator_le]
    intro p hp q hq
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hp hq) (inv_mem hp)) (inv_mem hq)
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨j, hj, rfl⟩ x y
    exact fg_polar_isom_of_mem j.2 x y
  · rintro _ ⟨j, hj, rfl⟩ x
    exact (hCρ j (hPC hj) x).symm
  · intro σ hσB hσρ g hg
    have hσO : σ ∈ TauCeti.QuadraticMap.orthogonalGroup Q := fg_mem_orthogonalGroup_of_polar hσB
    let σ' : OGroup Q := ⟨σ, hσO⟩
    have hσ'C : σ' ∈ C := by
      rw [mem_fixSub_iff]
      apply Subtype.ext
      rw [coe_simAct]
      apply mul_inv_eq_iff_eq_mul.mpr
      apply LinearEquiv.ext
      intro x
      exact (hσρ x).symm
    obtain ⟨j, hj, rfl⟩ := hg
    have hmapC : (⁅(⊤ : Subgroup ↥C), (⊤ : Subgroup ↥C)⁆ : Subgroup ↥C).map C.subtype =
        ⁅C, C⁆ :=
      Subgroup.map_subtype_commutator C
    rw [← hmapC] at hj
    obtain ⟨e, he, rfl⟩ := hj
    have hnorm : (⁅(⊤ : Subgroup ↥C), (⊤ : Subgroup ↥C)⁆ : Subgroup ↥C).Normal := inferInstance
    have hconj := hnorm.conj_mem e he (⟨σ', hσ'C⟩ : ↥C)
    refine ⟨σ' * (C.subtype e) * σ'⁻¹, ?_, rfl⟩
    rw [← hmapC]
    exact ⟨_, hconj, rfl⟩

theorem fg_cplx_lifts (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    {ρ : ↥(simGroup Q)} {lam : ZMod 3}
    (hρ : FGCplx Q.polarBilin (ρ : V ≃ₗ[ZMod 3] V).toLinearMap lam)
    (hsimp : IsSimpleGroup ↥⁅fixSub (simAct Q ρ), fixSub (simAct Q ρ)⁆)
    (hnab : ∃ a b : ↥⁅fixSub (simAct Q ρ), fixSub (simAct Q ρ)⁆, a * b ≠ b * a)
    (hcard : ¬ Nat.card ↥⁅fixSub (simAct Q ρ), fixSub (simAct Q ρ)⁆ ∣ 11232) {a : ProjSim Q}
    (ha : ∀ j ∈ ⁅fixSub (simAct Q ρ), fixSub (simAct Q ρ)⁆,
      toProj Q (projSimActO Q a j) = toProj Q j) :
    ∃ (γ : simGroup Q) (α β : ZMod 3), (QuotientGroup.mk γ : ProjSim Q) = a ∧
      ∀ v, (γ : V ≃ₗ[ZMod 3] V) v = α • v + β • (ρ : V ≃ₗ[ZMod 3] V) v := by
  obtain ⟨γ, rfl⟩ := QuotientGroup.mk_surjective a
  let P : Subgroup (OGroup Q) := ⁅fixSub (simAct Q ρ), fixSub (simAct Q ρ)⁆
  have hperf : Group.IsPerfect ↥P := (ff_isQuasisimple_of_simple hsimp hnab).1
  have hcomm := fg_projSimActO_eq_of_perfect P hperf (QuotientGroup.mk γ) ha
  have hcomm' : ∀ j ∈ P, simAct Q γ j = j := fun j hj => by
    have h := hcomm j hj
    rwa [projSimActO_mk] at h
  let H : Subgroup (V ≃ₗ[ZMod 3] V) := P.map (TauCeti.QuadraticMap.orthogonalGroup Q).subtype
  have hH : FGCplxGroup Q.polarBilin (ρ : V ≃ₗ[ZMod 3] V).toLinearMap H :=
    fg_cplxGroup_commutator hρ
  let e : ↥P ≃* ↥H := Subgroup.equivMapOfInjective P
    (TauCeti.QuadraticMap.orthogonalGroup Q).subtype (Subgroup.subtype_injective _)
  haveI : IsSimpleGroup ↥P := hsimp
  haveI : IsSimpleGroup ↥H := e.symm.isSimpleGroup
  have hcardH : ¬ Nat.card ↥H ∣ 11232 := by
    rw [← Nat.card_congr e.toEquiv]
    exact hcard
  have hnabH : ∃ x y : ↥H, x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := hnab
    exact ⟨e x, e y, fun h => hxy (e.injective (by rw [map_mul, map_mul]; exact h))⟩
  have hB : Q.polarBilin.Nondegenerate := QuadraticMap.nondegenerate_polar_iff.mpr hQ
  obtain ⟨α, β, hαβ⟩ := fg_commutant_rho hB hdim hρ hH hcardH hnabH
    ((γ : V ≃ₗ[ZMod 3] V).toLinearMap) (by
      rintro _ ⟨j, hj, rfl⟩ v
      exact fg_apply_comm_of_simAct γ (hcomm' j hj) v)
  exact ⟨γ, α, β, rfl, hαβ⟩

end CFSG.OddStandard.SmallF3.Omega
