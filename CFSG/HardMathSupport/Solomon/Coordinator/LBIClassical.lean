module

public import CFSG.HardMathSupport.Solomon.Coordinator.LBIInput6_1
public import CFSG.RankThree.CentralCover.LinearUnitaryFourGroupWitness
public import CFSG.Assembly.GL83LieDefs

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open (griessHopfMultiplier)
open CFSG.Assembly.LowTwoRank CFSG.RankThree.CentralCover
open scoped commutatorElement

section Scalars

variable {K : Type} [Field K]

theorem lbi_det_of_closure {T : Set (Matrix.GeneralLinearGroup (Fin 3) K)}
    (hT : ∀ A ∈ T, (A : Matrix (Fin 3) (Fin 3) K).det = 1) :
    ∀ A ∈ Subgroup.closure T, (A : Matrix (Fin 3) (Fin 3) K).det = 1 := by
  have hle : Subgroup.closure T ≤ (Matrix.GeneralLinearGroup.det : Matrix.GeneralLinearGroup (Fin 3) K →* Kˣ).ker := by
    rw [Subgroup.closure_le]
    intro A hA
    rw [SetLike.mem_coe, MonoidHom.mem_ker]
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply]
    exact hT A hA
  intro A hA
  have := hle hA
  rw [MonoidHom.mem_ker] at this
  rw [← Matrix.GeneralLinearGroup.val_det_apply, this]
  rfl

theorem lbi_proj_exp (S : Subgroup (Matrix.GeneralLinearGroup (Fin 3) K))
    (hdet : ∀ s ∈ S, (s : Matrix (Fin 3) (Fin 3) K).det = 1) :
    ∀ w ∈ (statedProjMk S).ker, w ^ 3 = 1 := by
  intro w hw
  have hw' : w ∈ (StatedScalars (Fin 3) K).subgroupOf S := by
    rwa [statedProjMk, QuotientGroup.ker_mk'] at hw
  obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.1 hw'
  have h1 : ((c ^ 3 : Kˣ) : K) = 1 := by
    have := hdet w w.2
    rw [← hc, ← Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.det_scalar] at this
    simpa using this
  have hc3 : c ^ 3 = 1 := Units.ext h1
  apply Subtype.ext
  show ((w : Matrix.GeneralLinearGroup (Fin 3) K)) ^ 3 = 1
  rw [← hc, ← map_pow, hc3, map_one]

theorem lbi_scalar_mem_ker (S : Subgroup (Matrix.GeneralLinearGroup (Fin 3) K)) (c : Kˣ)
    (hc : Matrix.GeneralLinearGroup.scalar (Fin 3) c ∈ S) :
    (⟨_, hc⟩ : S) ∈ (statedProjMk S).ker := by
  rw [statedProjMk, QuotientGroup.ker_mk']
  exact Subgroup.mem_subgroupOf.2 ⟨c, rfl⟩

theorem lbi_scalar_ne_one (S : Subgroup (Matrix.GeneralLinearGroup (Fin 3) K)) (c : Kˣ) (hc1 : c ≠ 1)
    (hc : Matrix.GeneralLinearGroup.scalar (Fin 3) c ∈ S) :
    (⟨_, hc⟩ : S) ≠ 1 := by
  intro h
  apply hc1
  have := congrArg (fun s : S => ((s : Matrix.GeneralLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0) h
  apply Units.ext
  simpa [Matrix.GeneralLinearGroup.coe_scalar] using this

end Scalars

theorem lbi_family {Y : Type} [Group Y] [Finite Y] (hq : CFSG.Open.IsQuasisimple Y)
    (h3 : IsPGroup 3 (Subgroup.center Y)) {K : Type} [Field K] [Finite K]
    (S : Subgroup (Matrix.GeneralLinearGroup (Fin 3) K))
    (hdet : ∀ s ∈ S, (s : Matrix (Fin 3) (Fin 3) K).det = 1) (hperfS : Group.IsPerfect ↥S)
    (ω : Kˣ) (hω1 : ω ≠ 1) (hωS : Matrix.GeneralLinearGroup.scalar (Fin 3) ω ∈ S)
    (e : Y ⧸ Subgroup.center Y ≃* StatedProj S)
    {A : Type} [Group A] [Finite A] (eH : griessHopfMultiplier (Y ⧸ Subgroup.center Y) ≃* A)
    (hA : Nat.card A ∣ 48) :
    Subgroup.center Y = ⊥ ∨ Nonempty (Y ≃* ↥S) := by
  have : Finite ↥S := inferInstance
  let θ : ↥S →* Y ⧸ Subgroup.center Y := e.symm.toMonoidHom.comp (statedProjMk S)
  have hθker : ∀ w : ↥S, w ∈ θ.ker → w ∈ (statedProjMk S).ker := by
    intro w hw
    rw [MonoidHom.mem_ker] at hw ⊢
    exact e.symm.map_eq_one_iff.1 hw
  have hθ : Function.Surjective θ := e.symm.surjective.comp (statedProjMk_surjective S)
  refine lbi_main_aux hq h3 θ hθ (fun w hw => ker_statedProjMk_le_center S (hθker w hw))
    hperfS.commutator_eq_top (fun w hw => lbi_proj_exp S hdet w (hθker w hw)) ?_ eH hA
  refine ⟨⟨_, hωS⟩, ?_, lbi_scalar_ne_one S ω hω1 hωS⟩
  rw [MonoidHom.mem_ker]
  have := lbi_scalar_mem_ker S ω hωS
  rw [MonoidHom.mem_ker] at this
  show e.symm (statedProjMk S ⟨_, hωS⟩) = 1
  rw [this, map_one]

end CFSG.HardMathSupport.Solomon.Coordinator
