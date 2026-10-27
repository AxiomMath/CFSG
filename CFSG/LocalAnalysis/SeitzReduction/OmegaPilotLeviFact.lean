module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotLeviFactMatrix
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotLeviFact
public import CFSG.Assembly.ComponentTypeDefs

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup Matrix
open CFSG.Assembly.LowTwoRank (StatedOmega StatedQuadPlus)
open CFSG.Quasithin (perfectCore perfectCore_le le_perfectCore_of_perfect perfectCore_perfect)
open CFSG.SeitzReduction.SymplecticPilot (suppGL mem_suppGL IsSuppMat diagSpEntry diagSpEntry_inl
  diagSpEntry_inr planeCoords mem_planeCoords planeTorusParam liftParam diagSpEntry_liftParam
  diagSpEntry_eq_one_of_mem_planeTorusParam exists_mem_planeTorusParam_diagSpEntry_ne
  commute_of_diag_iff)

section Diagonal

variable (F : Type) [Field F] (m : ℕ)

@[expose] def omegaDiagUnits : (Fin m → Fˣ) →* (Fin m ⊕ Fin m → Fˣ) where
  toFun t := Sum.elim t (fun i => (t i)⁻¹)
  map_one' := by
    funext a
    rcases a with i | i <;> simp
  map_mul' t s := by
    funext a
    rcases a with i | i
    · rfl
    · simp only [Sum.elim_inr, Pi.mul_apply, _root_.mul_inv_rev]
      exact mul_comm _ _

@[expose] noncomputable def diagOmega : (Fin m → Fˣ) →* GL (Fin m ⊕ Fin m) F :=
  TauCeti.diagGL.comp (omegaDiagUnits F m)

variable {F m}

theorem diagOmega_coe (t : Fin m → Fˣ) :
    (diagOmega F m t : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F) = diagonal (diagSpEntry t) := by
  rw [diagOmega, MonoidHom.comp_apply, TauCeti.diagGL_coe]
  congr 1
  funext a
  rcases a with i | i <;> rfl

theorem diagOmega_apply_ne (t : Fin m → Fˣ) {a b : Fin m ⊕ Fin m} (hab : a ≠ b) :
    (diagOmega F m t : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F) a b = 0 := by
  rw [diagOmega_coe, diagonal_apply_ne _ hab]

theorem diagOmega_apply_self (t : Fin m → Fˣ) (a : Fin m ⊕ Fin m) :
    (diagOmega F m t : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F) a a = diagSpEntry t a := by
  rw [diagOmega_coe, diagonal_apply_eq]

theorem diagOmega_isometry (t : Fin m → Fˣ) (v : Fin m ⊕ Fin m → F) :
    StatedQuadPlus m F ((diagOmega F m t : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F) *ᵥ v) =
      StatedQuadPlus m F v := by
  rw [diagOmega_coe]
  unfold StatedQuadPlus
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [mulVec_diagonal, diagSpEntry_inl, diagSpEntry_inr]
  have h : ((t i : Fˣ) : F) * (((t i)⁻¹ : Fˣ) : F) = 1 := by simp
  linear_combination (v (Sum.inl i) * v (Sum.inr i)) * h

@[expose] def isometryClosure (F : Type) [Field F] (m : ℕ) : Subgroup (GL (Fin m ⊕ Fin m) F) :=
  Subgroup.closure {A : GL (Fin m ⊕ Fin m) F |
    ∀ v, StatedQuadPlus m F ((A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F) *ᵥ v) =
      StatedQuadPlus m F v}

theorem statedOmega_eq_commutator_isometryClosure :
    StatedOmega (StatedQuadPlus m F) = ⁅isometryClosure F m, isometryClosure F m⁆ :=
  rfl

theorem diagOmega_mem_isometryClosure (t : Fin m → Fˣ) :
    diagOmega F m t ∈ isometryClosure F m :=
  Subgroup.subset_closure (diagOmega_isometry t)

theorem diagOmega_mem_normalizer (t : Fin m → Fˣ) :
    diagOmega F m t ∈
      normalizer (StatedOmega (StatedQuadPlus m F) : Set (GL (Fin m ⊕ Fin m) F)) := by
  set C := isometryClosure F m
  have hx : diagOmega F m t ∈ C := diagOmega_mem_isometryClosure t
  have key : ∀ x ∈ C, ∀ y ∈ ⁅C, C⁆, x * y * x⁻¹ ∈ ⁅C, C⁆ := by
    intro x hxC y hy
    have hmap : (⁅C, C⁆).map (MulAut.conj x).toMonoidHom = ⁅C, C⁆ := by
      rw [Subgroup.map_commutator]
      have hC : C.map (MulAut.conj x).toMonoidHom = C := by
        ext z
        simp only [mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        constructor
        · rintro ⟨w, hw, rfl⟩
          exact mul_mem (mul_mem hxC hw) (inv_mem hxC)
        · intro hz
          exact ⟨x⁻¹ * z * x, mul_mem (mul_mem (inv_mem hxC) hz) hxC, by group⟩
      rw [hC]
    rw [← hmap]
    exact ⟨y, hy, rfl⟩
  rw [mem_normalizer_iff]
  intro y
  rw [statedOmega_eq_commutator_isometryClosure]
  constructor
  · exact key _ hx y
  · intro hy
    have := key _ (inv_mem hx) _ hy
    simpa [mul_assoc] using this

end Diagonal

section LeviFact

variable {F : Type} [Field F] {m : ℕ}

variable (F) in
@[expose] def omegaBlock (I : Finset (Fin m)) : Subgroup (GL (Fin m ⊕ Fin m) F) :=
  StatedOmega (StatedQuadPlus m F) ⊓ suppGL F (planeCoords I)

theorem omegaBlock_le_centralizer_of_const {I : Finset (Fin m)} {D : Set (Fin m → Fˣ)}
    (hconst : ∀ s ∈ D, ∀ a ∈ planeCoords I, ∀ b ∈ planeCoords I,
      diagSpEntry s a = diagSpEntry s b) :
    omegaBlock F I ≤ centralizer (diagOmega F m '' D) := by
  intro x hx
  rw [mem_centralizer_iff]
  rintro _ ⟨s, hs, rfl⟩
  refine ((commute_of_diag_iff (fun a b hab => diagOmega_apply_ne s hab) x).2
    fun a b hab => ?_).eq.symm
  rw [diagOmega_apply_self, diagOmega_apply_self] at hab
  by_cases h : a ∈ planeCoords I ∧ b ∈ planeCoords I
  · exact absurd (hconst s hs a h.1 b h.2) hab
  · have hne : a ≠ b := fun e => hab (e ▸ rfl)
    rw [(mem_inf.1 hx).2 a b h, Matrix.one_apply_ne hne]

theorem perfectCore_statedOmega_inf_centralizer_eq_perfectCore_omegaBlock [Finite F]
    {I : Finset (Fin m)} (D : Set (Fin m → Fˣ))
    (hconst : ∀ s ∈ D, ∀ a ∈ planeCoords I, ∀ b ∈ planeCoords I,
      diagSpEntry s a = diagSpEntry s b)
    (hsep : ∀ a b : Fin m ⊕ Fin m, a ≠ b → (a ∉ planeCoords I ∨ b ∉ planeCoords I) →
      ∃ s ∈ D, diagSpEntry s a ≠ diagSpEntry s b) :
    perfectCore (StatedOmega (StatedQuadPlus m F) ⊓ centralizer (diagOmega F m '' D)) =
      perfectCore (omegaBlock F I) := by
  rw [SymplecticPilot.perfectCore_inf_centralizer_eq_perfectCore_inf_suppGL
      (T := Set.univ) (fun x _ a b hab => absurd ⟨Set.mem_univ a, Set.mem_univ b⟩ hab)
      (diagOmega F m '' D)
      (by rintro _ ⟨s, -, rfl⟩ a b hab; exact diagOmega_apply_ne s hab)
      (fun a _ b _ hab hS => by
        obtain ⟨s, hs, hne⟩ := hsep a b hab hS
        exact ⟨diagOmega F m s, ⟨s, hs, rfl⟩, by
          rw [diagOmega_apply_self, diagOmega_apply_self]; exact hne⟩)]
  show perfectCore (omegaBlock F I ⊓ centralizer (diagOmega F m '' D)) = _
  rw [inf_of_le_left (omegaBlock_le_centralizer_of_const hconst)]

end LeviFact

end CFSG.SeitzReduction.OmegaPilot
