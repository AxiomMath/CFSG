module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualTypeARep

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Module QuadraticMap
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (plusIndexEquiv coordinateQuadPlus coordinateQuadPlus_apply)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear

variable {K : Type} [Field K] {n ℓ : ℕ} (P : LowPairing n ℓ)

@[expose] noncomputable def lowProj : (Fin (2 * n) → K) →ₗ[K] (Fin (2 * n) → K) :=
  coordLin (fun i => if i.val < ℓ then LinearMap.proj (plusIndexEquiv n (.inl i)) else 0)
    fun _ => 0

@[expose] noncomputable def lowLift : (Fin (2 * n) → K) →ₗ[K] (Fin (2 * n) → K) :=
  coordLin (fun _ => 0)
    fun i => if i.val < ℓ then LinearMap.proj (plusIndexEquiv n (.inl (P.τ i))) else 0

@[expose] noncomputable def midProj : (Fin (2 * n) → K) →ₗ[K] (Fin (2 * n) → K) :=
  coordLin (fun i => if i.val < ℓ then 0 else LinearMap.proj (plusIndexEquiv n (.inl i)))
    fun i => if i.val < ℓ then 0 else LinearMap.proj (plusIndexEquiv n (.inr i))

variable {P}

theorem lowProj_inl (v : Fin (2 * n) → K) (i : Fin n) :
    lowProj (K := K) (n := n) (ℓ := ℓ) v (plusIndexEquiv n (.inl i)) =
      if i.val < ℓ then v (plusIndexEquiv n (.inl i)) else 0 := by
  rw [lowProj, coordLin_inl]
  split_ifs <;> rfl

theorem lowProj_inr (v : Fin (2 * n) → K) (i : Fin n) :
    lowProj (K := K) (n := n) (ℓ := ℓ) v (plusIndexEquiv n (.inr i)) = 0 := by
  rw [lowProj, coordLin_inr]
  rfl

theorem lowLift_inl (v : Fin (2 * n) → K) (i : Fin n) :
    lowLift P v (plusIndexEquiv n (.inl i)) = 0 := by
  rw [lowLift, coordLin_inl]
  rfl

theorem lowLift_inr (v : Fin (2 * n) → K) (i : Fin n) :
    lowLift P v (plusIndexEquiv n (.inr i)) =
      if i.val < ℓ then v (plusIndexEquiv n (.inl (P.τ i))) else 0 := by
  rw [lowLift, coordLin_inr]
  split_ifs <;> rfl

theorem midProj_inl (v : Fin (2 * n) → K) (i : Fin n) :
    midProj (K := K) (n := n) (ℓ := ℓ) v (plusIndexEquiv n (.inl i)) =
      if i.val < ℓ then 0 else v (plusIndexEquiv n (.inl i)) := by
  rw [midProj, coordLin_inl]
  split_ifs <;> rfl

theorem midProj_inr (v : Fin (2 * n) → K) (i : Fin n) :
    midProj (K := K) (n := n) (ℓ := ℓ) v (plusIndexEquiv n (.inr i)) =
      if i.val < ℓ then 0 else v (plusIndexEquiv n (.inr i)) := by
  rw [midProj, coordLin_inr]
  split_ifs <;> rfl

theorem lowProj_mem_lowSpan (v : Fin (2 * n) → K) :
    lowProj (K := K) (n := n) (ℓ := ℓ) v ∈ lowSpan K n ℓ := fun i =>
  ⟨lowProj_inr v i, fun hi => by rw [lowProj_inl, ite_eq_right (by omega)]⟩

theorem lowProj_mem_range (v : Fin (2 * n) → K) :
    lowProj (K := K) (n := n) (ℓ := ℓ) v ∈ LinearMap.range (lowNil (K := K) P) := by
  rw [range_lowNil]
  exact lowProj_mem_lowSpan v

theorem lowProj_of_mem_lowSpan {w : Fin (2 * n) → K} (hw : w ∈ lowSpan K n ℓ) :
    lowProj (K := K) (n := n) (ℓ := ℓ) w = w := by
  refine ext_plus (fun i => ?_) fun i => ?_
  · rw [lowProj_inl]
    split_ifs with h
    · rfl
    · exact ((hw i).2 (by omega)).symm
  · rw [lowProj_inr, (hw i).1]

theorem lowProj_lowLift (v : Fin (2 * n) → K) :
    lowProj (K := K) (n := n) (ℓ := ℓ) (lowLift P v) = 0 :=
  ext_plus (fun i => by rw [lowProj_inl, lowLift_inl]; simp) fun i => lowProj_inr _ i

theorem lowProj_midProj (v : Fin (2 * n) → K) :
    lowProj (K := K) (n := n) (ℓ := ℓ) (midProj (K := K) (n := n) (ℓ := ℓ) v) = 0 :=
  ext_plus (fun i => by rw [lowProj_inl, midProj_inl]; split_ifs <;> rfl)
    fun i => lowProj_inr _ i

theorem lowNil_lowLift (v : Fin (2 * n) → K) :
    lowNil P (lowLift P v) = lowProj (K := K) (n := n) (ℓ := ℓ) v := by
  refine ext_plus (fun i => ?_) fun i => by rw [lowNil_inr, lowProj_inr]
  rw [lowNil_inl, lowLift_inr, lowProj_inl]
  split_ifs with h1 h2
  · rw [P.invol]
  · exact absurd ((P.lt_iff i).mpr h1) h2
  · rfl

theorem lowNil_midProj (v : Fin (2 * n) → K) :
    lowNil P (midProj (K := K) (n := n) (ℓ := ℓ) v) = 0 := by
  refine lowNil_of_mem_lowPerp P fun i hi => ?_
  rw [midProj_inr, ite_eq_left hi]

theorem lowNil_of_mem_lowSpan {w : Fin (2 * n) → K} (hw : w ∈ lowSpan K n ℓ) :
    lowNil P w = 0 :=
  lowNil_of_mem_lowPerp P (lowSpan_le_lowPerp ℓ hw)

theorem midProj_of_mem_lowSpan {w : Fin (2 * n) → K} (hw : w ∈ lowSpan K n ℓ) :
    midProj (K := K) (n := n) (ℓ := ℓ) w = 0 := by
  refine ext_plus (fun i => ?_) fun i => ?_
  · rw [midProj_inl]
    split_ifs with h
    · rfl
    · exact (hw i).2 (by omega)
  · rw [midProj_inr]
    split_ifs
    · rfl
    · exact (hw i).1

theorem midProj_lowLift (v : Fin (2 * n) → K) :
    midProj (K := K) (n := n) (ℓ := ℓ) (lowLift P v) = 0 := by
  refine ext_plus (fun i => ?_) fun i => ?_
  · rw [midProj_inl, lowLift_inl]
    split_ifs <;> rfl
  · rw [midProj_inr, lowLift_inr]
    split_ifs <;> rfl

theorem midProj_midProj (v : Fin (2 * n) → K) :
    midProj (K := K) (n := n) (ℓ := ℓ) (midProj (K := K) (n := n) (ℓ := ℓ) v) =
      midProj (K := K) (n := n) (ℓ := ℓ) v := by
  refine ext_plus (fun i => ?_) fun i => ?_
  · rw [midProj_inl, midProj_inl]
    split_ifs <;> rfl
  · rw [midProj_inr, midProj_inr]
    split_ifs <;> rfl

theorem lowProj_add_lowLift_add_midProj (v : Fin (2 * n) → K) :
    lowProj (K := K) (n := n) (ℓ := ℓ) v + lowLift P (lowNil P v) +
      midProj (K := K) (n := n) (ℓ := ℓ) v = v := by
  refine ext_plus (fun i => ?_) fun i => ?_
  · simp only [Pi.add_apply, lowProj_inl, lowLift_inl, midProj_inl]
    split_ifs <;> simp
  · simp only [Pi.add_apply, lowProj_inr, lowLift_inr, midProj_inr, lowNil_inl]
    split_ifs with h1 h2
    · rw [P.invol]
      simp
    · exact absurd ((P.lt_iff i).mpr h1) h2
    · simp

variable (P)

@[expose] noncomputable def lowProjU :
    (Fin (2 * n) → K) →ₗ[K] LinearMap.range (lowNil (K := K) P) :=
  LinearMap.codRestrict _ lowProj fun v => lowProj_mem_range (P := P) v

@[expose] noncomputable def leviLin (h : Module.End K (LinearMap.range (lowNil (K := K) P))) :
    (Fin (2 * n) → K) →ₗ[K] (Fin (2 * n) → K) :=
  (LinearMap.range (lowNil P)).subtype ∘ₗ h ∘ₗ lowProjU P +
    lowLift P ∘ₗ (LinearMap.range (lowNil P)).subtype ∘ₗ h ∘ₗ lowProjU P ∘ₗ lowNil P +
      midProj (K := K) (n := n) (ℓ := ℓ)

variable {P}

theorem coe_lowProjU (v : Fin (2 * n) → K) :
    (lowProjU P v : Fin (2 * n) → K) = lowProj (K := K) (n := n) (ℓ := ℓ) v :=
  rfl

theorem mem_lowSpan_of_mem_range {w : Fin (2 * n) → K}
    (hw : w ∈ LinearMap.range (lowNil (K := K) P)) : w ∈ lowSpan K n ℓ := by
  rwa [range_lowNil] at hw

theorem lowProjU_coe (u : LinearMap.range (lowNil (K := K) P)) :
    lowProjU P (u : Fin (2 * n) → K) = u :=
  Subtype.ext (lowProj_of_mem_lowSpan (mem_lowSpan_of_mem_range u.2))

theorem leviLin_apply (h : Module.End K (LinearMap.range (lowNil (K := K) P)))
    (v : Fin (2 * n) → K) :
    leviLin P h v = (h (lowProjU P v) : Fin (2 * n) → K) +
      lowLift P (h (lowProjU P (lowNil P v)) : Fin (2 * n) → K) +
        midProj (K := K) (n := n) (ℓ := ℓ) v :=
  rfl

theorem leviLin_apply_of_mem (h : Module.End K (LinearMap.range (lowNil (K := K) P)))
    (u : LinearMap.range (lowNil (K := K) P)) :
    leviLin P h (u : Fin (2 * n) → K) = (h u : Fin (2 * n) → K) := by
  have hu := mem_lowSpan_of_mem_range u.2
  rw [leviLin_apply, lowProjU_coe, lowNil_of_mem_lowSpan hu, map_zero, map_zero,
    Submodule.coe_zero, map_zero, midProj_of_mem_lowSpan hu, add_zero, add_zero]

theorem lowProjU_leviLin (h : Module.End K (LinearMap.range (lowNil (K := K) P)))
    (v : Fin (2 * n) → K) : lowProjU P (leviLin P h v) = h (lowProjU P v) := by
  apply Subtype.ext
  rw [coe_lowProjU, leviLin_apply, map_add, map_add, lowProj_lowLift, lowProj_midProj, add_zero,
    add_zero, lowProj_of_mem_lowSpan (mem_lowSpan_of_mem_range (h _).2)]

theorem lowNil_leviLin (h : Module.End K (LinearMap.range (lowNil (K := K) P)))
    (v : Fin (2 * n) → K) :
    lowNil P (leviLin P h v) = (h (lowProjU P (lowNil P v)) : Fin (2 * n) → K) := by
  rw [leviLin_apply, map_add, map_add, lowNil_of_mem_lowSpan (mem_lowSpan_of_mem_range (h _).2),
    lowNil_lowLift, lowNil_midProj, zero_add, add_zero,
    lowProj_of_mem_lowSpan (mem_lowSpan_of_mem_range (h _).2)]

theorem midProj_leviLin (h : Module.End K (LinearMap.range (lowNil (K := K) P)))
    (v : Fin (2 * n) → K) :
    midProj (K := K) (n := n) (ℓ := ℓ) (leviLin P h v) = midProj (K := K) (n := n) (ℓ := ℓ) v := by
  rw [leviLin_apply, map_add, map_add, midProj_of_mem_lowSpan (mem_lowSpan_of_mem_range (h _).2),
    midProj_lowLift, midProj_midProj, zero_add, zero_add]

theorem leviLin_lowNil (h : Module.End K (LinearMap.range (lowNil (K := K) P)))
    (v : Fin (2 * n) → K) : leviLin P h (lowNil P v) = lowNil P (leviLin P h v) := by
  rw [lowNil_leviLin, leviLin_apply_of_mem h ⟨lowNil P v, LinearMap.mem_range_self _ v⟩]
  congr 2
  exact (lowProjU_coe ⟨lowNil P v, LinearMap.mem_range_self _ v⟩).symm

theorem leviLin_mul (h h' : Module.End K (LinearMap.range (lowNil (K := K) P))) :
    leviLin P (h * h') = leviLin P h ∘ₗ leviLin P h' := by
  refine LinearMap.ext fun v => ?_
  rw [LinearMap.comp_apply, leviLin_apply h, lowProjU_leviLin, lowNil_leviLin, lowProjU_coe,
    midProj_leviLin, leviLin_apply]
  rfl

theorem leviLin_one : leviLin P (1 : Module.End K (LinearMap.range (lowNil (K := K) P))) =
    LinearMap.id := by
  refine LinearMap.ext fun v => ?_
  rw [leviLin_apply, Module.End.one_apply, Module.End.one_apply, coe_lowProjU, LinearMap.id_apply]
  conv_rhs => rw [← lowProj_add_lowLift_add_midProj (P := P) v]
  rw [coe_lowProjU, lowProj_of_mem_lowSpan (lowNil_mem_lowSpan P v)]

theorem leviLin_comp_symm
    (e : LinearMap.range (lowNil (K := K) P) ≃ₗ[K] LinearMap.range (lowNil (K := K) P)) :
    leviLin P e.toLinearMap ∘ₗ leviLin P e.symm.toLinearMap = LinearMap.id := by
  rw [← leviLin_mul, ← leviLin_one (P := P)]
  congr 1
  exact e.comp_symm

theorem leviLin_symm_comp
    (e : LinearMap.range (lowNil (K := K) P) ≃ₗ[K] LinearMap.range (lowNil (K := K) P)) :
    leviLin P e.symm.toLinearMap ∘ₗ leviLin P e.toLinearMap = LinearMap.id := by
  rw [← leviLin_mul, ← leviLin_one (P := P)]
  congr 1
  exact e.symm_comp

@[expose] noncomputable def leviEquiv
    (e : LinearMap.range (lowNil (K := K) P) ≃ₗ[K] LinearMap.range (lowNil (K := K) P)) :
    (Fin (2 * n) → K) ≃ₗ[K] (Fin (2 * n) → K) :=
  LinearEquiv.ofLinearMap (leviLin P e.toLinearMap) (leviLin P e.symm.toLinearMap)
    (leviLin_comp_symm e) (leviLin_symm_comp e)

theorem leviEquiv_apply
    (e : LinearMap.range (lowNil (K := K) P) ≃ₗ[K] LinearMap.range (lowNil (K := K) P))
    (v : Fin (2 * n) → K) : leviEquiv e v = leviLin P e.toLinearMap v :=
  rfl

variable (P) in
@[expose] noncomputable def leviHom :
    (LinearMap.range (lowNil (K := K) P) ≃ₗ[K] LinearMap.range (lowNil (K := K) P)) →*
      ((Fin (2 * n) → K) ≃ₗ[K] (Fin (2 * n) → K)) where
  toFun e := leviEquiv e
  map_one' := by
    refine LinearEquiv.ext fun v => ?_
    rw [leviEquiv_apply]
    have h1 : (1 : LinearMap.range (lowNil (K := K) P) ≃ₗ[K]
        LinearMap.range (lowNil (K := K) P)).toLinearMap = 1 := rfl
    rw [h1, leviLin_one]
    rfl
  map_mul' e e' := by
    refine LinearEquiv.ext fun v => ?_
    rw [leviEquiv_apply]
    have h1 : (e * e' : LinearMap.range (lowNil (K := K) P) ≃ₗ[K]
        LinearMap.range (lowNil (K := K) P)).toLinearMap = e.toLinearMap * e'.toLinearMap := rfl
    rw [h1, leviLin_mul]
    rfl

theorem coordinateQuadPlus_add_lowLift_add_midProj {a b : Fin (2 * n) → K}
    (ha : a ∈ lowSpan K n ℓ) (v : Fin (2 * n) → K) :
    coordinateQuadPlus n K (a + lowLift P b + midProj (K := K) (n := n) (ℓ := ℓ) v) =
      lowForm P a b + ∑ i, if i.val < ℓ then 0 else
        v (plusIndexEquiv n (.inl i)) * v (plusIndexEquiv n (.inr i)) := by
  rw [coordinateQuadPlus_apply, lowForm, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.add_apply, lowLift_inl, lowLift_inr, midProj_inl, midProj_inr, (ha i).1]
  split_ifs with hi
  · simp
  · rw [(ha i).2 (by omega)]
    simp

theorem coordinateQuadPlus_leviLin (h : Module.End K (LinearMap.range (lowNil (K := K) P)))
    (hβ : ∀ u u' : LinearMap.range (lowNil (K := K) P),
      lowForm P (h u : Fin (2 * n) → K) (h u') = lowForm P (u : Fin (2 * n) → K) u')
    (v : Fin (2 * n) → K) : coordinateQuadPlus n K (leviLin P h v) = coordinateQuadPlus n K v := by
  rw [leviLin_apply, coordinateQuadPlus_add_lowLift_add_midProj (mem_lowSpan_of_mem_range (h _).2),
    hβ]
  conv_rhs => rw [← lowProj_add_lowLift_add_midProj (P := P) v]
  rw [coordinateQuadPlus_add_lowLift_add_midProj (lowProj_mem_lowSpan v),
    coe_lowProjU, coe_lowProjU, lowProj_of_mem_lowSpan (lowNil_mem_lowSpan P v)]

theorem wallForm_eq_lowForm [CharP K 2] (u u' : LinearMap.range (lowNil (K := K) P)) :
    wallForm (QuadraticMap.polarBilin (coordinateQuadPlus n K)) (lowNil P) (polar_lowNil_left P)
      u u' = lowForm P (u : Fin (2 * n) → K) u' := by
  obtain ⟨_, x, rfl⟩ := u
  obtain ⟨_, y, rfl⟩ := u'
  rw [wallForm_apply, polar_lowNil_eq_lowForm]

end CFSG.SeitzReduction.OmegaPilot
