module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualTypeASection
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualTypeANTDet

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Module QuadraticMap CFSG.Assembly.LowTwoRank
open CFSG.Quasithin (perfectCore perfectCore_le le_perfectCore_of_perfect perfectCore_perfect)
open LinearPilot (autFixSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (plusIndexEquiv coordinateQuadPlus coordinateQuadPlus_apply)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter (isometryConjugationHom)
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.Quasithin.G11.P3Ortho.Om4 (rho' rho'_injective)

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n ℓ : ℕ} (P : LowPairing n ℓ)

section Rel

variable {m : ℕ} (h : ℓ + m = n) (hQ : ∃ v, coordinateQuadPlus n K v ≠ 0)

omit [Finite K] in
theorem projLift_rel_of_block (x : typeACore K P) (t : K)
    (hg : ∀ w, coreBlockHom P h hQ x (coreBlockHom P h hQ x w) -
      t • coreBlockHom P h hQ x w + w = 0)
    {v : Fin (2 * n) → K} (hv : v ∈ lowPerp K n ℓ) :
    projLift hQ (x : matrixProjectiveDerived (coordinateQuadPlus n K))
        (projLift hQ (x : matrixProjectiveDerived (coordinateQuadPlus n K)) v) -
      t • projLift hQ (x : matrixProjectiveDerived (coordinateQuadPlus n K)) v + v ∈
        lowSpan K n ℓ := by
  set g := (projLift hQ (x : matrixProjectiveDerived (coordinateQuadPlus n K)) :
    (Fin (2 * n) → K) →ₗ[K] (Fin (2 * n) → K)) with hgdef
  have hgW : ∀ u ∈ lowSpan K n ℓ, g u ∈ lowSpan K n ℓ := fun u hu =>
    projLift_mem_lowSpan_of_mem_core P hQ x.2 hu
  have hgP : ∀ u ∈ lowPerp K n ℓ, g u ∈ lowPerp K n ℓ := fun u hu =>
    projLift_mem_lowPerp_of_mem_core P hQ x.2 hu
  have hv1 := hgP v hv
  refine mem_lowSpan_of_mem_lowPerp h
    (add_mem (sub_mem (hgP _ hv1) (Submodule.smul_mem _ _ hv1)) hv) ?_
  have e1 := comp_blockCoord_of_mem_lowPerp h hgW hv
  have e2 := comp_blockCoord_of_mem_lowPerp h hgW hv1
  have hsplit : (g (g v) - t • g v + v) ∘ blockCoord h =
      g (g v) ∘ blockCoord h - t • (g v ∘ blockCoord h) + v ∘ blockCoord h := rfl
  change (g (g v) - t • g v + v) ∘ blockCoord h = 0
  rw [hsplit, e2, e1]
  exact hg (v ∘ blockCoord h)

omit [Finite K] in
theorem eq_of_projLift_rel (hm : 0 < m) (x : typeACore K P) (t s : K)
    (hg : ∀ w, coreBlockHom P h hQ x (coreBlockHom P h hQ x w) -
      t • coreBlockHom P h hQ x w + w = 0)
    (hs : ∀ v ∈ lowPerp K n ℓ,
      projLift hQ (x : matrixProjectiveDerived (coordinateQuadPlus n K))
          (projLift hQ (x : matrixProjectiveDerived (coordinateQuadPlus n K)) v) -
        s • projLift hQ (x : matrixProjectiveDerived (coordinateQuadPlus n K)) v + v ∈
          lowSpan K n ℓ) :
    s = t := by
  set g := (projLift hQ (x : matrixProjectiveDerived (coordinateQuadPlus n K)) :
    (Fin (2 * n) → K) →ₗ[K] (Fin (2 * n) → K)) with hgdef
  have hgW : ∀ u ∈ lowSpan K n ℓ, g u ∈ lowSpan K n ℓ := fun u hu =>
    projLift_mem_lowSpan_of_mem_core P hQ x.2 hu
  have hgP : ∀ u ∈ lowPerp K n ℓ, g u ∈ lowPerp K n ℓ := fun u hu =>
    projLift_mem_lowPerp_of_mem_core P hQ x.2 hu
  have key : ∀ w, (t - s) • coreBlockHom P h hQ x w = 0 := by
    intro w
    have hv := extend_blockCoord_mem_lowPerp h w
    have hv1 := hgP _ hv
    have h0 := comp_blockCoord_eq_zero_of_mem_lowSpan h (hs _ hv)
    have e1 := comp_blockCoord_of_mem_lowPerp h hgW hv
    have e2 := comp_blockCoord_of_mem_lowPerp h hgW hv1
    have hsplit : (g (g (Function.extend (blockCoord h) w 0)) -
        s • g (Function.extend (blockCoord h) w 0) + Function.extend (blockCoord h) w 0) ∘
          blockCoord h =
        g (g (Function.extend (blockCoord h) w 0)) ∘ blockCoord h -
          s • (g (Function.extend (blockCoord h) w 0) ∘ blockCoord h) +
          Function.extend (blockCoord h) w 0 ∘ blockCoord h := rfl
    change (g (g (Function.extend (blockCoord h) w 0)) -
        s • g (Function.extend (blockCoord h) w 0) + Function.extend (blockCoord h) w 0) ∘
          blockCoord h = 0 at h0
    rw [hsplit, e2, e1, extend_blockCoord_comp] at h0
    have h1 := hg w
    change blockPart h g (blockPart h g w) - s • blockPart h g w + w = 0 at h0
    change blockPart h g (blockPart h g w) - t • blockPart h g w + w = 0 at h1
    change (t - s) • blockPart h g w = 0
    rw [sub_smul]
    calc t • blockPart h g w - s • blockPart h g w =
        (blockPart h g (blockPart h g w) - s • blockPart h g w + w) -
          (blockPart h g (blockPart h g w) - t • blockPart h g w + w) := by abel
      _ = 0 := by rw [h0, h1, sub_zero]
  set e : Fin (2 * m) → K := Pi.single ⟨0, by omega⟩ 1 with he
  have he0 : e ≠ 0 := by
    intro h0
    have := congrFun h0 ⟨0, by omega⟩
    rw [he, Pi.single_eq_same] at this
    exact one_ne_zero this
  have h2 := key ((coreBlockHom P h hQ x).symm e)
  rw [LinearEquiv.apply_symm_apply] at h2
  rcases smul_eq_zero.mp h2 with h3 | h3
  · exact (sub_eq_zero.mp h3).symm
  · exact absurd h3 he0

end Rel

section Two

variable (h : ℓ + 2 = n) (hQ : ∃ v, coordinateQuadPlus n K v ≠ 0) (hq4 : 4 ≤ Nat.card K)

include hQ hq4 in
theorem range_blockLeviP_le_two : (blockLeviP (K := K) h).range ≤ typeACore K P := by
  have : Group.IsPerfect (orthDerived (coordinateQuadPlus 2 K)) := isPerfect_orthDerived_two K hq4
  refine le_perfectCore_of_perfect ?_
    (Subgroup.isPerfect_iff.mp (Group.IsPerfect.range (blockLeviP (K := K) h)))
  rintro _ ⟨g, rfl⟩
  refine mem_autFixSubgroup_of_commute hQ (lowRep P) fun v => ?_
  rw [projLift_blockLeviP h hQ]
  change blockExtend h g (matrixLinearEquiv (lowRepGL P) v) =
    matrixLinearEquiv (lowRepGL P) (blockExtend h g v)
  rw [matrixLinearEquiv_lowRepGL, matrixLinearEquiv_lowRepGL, map_add, blockExtend_lowNil]

include hq4 in
theorem exists_coreBlockHom_eq_two (g : orthDerived (coordinateQuadPlus 2 K)) :
    ∃ x : typeACore K P, coreBlockHom P h hQ x = g := by
  refine ⟨⟨blockLeviP h g, range_blockLeviP_le_two P h hQ hq4 ⟨g, rfl⟩⟩, ?_⟩
  apply LinearEquiv.toLinearMap_injective
  rw [coreBlockHom_toLinearMap]
  change blockPart h (projLift hQ (blockLeviP h g) : (Fin (2 * n) → K) →ₗ[K] (Fin (2 * n) → K)) = _
  rw [projLift_blockLeviP h hQ, blockPart_blockExtend]

@[expose] noncomputable def coreSLPair :
    typeACore K P →* Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K :=
  (orthTwoEquiv K hq4).toMonoidHom.comp (coreSectionHom P h hQ)

theorem rho'_coreSLPair (x : typeACore K P) :
    rho' K (coreSLPair P h hQ hq4 x) = detConj K (coreBlockHom P h hQ x) :=
  rho'_orthTwoEquiv K hq4 (coreSectionHom P h hQ x)

theorem coreSLPair_surjective : Function.Surjective (coreSLPair P h hQ hq4) := by
  intro z
  obtain ⟨x, hx⟩ := exists_coreBlockHom_eq_two P h hQ hq4 ((orthTwoEquiv K hq4).symm z)
  refine ⟨x, ?_⟩
  have hx' : coreSectionHom P h hQ x = (orthTwoEquiv K hq4).symm z := Subtype.ext hx
  change orthTwoEquiv K hq4 (coreSectionHom P h hQ x) = z
  rw [hx', MulEquiv.apply_symm_apply]

theorem coreSLPair_eq_one_iff (x : typeACore K P) :
    coreSLPair P h hQ hq4 x = 1 ↔
      kerQuotHom hQ (typeACore K P) (lowNil P)
        (fun _ hx v => projLift_lowNil_of_mem_core hQ hx v) x = 1 := by
  rw [← coreBlockHom_eq_one_iff P h hQ x]
  change orthTwoEquiv K hq4 (coreSectionHom P h hQ x) = 1 ↔ _
  rw [MulEquiv.map_eq_one_iff]
  constructor
  · intro h1
    exact congrArg Subtype.val h1
  · intro h1
    exact Subtype.ext h1

theorem coreBlockHom_eq_left (x : typeACore K P) (hx : (coreSLPair P h hQ hq4 x).2 = 1) :
    coreBlockHom P h hQ x = (detConj K).symm (rho' K ((coreSLPair P h hQ hq4 x).1, 1)) := by
  have e : coreSLPair P h hQ hq4 x = ((coreSLPair P h hQ hq4 x).1, 1) := Prod.ext rfl hx
  rw [← e, rho'_coreSLPair, MulEquiv.symm_apply_apply]

theorem coreBlockHom_eq_right (x : typeACore K P) (hx : (coreSLPair P h hQ hq4 x).1 = 1) :
    coreBlockHom P h hQ x = (detConj K).symm (rho' K (1, (coreSLPair P h hQ hq4 x).2)) := by
  have e : coreSLPair P h hQ hq4 x = (1, (coreSLPair P h hQ hq4 x).2) := Prod.ext hx rfl
  rw [← e, rho'_coreSLPair, MulEquiv.symm_apply_apply]

theorem projLift_rel_left (x : typeACore K P) (hx : (coreSLPair P h hQ hq4 x).2 = 1)
    {v : Fin (2 * n) → K} (hv : v ∈ lowPerp K n ℓ) :
    projLift hQ (x : matrixProjectiveDerived (coordinateQuadPlus n K))
        (projLift hQ (x : matrixProjectiveDerived (coordinateQuadPlus n K)) v) -
      Matrix.trace ((coreSLPair P h hQ hq4 x).1 : Matrix (Fin 2) (Fin 2) K) •
        projLift hQ (x : matrixProjectiveDerived (coordinateQuadPlus n K)) v + v ∈
        lowSpan K n ℓ :=
  projLift_rel_of_block P h hQ x _ (fun w => by
    rw [coreBlockHom_eq_left P h hQ hq4 x hx]
    exact rel_left K _ w) hv

theorem projLift_rel_right (x : typeACore K P) (hx : (coreSLPair P h hQ hq4 x).1 = 1)
    {v : Fin (2 * n) → K} (hv : v ∈ lowPerp K n ℓ) :
    projLift hQ (x : matrixProjectiveDerived (coordinateQuadPlus n K))
        (projLift hQ (x : matrixProjectiveDerived (coordinateQuadPlus n K)) v) -
      Matrix.trace ((coreSLPair P h hQ hq4 x).2 : Matrix (Fin 2) (Fin 2) K) •
        projLift hQ (x : matrixProjectiveDerived (coordinateQuadPlus n K)) v + v ∈
        lowSpan K n ℓ :=
  projLift_rel_of_block P h hQ x _ (fun w => by
    rw [coreBlockHom_eq_right P h hQ hq4 x hx]
    exact rel_right K _ w) hv

theorem eq_trace_left (x : typeACore K P) (hx : (coreSLPair P h hQ hq4 x).2 = 1) (s : K)
    (hs : ∀ v ∈ lowPerp K n ℓ,
      projLift hQ (x : matrixProjectiveDerived (coordinateQuadPlus n K))
          (projLift hQ (x : matrixProjectiveDerived (coordinateQuadPlus n K)) v) -
        s • projLift hQ (x : matrixProjectiveDerived (coordinateQuadPlus n K)) v + v ∈
          lowSpan K n ℓ) :
    s = Matrix.trace ((coreSLPair P h hQ hq4 x).1 : Matrix (Fin 2) (Fin 2) K) :=
  eq_of_projLift_rel P h hQ (by norm_num) x _ s (fun w => by
    rw [coreBlockHom_eq_left P h hQ hq4 x hx]
    exact rel_left K _ w) hs

theorem eq_trace_right (x : typeACore K P) (hx : (coreSLPair P h hQ hq4 x).1 = 1) (s : K)
    (hs : ∀ v ∈ lowPerp K n ℓ,
      projLift hQ (x : matrixProjectiveDerived (coordinateQuadPlus n K))
          (projLift hQ (x : matrixProjectiveDerived (coordinateQuadPlus n K)) v) -
        s • projLift hQ (x : matrixProjectiveDerived (coordinateQuadPlus n K)) v + v ∈
          lowSpan K n ℓ) :
    s = Matrix.trace ((coreSLPair P h hQ hq4 x).2 : Matrix (Fin 2) (Fin 2) K) :=
  eq_of_projLift_rel P h hQ (by norm_num) x _ s (fun w => by
    rw [coreBlockHom_eq_right P h hQ hq4 x hx]
    exact rel_right K _ w) hs

end Two

end CFSG.SeitzReduction.OmegaPilot
