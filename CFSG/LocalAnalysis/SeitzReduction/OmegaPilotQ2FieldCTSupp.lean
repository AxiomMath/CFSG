module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotQ2SwapGen
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotUniqueGen
public import CFSG.RankThree.PartOne.KC.OrthogonalComponentFacts

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived
  matrixDerived matrixProjectiveProjection)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadPlus
  coordinateQuadMinus plusIndexEquiv)
open CFSG.SeitzReduction.SymplecticPilot (suppGL IsSuppMat mem_suppGL planeCoords)
open CFSG.Assembly.LowTwoRank (StatedOmega StatedQuadPlus)

section Supp

variable {K : Type} [Field K] {d : ℕ}

variable (Q : QuadraticForm K (Fin d → K)) in
@[expose] noncomputable def suppBar (C : Set (Fin d)) : Subgroup (matrixProjectiveDerived Q) :=
  ((suppGL K C).comap (matrixDerived Q).subtype).map (matrixProjectiveProjection Q)

variable {Q : QuadraticForm K (Fin d → K)}

theorem suppBar_le_centralizer {C D : Set (Fin d)} (h : Disjoint C D) :
    suppBar Q C ≤ centralizer (suppBar Q D : Set (matrixProjectiveDerived Q)) := by
  rintro _ ⟨A, hA, rfl⟩
  rw [mem_centralizer_iff]
  rintro _ ⟨B, hB, rfl⟩
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul]
  exact (commute_of_mem_suppGL_of_disjoint h hA hB).eq.symm

theorem projHom_mem_suppBar_of_entry {C : Set (Fin d)} (g : orthDerived Q)
    (hg : ∀ a b, ¬ (a ∈ C ∧ b ∈ C) →
      (g : (Fin d → K) ≃ₗ[K] (Fin d → K)) (Pi.single b 1) a = (1 : Matrix (Fin d) (Fin d) K) a b) :
    projHom Q g ∈ suppBar Q C := by
  refine ⟨(derivedEquiv Q).symm g, ?_, rfl⟩
  rw [SetLike.mem_coe, mem_comap]
  intro a b hab
  change ((derivedEquiv Q).symm g : GL (Fin d) K).val a b = (1 : Matrix (Fin d) (Fin d) K) a b
  rw [derivedEquiv_symm_entry]
  exact hg a b hab

theorem entry_eq_of_fix {C : Set (Fin d)} {g : (Fin d → K) ≃ₗ[K] (Fin d → K)}
    (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hfix : ∀ b, b ∉ C → g (Pi.single b 1) = Pi.single b 1)
    (hdual : ∀ a, a ∉ C → ∃ a', a' ∉ C ∧ ∃ β : K, β ≠ 0 ∧
      ∀ v, QuadraticMap.polar Q (Pi.single a' 1) v = β * v a) :
    ∀ a b, ¬ (a ∈ C ∧ b ∈ C) → g (Pi.single b 1) a = (1 : Matrix (Fin d) (Fin d) K) a b := by
  intro a b hab
  by_cases hb : b ∈ C
  · have ha : a ∉ C := fun ha => hab ⟨ha, hb⟩
    obtain ⟨a', ha', β, hβ, hpol⟩ := hdual a ha
    have h1 := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hgO (Pi.single a' 1)
      (Pi.single b 1)
    rw [hfix a' ha', hpol, hpol] at h1
    have hab' : a ≠ b := fun e => ha (e ▸ hb)
    rw [Pi.single_eq_of_ne hab', mul_zero] at h1
    rw [Matrix.one_apply_ne hab']
    exact (mul_eq_zero.1 h1).resolve_left hβ
  · rw [hfix b hb, Matrix.one_apply, Pi.single_apply]

theorem projHom_mem_suppBar_of_fix {C : Set (Fin d)} (g : orthDerived Q)
    (hfix : ∀ b, b ∉ C →
      (g : (Fin d → K) ≃ₗ[K] (Fin d → K)) (Pi.single b 1) = Pi.single b 1)
    (hdual : ∀ a, a ∉ C → ∃ a', a' ∉ C ∧ ∃ β : K, β ≠ 0 ∧
      ∀ v, QuadraticMap.polar Q (Pi.single a' 1) v = β * v a) :
    projHom Q g ∈ suppBar Q C :=
  projHom_mem_suppBar_of_entry g (entry_eq_of_fix
    (CFSG.RankThree.PartOne.KCOrthogonal.orthDerived_le_orthogonalGroup g.2) hfix hdual)

theorem IsHypCoord.dual_left {a b : Fin d} (h : IsHypCoord Q a b) :
    ∀ v, QuadraticMap.polar Q (Pi.single b 1) v = 1 * v a := fun v => by
  rw [one_mul, h.polar_right]

theorem IsHypCoord.dual_right {a b : Fin d} (h : IsHypCoord Q a b) :
    ∀ v, QuadraticMap.polar Q (Pi.single a 1) v = 1 * v b := fun v => by
  rw [one_mul, h.polar_left]

end Supp

section Embed

open CFSG.RankThree.PartOne.KCOrthogonalSubfield (incl incl_mk inclHom inclHom_val glIncl_val)
open CFSG.Adapters.RankTwoModelTransports (glCongr glCongr_coe)

theorem statedDerivedPlusEquiv_entry (F : Type) [Field F] [CharP F 2] (m : ℕ)
    (x : StatedOmega (StatedQuadPlus m F)) (a b : Fin (2 * m)) :
    ((statedDerivedPlusEquiv F m x : matrixDerived (coordinateQuadPlus m F)) :
      GL (Fin (2 * m)) F).val a b =
      (x : GL (Fin m ⊕ Fin m) F).val ((plusIndexEquiv m).symm a) ((plusIndexEquiv m).symm b) := by
  have h := statedDerivedPlusEquiv_symm_entry F m (statedDerivedPlusEquiv F m x)
    ((plusIndexEquiv m).symm a) ((plusIndexEquiv m).symm b)
  rw [MulEquiv.symm_apply_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h
  exact h.symm

theorem isSuppMat_statedDerivedPlusEquiv {F : Type} [Field F] [CharP F 2] {m : ℕ}
    {S : Set (Fin m ⊕ Fin m)} {x : StatedOmega (StatedQuadPlus m F)}
    (hx : (x : GL (Fin m ⊕ Fin m) F) ∈ suppGL F S) :
    ((statedDerivedPlusEquiv F m x : matrixDerived (coordinateQuadPlus m F)) :
      GL (Fin (2 * m)) F) ∈ suppGL F (plusIndexEquiv m '' S) := by
  intro a b hab
  rw [statedDerivedPlusEquiv_entry]
  have hab' : ¬ ((plusIndexEquiv m).symm a ∈ S ∧ (plusIndexEquiv m).symm b ∈ S) := by
    rintro ⟨ha, hb⟩
    exact hab ⟨⟨_, ha, Equiv.apply_symm_apply _ a⟩, ⟨_, hb, Equiv.apply_symm_apply _ b⟩⟩
  rw [hx _ _ hab', Matrix.one_apply, Matrix.one_apply]
  simp only [(plusIndexEquiv m).symm.injective.eq_iff]

theorem siegelNode_le_suppGL {F : Type} [Field F] {n : ℕ} (j : Fin n) :
    siegelNode F n j ≤ suppGL F (planeCoords (plusNodeSet n j)) :=
  (map_mono (siegelBlockGL_le_suppGL _)).trans (map_flipGL_suppGL_le _ _)

theorem rationalNode_le_suppBar {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}
    (hn : 1 ≤ n) (j : Fin n) :
    rationalNode (K := F) hn j ≤
      suppBar (coordinateQuadPlus n F) (plusIndexEquiv n '' planeCoords (plusNodeSet n j)) := by
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨statedDerivedPlusEquiv F n x, ?_, rfl⟩
  rw [SetLike.mem_coe, mem_comap]
  exact isSuppMat_statedDerivedPlusEquiv (siegelNode_le_suppGL j (mem_subgroupOf.1 hx))

variable {K : Type} [Field K] [Finite K] [CharP K 2] {F : Type} [Field F] [Finite F] [CharP F 2]

theorem statedOmegaPlusEquiv_symm_mk {m : ℕ} (hm : 1 ≤ m)
    (A : matrixDerived (coordinateQuadPlus m K)) :
    (statedOmegaPlusEquiv K m hm).symm (matrixProjectiveProjection _ A) =
      (statedDerivedPlusEquiv K m).symm A := by
  rw [MulEquiv.symm_apply_eq]
  change _ = matrixProjectiveProjection _ (statedDerivedPlusEquiv K m
    ((statedDerivedPlusEquiv K m).symm A))
  rw [MulEquiv.apply_symm_apply]

theorem map_fieldEmbed_suppBar_le (ι : K →+* F) {n : ℕ} (hn : 1 ≤ n) (C : Set (Fin (2 * n))) :
    (suppBar (coordinateQuadPlus n K) C).map (fieldEmbed ι n hn) ≤
      suppBar (coordinateQuadPlus n F) C := by
  rintro _ ⟨_, ⟨A, hA, rfl⟩, rfl⟩
  rw [SetLike.mem_coe, mem_comap] at hA
  set k := ι.fieldRange
  set y := statedOmegaPlusCongr ι.rangeRestrictFieldEquiv n ((statedDerivedPlusEquiv K n).symm A)
    with hy
  have he : fieldEmbed ι n hn (matrixProjectiveProjection _ A) =
      matrixProjectiveProjection _ (inclHom k (E7Pilot.isExtension_coordinateQuadPlus n k)
        (statedDerivedPlusEquiv k n y)) := by
    change incl k _ (statedOmegaPlusEquiv k n hn (statedOmegaPlusCongr _ n
      ((statedOmegaPlusEquiv K n hn).symm (matrixProjectiveProjection _ A)))) = _
    rw [statedOmegaPlusEquiv_symm_mk]
    rfl
  rw [he]
  refine ⟨_, ?_, rfl⟩
  rw [SetLike.mem_coe, mem_comap]
  intro a b hab
  change ((inclHom k (E7Pilot.isExtension_coordinateQuadPlus n k) (statedDerivedPlusEquiv k n y) :
    matrixDerived (coordinateQuadPlus n F)) : GL (Fin (2 * n)) F).val a b = _
  rw [inclHom_val, glIncl_val, Matrix.map_apply, statedDerivedPlusEquiv_entry, hy,
    coe_statedOmegaPlusCongr, glCongr_coe, Matrix.map_apply, statedDerivedPlusEquiv_symm_entry,
    Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  change ((ι.rangeRestrictFieldEquiv ((A : GL (Fin (2 * n)) K).val a b) : k) : F) = _
  have h1 : (A : GL (Fin (2 * n)) K).val a b = (1 : Matrix (Fin (2 * n)) (Fin (2 * n)) K) a b :=
    hA a b hab
  rw [h1, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

end Embed

section Fix

variable {K : Type} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}

theorem fixVecBar_le_suppBar {S : Set (Fin d → K)} {C : Set (Fin d)}
    (hS : ∀ b, b ∉ C → (Pi.single b 1 : Fin d → K) ∈ S)
    (hdual : ∀ a, a ∉ C → ∃ a', a' ∉ C ∧ ∃ β : K, β ≠ 0 ∧
      ∀ v, QuadraticMap.polar Q (Pi.single a' 1) v = β * v a) :
    fixVecBar Q S ≤ suppBar Q C := by
  rintro _ ⟨g, hg, rfl⟩
  exact projHom_mem_suppBar_of_fix g (fun b hb => mem_subgroupOf.1 hg _ (hS b hb)) hdual

theorem map_fixVecBar_le_of_isometry {d' : ℕ} {Q' : QuadraticForm K (Fin d' → K)}
    (M : Q.IsometryEquiv Q') (Θ : matrixProjectiveDerived Q →* matrixProjectiveDerived Q')
    (hΘ : ∀ g, Θ (projHom Q g) = projHom Q' (orthDerivedCongr M g)) (T : Set (Fin d → K)) :
    (fixVecBar Q T).map Θ ≤ fixVecBar Q' (M.toLinearEquiv '' T) := by
  rintro _ ⟨_, ⟨g, hg, rfl⟩, rfl⟩
  rw [hΘ]
  refine ⟨orthDerivedCongr M g, mem_subgroupOf.2 ?_, rfl⟩
  rintro _ ⟨v, hv, rfl⟩
  rw [orthDerivedCongr_apply, LinearEquiv.symm_apply_apply, mem_subgroupOf.1 hg v hv]

theorem mulVec_eq_self_of_mem_suppGL {C : Set (Fin d)} {A : GL (Fin d) K} (hA : A ∈ suppGL K C)
    {v : Fin d → K} (hv : ∀ i ∈ C, v i = 0) : Matrix.mulVec A.val v = v := by
  have h : Matrix.mulVec A.val v = Matrix.mulVec (1 : Matrix (Fin d) (Fin d) K) v := by
    funext a
    simp only [Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl fun t _ => ?_
    by_cases ht : t ∈ C
    · rw [hv t ht, mul_zero, mul_zero]
    · have h1 : A.val a t = (1 : Matrix (Fin d) (Fin d) K) a t := hA a t (fun h => ht h.2)
      rw [h1]
  rw [h, Matrix.one_mulVec]

theorem projHom_orthDerivedCongr_mem_suppBar {d' : ℕ} {Q' : QuadraticForm K (Fin d' → K)}
    (M : Q.IsometryEquiv Q') {C : Set (Fin d)} {C' : Set (Fin d')}
    (hM : ∀ z : Fin d → K, (∀ i ∈ C', M.toLinearEquiv z i = 0) → ∀ i ∈ C, z i = 0)
    (hdual : ∀ a, a ∉ C' → ∃ a', a' ∉ C' ∧ ∃ β : K, β ≠ 0 ∧
      ∀ v, QuadraticMap.polar Q' (Pi.single a' 1) v = β * v a)
    {A : matrixDerived Q} (hA : (A : GL (Fin d) K) ∈ suppGL K C) :
    projHom Q' (orthDerivedCongr M (derivedEquiv Q A)) ∈ suppBar Q' C' := by
  refine projHom_mem_suppBar_of_fix _ (fun b hb => ?_) hdual
  rw [orthDerivedCongr_apply, coe_derivedEquiv]
  have hz : ∀ i ∈ C, (M.toLinearEquiv.symm (Pi.single b 1)) i = 0 := by
    refine hM _ fun i hi => ?_
    rw [LinearEquiv.apply_symm_apply]
    exact Pi.single_eq_of_ne (fun h => hb (by rw [← h]; exact hi)) 1
  change M.toLinearEquiv
    (CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear.matrixLinearEquiv
      (A : GL (Fin d) K) (M.toLinearEquiv.symm (Pi.single b 1))) = _
  rw [CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear.matrixLinearEquiv_apply,
    mulVec_eq_self_of_mem_suppGL hA hz, LinearEquiv.apply_symm_apply]

theorem projHom_derivedEquiv (A : matrixDerived Q) :
    projHom Q (derivedEquiv Q A) = matrixProjectiveProjection Q A := by
  change matrixProjectiveProjection Q ((derivedEquiv Q).symm (derivedEquiv Q A)) = _
  rw [MulEquiv.symm_apply_apply]

theorem dual_coordinateQuadPlus {n : ℕ} (P : Finset (Fin n)) :
    ∀ a, a ∉ plusIndexEquiv n '' planeCoords P → ∃ a', a' ∉ plusIndexEquiv n '' planeCoords P ∧
      ∃ β : K, β ≠ 0 ∧
        ∀ v, QuadraticMap.polar (coordinateQuadPlus n K) (Pi.single a' 1) v = β * v a := by
  intro a ha
  obtain ⟨s, rfl⟩ := (plusIndexEquiv n).surjective a
  have hs : s ∉ planeCoords P := fun h => ha ⟨s, h, rfl⟩
  have hnot : ∀ t : Fin n ⊕ Fin n, SymplecticPilot.planeOf t = SymplecticPilot.planeOf s →
      plusIndexEquiv n t ∉ plusIndexEquiv n '' planeCoords P := by
    rintro t ht ⟨t', ht', e⟩
    rw [(plusIndexEquiv n).injective e] at ht'
    exact hs (by rw [SymplecticPilot.mem_planeCoords] at ht' ⊢; rwa [← ht])
  rcases s with i | i
  · exact ⟨plusIndexEquiv n (.inr i), hnot _ rfl, 1, one_ne_zero,
      (isHypCoord_coordinateQuadPlus (K := K) i).dual_left⟩
  · exact ⟨plusIndexEquiv n (.inl i), hnot _ rfl, 1, one_ne_zero,
      (isHypCoord_coordinateQuadPlus (K := K) i).dual_right⟩

end Fix

end CFSG.SeitzReduction.OmegaPilot
