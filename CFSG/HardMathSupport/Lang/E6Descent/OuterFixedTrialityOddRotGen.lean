module

public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixedTrialityOddEllFrame

public noncomputable section

namespace CFSG.HardMathSupport.Lang.E6Descent

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.GH74.GLS.Stage2.Bender.Thm1 CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix MatrixGroups

set_option linter.unusedSectionVars false

section OrbitElements

variable {L : Type} [Field L]

abbrev rotOrbit : Fin TwistTag.D4.foldedTag.rank := ⟨0, by decide⟩

theorem rotOrbit_mem {i : Fin TwistTag.D4.tag.rank} (hi : i = 0 ∨ i = 1 ∨ i = 3) :
    i ∈ TwistTag.D4.orbit rotOrbit := by
  rcases hi with rfl | rfl | rfl <;> decide

@[expose] def xO (c : L) : ModGL TwistTag.D4.tag L :=
  xUnit TwistTag.D4.tag L 0 c * xUnit TwistTag.D4.tag L 1 c * xUnit TwistTag.D4.tag L 3 c

@[expose] def yO (c : L) : ModGL TwistTag.D4.tag L :=
  yUnit TwistTag.D4.tag L 0 c * yUnit TwistTag.D4.tag L 1 c * yUnit TwistTag.D4.tag L 3 c

theorem commute_x_outer {i j : Fin TwistTag.D4.tag.rank} (hi : i = 0 ∨ i = 1 ∨ i = 3)
    (hj : j = 0 ∨ j = 1 ∨ j = 3) (c d : L) :
    Commute (xUnit TwistTag.D4.tag L i c) (xUnit TwistTag.D4.tag L j d) :=
  commute_xUnit_xUnit (t := TwistTag.D4) L (rotOrbit_mem hi) (rotOrbit_mem hj) c d

theorem commute_y_outer {i j : Fin TwistTag.D4.tag.rank} (hi : i = 0 ∨ i = 1 ∨ i = 3)
    (hj : j = 0 ∨ j = 1 ∨ j = 3) (hij : i ≠ j) (c d : L) :
    Commute (yUnit TwistTag.D4.tag L i c) (yUnit TwistTag.D4.tag L j d) :=
  commute_yUnit_yUnit (t := TwistTag.D4) L (rotOrbit_mem hi) (rotOrbit_mem hj) hij c d

theorem xO_zero : xO (0 : L) = 1 := by
  simp [xO, xUnit_zero]

theorem yO_zero : yO (0 : L) = 1 := by
  simp [yO, yUnit_zero]

theorem prod3_mul_prod3 {M : Type*} [Group M] (a b c a' b' c' : M) (h1 : Commute c a')
    (h2 : Commute b a') (h3 : Commute c b') :
    (a * b * c) * (a' * b' * c') = (a * a') * (b * b') * (c * c') := by
  calc (a * b * c) * (a' * b' * c') = a * b * (c * a') * b' * c' := by group
    _ = a * b * (a' * c) * b' * c' := by rw [h1.eq]
    _ = a * (b * a') * c * b' * c' := by group
    _ = a * (a' * b) * c * b' * c' := by rw [h2.eq]
    _ = a * a' * b * (c * b') * c' := by group
    _ = a * a' * b * (b' * c) * c' := by rw [h3.eq]
    _ = (a * a') * (b * b') * (c * c') := by group

theorem xO_add (c d : L) : xO (c + d) = xO c * xO d := by
  have h1 := commute_x_outer (L := L) (i := 3) (j := 0) (by simp) (by simp) c d
  have h2 := commute_x_outer (L := L) (i := 1) (j := 0) (by simp) (by simp) c d
  have h3 := commute_x_outer (L := L) (i := 3) (j := 1) (by simp) (by simp) c d
  simp only [xO, xUnit_add]
  exact (prod3_mul_prod3 _ _ _ _ _ _ h1 h2 h3).symm

theorem yO_add (c d : L) : yO (c + d) = yO c * yO d := by
  have h1 := commute_y_outer (L := L) (i := 3) (j := 0) (by simp) (by simp) (by decide) c d
  have h2 := commute_y_outer (L := L) (i := 1) (j := 0) (by simp) (by simp) (by decide) c d
  have h3 := commute_y_outer (L := L) (i := 3) (j := 1) (by simp) (by simp) (by decide) c d
  simp only [yO, yUnit_add]
  exact (prod3_mul_prod3 _ _ _ _ _ _ h1 h2 h3).symm

theorem xO_inv (c : L) : (xO c)⁻¹ = xO (-c) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← xO_add, add_neg_cancel, xO_zero]

theorem yO_inv (c : L) : (yO c)⁻¹ = yO (-c) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← yO_add, add_neg_cancel, yO_zero]

theorem xO_mem_adjointGroup (c : L) : xO c ∈ adjointGroup TwistTag.D4.tag L :=
  mul_mem (mul_mem (xUnit_mem_adjointGroup _ _) (xUnit_mem_adjointGroup _ _))
    (xUnit_mem_adjointGroup _ _)

theorem yO_mem_adjointGroup (c : L) : yO c ∈ adjointGroup TwistTag.D4.tag L :=
  mul_mem (mul_mem (yUnit_mem_adjointGroup _ _) (yUnit_mem_adjointGroup _ _))
    (yUnit_mem_adjointGroup _ _)

theorem diagramMap_conj_xO (c : L) :
    diagramMap TwistTag.D4 L * xO c * (diagramMap TwistTag.D4 L)⁻¹ = xO c := by
  have h : ∀ i, diagramMap TwistTag.D4 L * xUnit TwistTag.D4.tag L i c *
      (diagramMap TwistTag.D4 L)⁻¹ = xUnit TwistTag.D4.tag L (TwistTag.D4.perm i) c :=
    fun i => diagramMap_mul_xUnit_mul_inv (t := TwistTag.D4) (K := L) i c
  have e : diagramMap TwistTag.D4 L * xO c * (diagramMap TwistTag.D4 L)⁻¹ =
      (diagramMap TwistTag.D4 L * xUnit TwistTag.D4.tag L 0 c * (diagramMap TwistTag.D4 L)⁻¹) *
        (diagramMap TwistTag.D4 L * xUnit TwistTag.D4.tag L 1 c * (diagramMap TwistTag.D4 L)⁻¹) *
        (diagramMap TwistTag.D4 L * xUnit TwistTag.D4.tag L 3 c * (diagramMap TwistTag.D4 L)⁻¹) := by
    unfold xO; group
  rw [e, h, h, h]
  have p0 : TwistTag.D4.perm (0 : Fin TwistTag.D4.tag.rank) = 1 := by decide
  have p1 : TwistTag.D4.perm (1 : Fin TwistTag.D4.tag.rank) = 3 := by decide
  have p3 : TwistTag.D4.perm (3 : Fin TwistTag.D4.tag.rank) = 0 := by decide
  rw [p0, p1, p3]
  have h01 := commute_x_outer (L := L) (i := 0) (j := 1) (by simp) (by simp) c c
  have h03 := commute_x_outer (L := L) (i := 0) (j := 3) (by simp) (by simp) c c
  unfold xO
  calc xUnit TwistTag.D4.tag L 1 c * xUnit TwistTag.D4.tag L 3 c * xUnit TwistTag.D4.tag L 0 c
      = xUnit TwistTag.D4.tag L 1 c * (xUnit TwistTag.D4.tag L 3 c * xUnit TwistTag.D4.tag L 0 c) := by
        group
    _ = xUnit TwistTag.D4.tag L 1 c * (xUnit TwistTag.D4.tag L 0 c * xUnit TwistTag.D4.tag L 3 c) := by
        rw [h03.eq]
    _ = (xUnit TwistTag.D4.tag L 1 c * xUnit TwistTag.D4.tag L 0 c) * xUnit TwistTag.D4.tag L 3 c := by
        group
    _ = (xUnit TwistTag.D4.tag L 0 c * xUnit TwistTag.D4.tag L 1 c) * xUnit TwistTag.D4.tag L 3 c := by
        rw [h01.eq]

theorem diagramMap_conj_yO (c : L) :
    diagramMap TwistTag.D4 L * yO c * (diagramMap TwistTag.D4 L)⁻¹ = yO c := by
  have h : ∀ i, diagramMap TwistTag.D4 L * yUnit TwistTag.D4.tag L i c *
      (diagramMap TwistTag.D4 L)⁻¹ = yUnit TwistTag.D4.tag L (TwistTag.D4.perm i) c :=
    fun i => diagramMap_mul_yUnit_mul_inv (t := TwistTag.D4) (K := L) i c
  have e : diagramMap TwistTag.D4 L * yO c * (diagramMap TwistTag.D4 L)⁻¹ =
      (diagramMap TwistTag.D4 L * yUnit TwistTag.D4.tag L 0 c * (diagramMap TwistTag.D4 L)⁻¹) *
        (diagramMap TwistTag.D4 L * yUnit TwistTag.D4.tag L 1 c * (diagramMap TwistTag.D4 L)⁻¹) *
        (diagramMap TwistTag.D4 L * yUnit TwistTag.D4.tag L 3 c * (diagramMap TwistTag.D4 L)⁻¹) := by
    unfold yO; group
  rw [e, h, h, h]
  have p0 : TwistTag.D4.perm (0 : Fin TwistTag.D4.tag.rank) = 1 := by decide
  have p1 : TwistTag.D4.perm (1 : Fin TwistTag.D4.tag.rank) = 3 := by decide
  have p3 : TwistTag.D4.perm (3 : Fin TwistTag.D4.tag.rank) = 0 := by decide
  rw [p0, p1, p3]
  have h01 := commute_y_outer (L := L) (i := 0) (j := 1) (by simp) (by simp) (by decide) c c
  have h03 := commute_y_outer (L := L) (i := 0) (j := 3) (by simp) (by simp) (by decide) c c
  unfold yO
  calc yUnit TwistTag.D4.tag L 1 c * yUnit TwistTag.D4.tag L 3 c * yUnit TwistTag.D4.tag L 0 c
      = yUnit TwistTag.D4.tag L 1 c * (yUnit TwistTag.D4.tag L 3 c * yUnit TwistTag.D4.tag L 0 c) := by
        group
    _ = yUnit TwistTag.D4.tag L 1 c * (yUnit TwistTag.D4.tag L 0 c * yUnit TwistTag.D4.tag L 3 c) := by
        rw [h03.eq]
    _ = (yUnit TwistTag.D4.tag L 1 c * yUnit TwistTag.D4.tag L 0 c) * yUnit TwistTag.D4.tag L 3 c := by
        group
    _ = (yUnit TwistTag.D4.tag L 0 c * yUnit TwistTag.D4.tag L 1 c) * yUnit TwistTag.D4.tag L 3 c := by
        rw [h01.eq]

theorem rootDiagUnit_conj_xO (a : Fin TwistTag.D4.tag.rank → Lˣ) (lam : Lˣ)
    (h0 : a 0 = lam) (h1 : a 1 = lam) (h3 : a 3 = lam) (c : L) :
    rootDiagUnit TwistTag.D4.tag a * xO c * (rootDiagUnit TwistTag.D4.tag a)⁻¹ =
      xO ((lam : L) * c) := by
  have h := fun i c => (root_diagonal_conjugation TwistTag.D4.tag L a).1 i c
  have e : rootDiagUnit TwistTag.D4.tag a * xO c * (rootDiagUnit TwistTag.D4.tag a)⁻¹ =
      (rootDiagUnit TwistTag.D4.tag a * xUnit TwistTag.D4.tag L 0 c *
          (rootDiagUnit TwistTag.D4.tag a)⁻¹) *
        (rootDiagUnit TwistTag.D4.tag a * xUnit TwistTag.D4.tag L 1 c *
          (rootDiagUnit TwistTag.D4.tag a)⁻¹) *
        (rootDiagUnit TwistTag.D4.tag a * xUnit TwistTag.D4.tag L 3 c *
          (rootDiagUnit TwistTag.D4.tag a)⁻¹) := by
    unfold xO; group
  rw [e, h, h, h, h0, h1, h3]
  rfl

theorem rootDiagUnit_conj_yO (a : Fin TwistTag.D4.tag.rank → Lˣ) (lam : Lˣ)
    (h0 : a 0 = lam) (h1 : a 1 = lam) (h3 : a 3 = lam) (c : L) :
    rootDiagUnit TwistTag.D4.tag a * yO c * (rootDiagUnit TwistTag.D4.tag a)⁻¹ =
      yO (((lam⁻¹ : Lˣ) : L) * c) := by
  have h := fun i c => (root_diagonal_conjugation TwistTag.D4.tag L a).2.1 i c
  have e : rootDiagUnit TwistTag.D4.tag a * yO c * (rootDiagUnit TwistTag.D4.tag a)⁻¹ =
      (rootDiagUnit TwistTag.D4.tag a * yUnit TwistTag.D4.tag L 0 c *
          (rootDiagUnit TwistTag.D4.tag a)⁻¹) *
        (rootDiagUnit TwistTag.D4.tag a * yUnit TwistTag.D4.tag L 1 c *
          (rootDiagUnit TwistTag.D4.tag a)⁻¹) *
        (rootDiagUnit TwistTag.D4.tag a * yUnit TwistTag.D4.tag L 3 c *
          (rootDiagUnit TwistTag.D4.tag a)⁻¹) := by
    unfold yO; group
  rw [e, h, h, h, h0, h1, h3]
  rfl

theorem rotElt_eq' (b : Lˣ) :
    rotElt b = rootDiagUnit TwistTag.D4.tag (tup1 b) * (diagramMap TwistTag.D4 L)⁻¹ := rfl

theorem rotElt_mul_xO (b : Lˣ) (c : L) : rotElt b * xO c = xO c * rotElt b := by
  have h := rootDiagUnit_conj_xO (tup1 b) 1 rfl rfl rfl c
  have hP := diagramMap_conj_xO (L := L) c
  rw [Units.val_one, one_mul] at h
  have hd : rootDiagUnit TwistTag.D4.tag (tup1 b) * xO c = xO c * rootDiagUnit TwistTag.D4.tag (tup1 b) := by
    rw [← mul_inv_eq_iff_eq_mul]; exact h
  have hPi : (diagramMap TwistTag.D4 L)⁻¹ * xO c = xO c * (diagramMap TwistTag.D4 L)⁻¹ := by
    have : (diagramMap TwistTag.D4 L)⁻¹ * (diagramMap TwistTag.D4 L * xO c *
        (diagramMap TwistTag.D4 L)⁻¹) = (diagramMap TwistTag.D4 L)⁻¹ * xO c := by rw [hP]
    rw [← this]; group
  rw [rotElt_eq']
  calc rootDiagUnit TwistTag.D4.tag (tup1 b) * (diagramMap TwistTag.D4 L)⁻¹ * xO c
      = rootDiagUnit TwistTag.D4.tag (tup1 b) * ((diagramMap TwistTag.D4 L)⁻¹ * xO c) := by group
    _ = rootDiagUnit TwistTag.D4.tag (tup1 b) * (xO c * (diagramMap TwistTag.D4 L)⁻¹) := by rw [hPi]
    _ = (rootDiagUnit TwistTag.D4.tag (tup1 b) * xO c) * (diagramMap TwistTag.D4 L)⁻¹ := by group
    _ = xO c * (rootDiagUnit TwistTag.D4.tag (tup1 b) * (diagramMap TwistTag.D4 L)⁻¹) := by
        rw [hd]; group

theorem rotElt_mul_yO (b : Lˣ) (c : L) : rotElt b * yO c = yO c * rotElt b := by
  have h := rootDiagUnit_conj_yO (tup1 b) 1 rfl rfl rfl c
  have hP := diagramMap_conj_yO (L := L) c
  rw [inv_one, Units.val_one, one_mul] at h
  have hd : rootDiagUnit TwistTag.D4.tag (tup1 b) * yO c = yO c * rootDiagUnit TwistTag.D4.tag (tup1 b) := by
    rw [← mul_inv_eq_iff_eq_mul]; exact h
  have hPi : (diagramMap TwistTag.D4 L)⁻¹ * yO c = yO c * (diagramMap TwistTag.D4 L)⁻¹ := by
    have : (diagramMap TwistTag.D4 L)⁻¹ * (diagramMap TwistTag.D4 L * yO c *
        (diagramMap TwistTag.D4 L)⁻¹) = (diagramMap TwistTag.D4 L)⁻¹ * yO c := by rw [hP]
    rw [← this]; group
  rw [rotElt_eq']
  calc rootDiagUnit TwistTag.D4.tag (tup1 b) * (diagramMap TwistTag.D4 L)⁻¹ * yO c
      = rootDiagUnit TwistTag.D4.tag (tup1 b) * ((diagramMap TwistTag.D4 L)⁻¹ * yO c) := by group
    _ = rootDiagUnit TwistTag.D4.tag (tup1 b) * (yO c * (diagramMap TwistTag.D4 L)⁻¹) := by rw [hPi]
    _ = (rootDiagUnit TwistTag.D4.tag (tup1 b) * yO c) * (diagramMap TwistTag.D4 L)⁻¹ := by group
    _ = yO c * (rootDiagUnit TwistTag.D4.tag (tup1 b) * (diagramMap TwistTag.D4 L)⁻¹) := by
        rw [hd]; group

theorem xO_mem_graphCentralizer (b : Lˣ) (c : L) :
    xO c ∈ graphCentralizer TwistTag.D4.tag L (rotElt b) :=
  Subgroup.mem_inf.2 ⟨xO_mem_adjointGroup c,
    Subgroup.mem_centralizer_singleton_iff.2 (rotElt_mul_xO b c).symm⟩

theorem yO_mem_graphCentralizer (b : Lˣ) (c : L) :
    yO c ∈ graphCentralizer TwistTag.D4.tag L (rotElt b) :=
  Subgroup.mem_inf.2 ⟨yO_mem_adjointGroup c,
    Subgroup.mem_centralizer_singleton_iff.2 (rotElt_mul_yO b c).symm⟩

theorem xO_rot (c : L) :
    xUnit TwistTag.D4.tag L 1 c * xUnit TwistTag.D4.tag L 3 c * xUnit TwistTag.D4.tag L 0 c =
      xO c := by
  have h01 := commute_x_outer (L := L) (i := 0) (j := 1) (by simp) (by simp) c c
  have h03 := commute_x_outer (L := L) (i := 0) (j := 3) (by simp) (by simp) c c
  unfold xO
  calc xUnit TwistTag.D4.tag L 1 c * xUnit TwistTag.D4.tag L 3 c * xUnit TwistTag.D4.tag L 0 c
      = xUnit TwistTag.D4.tag L 1 c * (xUnit TwistTag.D4.tag L 3 c * xUnit TwistTag.D4.tag L 0 c) := by
        group
    _ = xUnit TwistTag.D4.tag L 1 c * (xUnit TwistTag.D4.tag L 0 c * xUnit TwistTag.D4.tag L 3 c) := by
        rw [h03.eq]
    _ = (xUnit TwistTag.D4.tag L 1 c * xUnit TwistTag.D4.tag L 0 c) * xUnit TwistTag.D4.tag L 3 c := by
        group
    _ = (xUnit TwistTag.D4.tag L 0 c * xUnit TwistTag.D4.tag L 1 c) * xUnit TwistTag.D4.tag L 3 c := by
        rw [h01.eq]

theorem yO_rot (c : L) :
    yUnit TwistTag.D4.tag L 1 c * yUnit TwistTag.D4.tag L 3 c * yUnit TwistTag.D4.tag L 0 c =
      yO c := by
  have h01 := commute_y_outer (L := L) (i := 0) (j := 1) (by simp) (by simp) (by decide) c c
  have h03 := commute_y_outer (L := L) (i := 0) (j := 3) (by simp) (by simp) (by decide) c c
  unfold yO
  calc yUnit TwistTag.D4.tag L 1 c * yUnit TwistTag.D4.tag L 3 c * yUnit TwistTag.D4.tag L 0 c
      = yUnit TwistTag.D4.tag L 1 c * (yUnit TwistTag.D4.tag L 3 c * yUnit TwistTag.D4.tag L 0 c) := by
        group
    _ = yUnit TwistTag.D4.tag L 1 c * (yUnit TwistTag.D4.tag L 0 c * yUnit TwistTag.D4.tag L 3 c) := by
        rw [h03.eq]
    _ = (yUnit TwistTag.D4.tag L 1 c * yUnit TwistTag.D4.tag L 0 c) * yUnit TwistTag.D4.tag L 3 c := by
        group
    _ = (yUnit TwistTag.D4.tag L 0 c * yUnit TwistTag.D4.tag L 1 c) * yUnit TwistTag.D4.tag L 3 c := by
        rw [h01.eq]

theorem twistHom_xO (Fr : L →+* L) (c : L) :
    twistHom TwistTag.D4 L Fr (xO c) = xO (Fr c) := by
  have p0 : TwistTag.D4.perm (0 : Fin TwistTag.D4.tag.rank) = 1 := by decide
  have p1 : TwistTag.D4.perm (1 : Fin TwistTag.D4.tag.rank) = 3 := by decide
  have p3 : TwistTag.D4.perm (3 : Fin TwistTag.D4.tag.rank) = 0 := by decide
  unfold xO
  rw [map_mul, map_mul, twistHom_xUnit, twistHom_xUnit, twistHom_xUnit, p0, p1, p3]
  exact xO_rot (Fr c)

theorem twistHom_yO (Fr : L →+* L) (c : L) :
    twistHom TwistTag.D4 L Fr (yO c) = yO (Fr c) := by
  have p0 : TwistTag.D4.perm (0 : Fin TwistTag.D4.tag.rank) = 1 := by decide
  have p1 : TwistTag.D4.perm (1 : Fin TwistTag.D4.tag.rank) = 3 := by decide
  have p3 : TwistTag.D4.perm (3 : Fin TwistTag.D4.tag.rank) = 0 := by decide
  unfold yO
  rw [map_mul, map_mul, twistHom_yUnit, twistHom_yUnit, twistHom_yUnit, p0, p1, p3]
  exact yO_rot (Fr c)

theorem yUnit_inj {i : Fin TwistTag.D4.tag.rank} {c d : L}
    (h : yUnit TwistTag.D4.tag L i c = yUnit TwistTag.D4.tag L i d) : c = d := by
  rw [← pinnedX_neg_single, ← pinnedX_neg_single] at h
  exact pinnedX_injective _ _ _ h

theorem z0_conj_xUnit (i : Fin TwistTag.D4.tag.rank) :
    ∃ μ : Lˣ, ∀ c : L, trialityOpposition L * xUnit TwistTag.D4.tag L i c *
      (trialityOpposition L)⁻¹ = yUnit TwistTag.D4.tag L i ((μ : L) * c) := by
  obtain ⟨μ, hμ⟩ := conj_pinnedX_of_smul_eq_neg (τ := TwistTag.D4.tag) (L := L)
    trialityOpposition_mem_monomialSubgroup weylQuotientHom_trialityOpposition_smul
    (γ := Pi.single i 1) (isRoot_single _ i)
  refine ⟨μ, fun c => ?_⟩
  have := hμ c
  rwa [pinnedX_single, pinnedX_neg_single] at this

theorem z0_conj_xO : ∃ μ : Lˣ, ∀ c : L, trialityOpposition L * xO c *
    (trialityOpposition L)⁻¹ = yO ((μ : L) * c) := by
  obtain ⟨μ0, h0⟩ := z0_conj_xUnit (L := L) 0
  obtain ⟨μ1, h1⟩ := z0_conj_xUnit (L := L) 1
  obtain ⟨μ3, h3⟩ := z0_conj_xUnit (L := L) 3
  have hcomm := diagramMap_comm_trialityOpposition (L := L)
  have key : ∀ (i j : Fin TwistTag.D4.tag.rank) (μi μj : Lˣ),
      TwistTag.D4.perm i = j →
      (∀ c : L, trialityOpposition L * xUnit TwistTag.D4.tag L i c * (trialityOpposition L)⁻¹ =
        yUnit TwistTag.D4.tag L i ((μi : L) * c)) →
      (∀ c : L, trialityOpposition L * xUnit TwistTag.D4.tag L j c * (trialityOpposition L)⁻¹ =
        yUnit TwistTag.D4.tag L j ((μj : L) * c)) → μi = μj := by
    intro i j μi μj hij hi hj
    have e1 : diagramMap TwistTag.D4 L * (trialityOpposition L * xUnit TwistTag.D4.tag L i 1 *
        (trialityOpposition L)⁻¹) * (diagramMap TwistTag.D4 L)⁻¹ =
        trialityOpposition L * xUnit TwistTag.D4.tag L j 1 * (trialityOpposition L)⁻¹ := by
      rw [← hij, ← diagramMap_mul_xUnit_mul_inv (t := TwistTag.D4) (K := L) i 1]
      have hc2 : (trialityOpposition L)⁻¹ * (diagramMap TwistTag.D4 L)⁻¹ =
          (diagramMap TwistTag.D4 L)⁻¹ * (trialityOpposition L)⁻¹ := by
        rw [← mul_inv_rev, ← mul_inv_rev, hcomm]
      calc diagramMap TwistTag.D4 L * (trialityOpposition L * xUnit TwistTag.D4.tag L i 1 *
            (trialityOpposition L)⁻¹) * (diagramMap TwistTag.D4 L)⁻¹
          = (diagramMap TwistTag.D4 L * trialityOpposition L) * xUnit TwistTag.D4.tag L i 1 *
            ((trialityOpposition L)⁻¹ * (diagramMap TwistTag.D4 L)⁻¹) := by group
        _ = (trialityOpposition L * diagramMap TwistTag.D4 L) * xUnit TwistTag.D4.tag L i 1 *
            ((diagramMap TwistTag.D4 L)⁻¹ * (trialityOpposition L)⁻¹) := by rw [hcomm, hc2]
        _ = _ := by group
    rw [hi, hj] at e1
    have e2 := diagramMap_mul_yUnit_mul_inv (t := TwistTag.D4) (K := L) i ((μi : L) * 1)
    rw [hij] at e2
    rw [e2] at e1
    have := yUnit_inj e1
    exact Units.ext (by simpa using this)
  have e01 : μ0 = μ1 := key 0 1 μ0 μ1 (by decide) h0 h1
  have e13 : μ1 = μ3 := key 1 3 μ1 μ3 (by decide) h1 h3
  refine ⟨μ0, fun c => ?_⟩
  unfold xO yO
  have : trialityOpposition L * (xUnit TwistTag.D4.tag L 0 c * xUnit TwistTag.D4.tag L 1 c *
      xUnit TwistTag.D4.tag L 3 c) * (trialityOpposition L)⁻¹ =
      (trialityOpposition L * xUnit TwistTag.D4.tag L 0 c * (trialityOpposition L)⁻¹) *
      (trialityOpposition L * xUnit TwistTag.D4.tag L 1 c * (trialityOpposition L)⁻¹) *
      (trialityOpposition L * xUnit TwistTag.D4.tag L 3 c * (trialityOpposition L)⁻¹) := by group
  rw [this, h0, h1, h3, ← e01, ← e13, ← e01]

theorem z0_sq : trialityOpposition L * trialityOpposition L = 1 := by
  have := trialityOpposition_sq (K := L)
  rwa [pow_two] at this

theorem z0_conj_yO : ∃ ν : Lˣ, ∀ c : L, trialityOpposition L * yO c *
    (trialityOpposition L)⁻¹ = xO ((ν : L) * c) := by
  obtain ⟨μ, hμ⟩ := z0_conj_xO (L := L)
  refine ⟨μ⁻¹, fun c => ?_⟩
  have h := hμ (((μ⁻¹ : Lˣ) : L) * c)
  have hz : (trialityOpposition L)⁻¹ = trialityOpposition L :=
    inv_eq_of_mul_eq_one_right z0_sq
  have e : yO ((μ : L) * (((μ⁻¹ : Lˣ) : L) * c)) = yO c := by
    congr 1
    rw [← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
  rw [e] at h
  calc trialityOpposition L * yO c * (trialityOpposition L)⁻¹
      = trialityOpposition L * (trialityOpposition L * xO (((μ⁻¹ : Lˣ) : L) * c) *
        (trialityOpposition L)⁻¹) * (trialityOpposition L)⁻¹ := by rw [h]
    _ = (trialityOpposition L * trialityOpposition L) * xO (((μ⁻¹ : Lˣ) : L) * c) *
        ((trialityOpposition L)⁻¹ * (trialityOpposition L)⁻¹) := by group
    _ = xO (((μ⁻¹ : Lˣ) : L) * c) := by
        rw [z0_sq, hz, z0_sq]; group

end OrbitElements

section TorusPart

variable (L : Type) [Field L] [IsAlgClosed L]

abbrev rotS : Subgroup (ModGL TwistTag.D4.tag L) :=
  torusGroup TwistTag.D4.tag L ⊓ graphCentralizer TwistTag.D4.tag L (diagramMap TwistTag.D4 L)

variable {L}

theorem rotS_le_graphCentralizer (b : Lˣ) :
    rotS L ≤ graphCentralizer TwistTag.D4.tag L (rotElt b) := by
  intro g hg
  obtain ⟨hgT, hgZ⟩ := Subgroup.mem_inf.1 hg
  obtain ⟨hgG, hgc⟩ := Subgroup.mem_inf.1 hgZ
  have hP : diagramMap TwistTag.D4 L * g = g * diagramMap TwistTag.D4 L :=
    (Subgroup.mem_centralizer_singleton_iff.1 hgc).symm
  have hPc : Commute (diagramMap TwistTag.D4 L)⁻¹ g := (show Commute _ g from hP).inv_left
  refine Subgroup.mem_inf.2 ⟨hgG, Subgroup.mem_centralizer_singleton_iff.2 (Eq.symm ?_)⟩
  have hd := torusGroup_comm hgT (rootDiagUnit_mem_torusGroup (τ := TwistTag.D4.tag) (tup1 b))
  rw [rotElt_eq']
  calc rootDiagUnit TwistTag.D4.tag (tup1 b) * (diagramMap TwistTag.D4 L)⁻¹ * g
      = rootDiagUnit TwistTag.D4.tag (tup1 b) * ((diagramMap TwistTag.D4 L)⁻¹ * g) := by group
    _ = rootDiagUnit TwistTag.D4.tag (tup1 b) * (g * (diagramMap TwistTag.D4 L)⁻¹) := by
        rw [hPc.eq]
    _ = (rootDiagUnit TwistTag.D4.tag (tup1 b) * g) * (diagramMap TwistTag.D4 L)⁻¹ := by group
    _ = (g * rootDiagUnit TwistTag.D4.tag (tup1 b)) * (diagramMap TwistTag.D4 L)⁻¹ := by
        rw [← hd]
    _ = g * (rootDiagUnit TwistTag.D4.tag (tup1 b) * (diagramMap TwistTag.D4 L)⁻¹) := by group

theorem exists_lam_of_mem_rotS {ξ : ModGL TwistTag.D4.tag L} (hξ : ξ ∈ rotS L) :
    ∃ lam : Lˣ, ∀ c : L, ξ * xO c * ξ⁻¹ = xO ((lam : L) * c) ∧
      ξ * yO c * ξ⁻¹ = yO (((lam⁻¹ : Lˣ) : L) * c) := by
  obtain ⟨hξT, hξZ⟩ := Subgroup.mem_inf.1 hξ
  obtain ⟨-, hξc⟩ := Subgroup.mem_inf.1 hξZ
  have hP : diagramMap TwistTag.D4 L * ξ = ξ * diagramMap TwistTag.D4 L :=
    (Subgroup.mem_centralizer_singleton_iff.1 hξc).symm
  obtain ⟨ν, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hξT
  rw [diagramMap_mul_rootDiagUnit] at hP
  have h2 := rootDiagUnit_injective (mul_right_cancel hP)
  have hν : ∀ i, ν (TwistTag.D4.perm.symm i) = ν i := fun i => congrFun h2 i
  have h30 : ν 3 = ν 0 := by
    have := hν 0
    have e : TwistTag.D4.perm.symm (0 : Fin TwistTag.D4.tag.rank) = 3 := by decide
    rwa [e] at this
  have h01 : ν 0 = ν 1 := by
    have := hν 1
    have e : TwistTag.D4.perm.symm (1 : Fin TwistTag.D4.tag.rank) = 0 := by decide
    rwa [e] at this
  refine ⟨ν 0, fun c => ⟨rootDiagUnit_conj_xO ν (ν 0) rfl h01.symm h30 c,
    rootDiagUnit_conj_yO ν (ν 0) rfl h01.symm h30 c⟩⟩

end TorusPart

section Core

variable {L : Type} [Field L] [IsAlgClosed L]

theorem mem_rotS_of_mem_graphCentralizer {b : Lˣ} {g : ModGL TwistTag.D4.tag L}
    (hgT : g ∈ torusGroup TwistTag.D4.tag L)
    (hg : g ∈ graphCentralizer TwistTag.D4.tag L (rotElt b)) : g ∈ rotS L := by
  obtain ⟨hgG, hgc⟩ := Subgroup.mem_inf.1 hg
  have hA : g * rotElt b = rotElt b * g := Subgroup.mem_centralizer_singleton_iff.1 hgc
  have hd := torusGroup_comm hgT (rootDiagUnit_mem_torusGroup (τ := TwistTag.D4.tag) (tup1 b))
  rw [rotElt_eq'] at hA
  have h1 : g * (diagramMap TwistTag.D4 L)⁻¹ = (diagramMap TwistTag.D4 L)⁻¹ * g := by
    have h2 : rootDiagUnit TwistTag.D4.tag (tup1 b) * (g * (diagramMap TwistTag.D4 L)⁻¹) =
        rootDiagUnit TwistTag.D4.tag (tup1 b) * ((diagramMap TwistTag.D4 L)⁻¹ * g) := by
      calc rootDiagUnit TwistTag.D4.tag (tup1 b) * (g * (diagramMap TwistTag.D4 L)⁻¹)
          = (rootDiagUnit TwistTag.D4.tag (tup1 b) * g) * (diagramMap TwistTag.D4 L)⁻¹ := by group
        _ = (g * rootDiagUnit TwistTag.D4.tag (tup1 b)) * (diagramMap TwistTag.D4 L)⁻¹ := by
            rw [hd]
        _ = g * (rootDiagUnit TwistTag.D4.tag (tup1 b) * (diagramMap TwistTag.D4 L)⁻¹) := by group
        _ = rootDiagUnit TwistTag.D4.tag (tup1 b) * (diagramMap TwistTag.D4 L)⁻¹ * g := hA
        _ = _ := by group
    exact mul_left_cancel h2
  have hPc : Commute (diagramMap TwistTag.D4 L) g :=
    ((show Commute g (diagramMap TwistTag.D4 L)⁻¹ from h1).inv_right).symm
  exact Subgroup.mem_inf.2 ⟨hgT, Subgroup.mem_inf.2 ⟨hgG,
    Subgroup.mem_centralizer_singleton_iff.2 hPc.symm.eq⟩⟩

structure RotFrame (F : ModGL TwistTag.D4.tag L →* ModGL TwistTag.D4.tag L) (e : ℤ) : Prop where
  frame : EllFrame F e
  adjoint : ∀ g ∈ adjointGroup TwistTag.D4.tag L, F g ∈ adjointGroup TwistTag.D4.tag L
  frob_xO : ∀ c : L, ∃ c' : L, F (xO c) = xO c' ∨ F (xO c) = yO c'
  frob_yO : ∀ c : L, ∃ c' : L, F (yO c) = yO c' ∨ F (yO c) = xO c'
  weyl : ∀ (M : D4Mat) (ζ : ModGL TwistTag.D4.tag L) (hζ : ζ ∈ monomialSubgroup TwistTag.D4.tag L),
    M * d4PermMat = d4PermMat * M →
    (∀ x, weylQuotientHom TwistTag.D4.tag L ⟨ζ, hζ⟩ • x = M *ᵥ x) →
    ∃ hFζ : F ζ ∈ monomialSubgroup TwistTag.D4.tag L,
      ∀ x, weylQuotientHom TwistTag.D4.tag L ⟨F ζ, hFζ⟩ • x = M *ᵥ x

variable {F : ModGL TwistTag.D4.tag L →* ModGL TwistTag.D4.tag L} {e : ℤ}

theorem RotFrame.mem_graphCentralizer (hF : RotFrame F e) {b : Lˣ} (hbe : b ^ e = b)
    {g : ModGL TwistTag.D4.tag L} (hg : g ∈ graphCentralizer TwistTag.D4.tag L (rotElt b)) :
    F g ∈ graphCentralizer TwistTag.D4.tag L (rotElt b) := by
  obtain ⟨hgG, hgc⟩ := Subgroup.mem_inf.1 hg
  have hA : g * rotElt b = rotElt b * g := Subgroup.mem_centralizer_singleton_iff.1 hgc
  have hFA : F (rotElt b) = rotElt b := hF.frame.rotElt hbe
  refine Subgroup.mem_inf.2 ⟨hF.adjoint g hgG, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
  have := congrArg F hA
  rwa [map_mul, map_mul, hFA] at this

theorem RotFrame.exists_frob_eq (hF : RotFrame F e) {b : Lˣ} (hbe : b ^ e = b)
    {ζ : ModGL TwistTag.D4.tag L} (hζ : ζ ∈ graphCentralizer TwistTag.D4.tag L (rotElt b))
    (hm : ζ ∈ monomialSubgroup TwistTag.D4.tag L) {M : D4Mat}
    (hMP : M * d4PermMat = d4PermMat * M)
    (hMw : ∀ x, weylQuotientHom TwistTag.D4.tag L ⟨ζ, hm⟩ • x = M *ᵥ x) :
    ∃ ξ ∈ rotS L, F ζ = ζ * ξ := by
  obtain ⟨hFm, hFw⟩ := hF.weyl M ζ hm hMP hMw
  have hξm : ζ⁻¹ * F ζ ∈ monomialSubgroup TwistTag.D4.tag L :=
    mul_mem (inv_mem hm) hFm
  have hw : weylQuotientHom TwistTag.D4.tag L ⟨ζ⁻¹ * F ζ, hξm⟩ = 1 := by
    have e1 : (⟨ζ⁻¹ * F ζ, hξm⟩ : monomialSubgroup TwistTag.D4.tag L) =
        ⟨ζ, hm⟩⁻¹ * ⟨F ζ, hFm⟩ := rfl
    rw [e1, map_mul, map_inv]
    refine FaithfulSMul.eq_of_smul_eq_smul (α := Fin TwistTag.D4.tag.rank → ℤ) fun v => ?_
    rw [mul_smul, hFw, one_smul]
    have := hMw v
    rw [← this, inv_smul_smul]
  have hξT := mem_torus_of_weyl_eq_one hξm hw
  have hξZ : ζ⁻¹ * F ζ ∈ graphCentralizer TwistTag.D4.tag L (rotElt b) :=
    mul_mem (inv_mem hζ) (hF.mem_graphCentralizer hbe hζ)
  refine ⟨ζ⁻¹ * F ζ, mem_rotS_of_mem_graphCentralizer hξT hξZ, ?_⟩
  group

end Core

section WeylElement

variable {L : Type} [Field L]

theorem xO_eq_orbitX (c : L) :
    xO c = (orbitX TwistTag.D4 L (RingHom.id L) rotOrbit ⟨c, by simp [mem_orbitField]⟩ :
      ModGL TwistTag.D4.tag L) := by
  rw [coe_orbitX]
  have h1 : (TwistTag.D4.orbit rotOrbit).card = 3 := by decide
  have h2 : TwistTag.D4.orbitMin rotOrbit = 0 := by decide
  rw [h1, h2]
  have p1 : TwistTag.D4.perm (0 : Fin TwistTag.D4.tag.rank) = 1 := by decide
  have p2 : (TwistTag.D4.perm ^ 2) (0 : Fin TwistTag.D4.tag.rank) = 3 := by decide
  simp [List.range_succ, xO, p1, p2, mul_assoc]

theorem yO_eq_orbitY (c : L) :
    yO c = (orbitY TwistTag.D4 L (RingHom.id L) rotOrbit ⟨c, by simp [mem_orbitField]⟩ :
      ModGL TwistTag.D4.tag L) := by
  rw [coe_orbitY]
  have h1 : (TwistTag.D4.orbit rotOrbit).card = 3 := by decide
  have h2 : TwistTag.D4.orbitMin rotOrbit = 0 := by decide
  rw [h1, h2]
  have p1 : TwistTag.D4.perm (0 : Fin TwistTag.D4.tag.rank) = 1 := by decide
  have p2 : (TwistTag.D4.perm ^ 2) (0 : Fin TwistTag.D4.tag.rank) = 3 := by decide
  simp [List.range_succ, yO, p1, p2, mul_assoc]

theorem nO_eq_canonicalRep :
    xO (1 : L) * yO (-1) * xO 1 =
      canonicalRep (coxeterSystem TwistTag.D4.tag) L (TwistTag.D4.orbitReflection rotOrbit) := by
  rw [canonicalRep_orbitReflection_eq_orbitN (σ := RingHom.id L)]
  simp only [orbitN, Subgroup.coe_mul]
  rw [xO_eq_orbitX 1, yO_eq_orbitY (-1)]
  rfl

theorem nO_weyl :
    ∃ hm : xO (1 : L) * yO (-1) * xO 1 ∈ monomialSubgroup TwistTag.D4.tag L,
      ∀ x, weylQuotientHom TwistTag.D4.tag L ⟨_, hm⟩ • x = d4MatShort *ᵥ x := by
  have hm : xO (1 : L) * yO (-1) * xO 1 ∈ monomialSubgroup TwistTag.D4.tag L := by
    rw [nO_eq_canonicalRep]
    exact canonicalRep_mem_monomialSubgroup L _
  refine ⟨hm, fun x => ?_⟩
  have h : weylQuotientHom TwistTag.D4.tag L ⟨_, hm⟩ = TwistTag.D4.orbitReflection rotOrbit := by
    refine weylQuotientHom_eq ?_
    show MapsRootLines (xO (1 : L) * yO (-1) * xO 1) _
    rw [nO_eq_canonicalRep]
    exact mapsRootLines_canonicalRep _
  rw [h]
  exact d4_orbitReflection_zero_smul x

theorem d4_rot_conj_A :
    d4MatShort * (d4MatThreeA * (d4MatShort * d4MatThreeB)) = d4MatThreeA := by decide +kernel

theorem d4_rot_conj_B :
    d4MatShort * (d4MatThreeB * (d4MatShort * d4MatThreeA)) = d4MatThreeB := by decide +kernel

theorem d4_rotA_perm : d4MatThreeA * d4PermMat = d4PermMat * d4MatThreeA := by decide +kernel

theorem d4_rotB_perm : d4MatThreeB * d4PermMat = d4PermMat * d4MatThreeB := by decide +kernel

end WeylElement

section Assembly

variable {L : Type} [Field L] [IsAlgClosed L]

@[expose] def rotGen (ζ : ModGL TwistTag.D4.tag L) : Set (ModGL TwistTag.D4.tag L) :=
  (rotS L : Set (ModGL TwistTag.D4.tag L)) ∪ Set.range (xO (L := L)) ∪ Set.range (yO (L := L)) ∪
    Set.range (fun c : L => ζ * xO c * ζ⁻¹) ∪ Set.range (fun c : L => ζ * yO c * ζ⁻¹)

@[expose] def rotR (ζ : ModGL TwistTag.D4.tag L) : Subgroup (ModGL TwistTag.D4.tag L) :=
  Subgroup.closure (rotGen ζ)

variable {ζ : ModGL TwistTag.D4.tag L}

theorem rotGen_S {g : ModGL TwistTag.D4.tag L} (hg : g ∈ rotS L) : g ∈ rotGen ζ :=
  Or.inl (Or.inl (Or.inl (Or.inl hg)))

theorem rotGen_x (c : L) : xO c ∈ rotGen ζ := Or.inl (Or.inl (Or.inl (Or.inr ⟨c, rfl⟩)))

theorem rotGen_y (c : L) : yO c ∈ rotGen ζ := Or.inl (Or.inl (Or.inr ⟨c, rfl⟩))

theorem rotGen_xc (c : L) : ζ * xO c * ζ⁻¹ ∈ rotGen ζ := Or.inl (Or.inr ⟨c, rfl⟩)

theorem rotGen_yc (c : L) : ζ * yO c * ζ⁻¹ ∈ rotGen ζ := Or.inr ⟨c, rfl⟩

theorem rotR_le (b : Lˣ) (hζ : ζ ∈ graphCentralizer TwistTag.D4.tag L (rotElt b)) :
    rotR ζ ≤ graphCentralizer TwistTag.D4.tag L (rotElt b) := by
  rw [rotR, Subgroup.closure_le]
  intro g hg
  rcases hg with (((hg | ⟨c, rfl⟩) | ⟨c, rfl⟩) | ⟨c, rfl⟩) | ⟨c, rfl⟩
  · exact rotS_le_graphCentralizer b hg
  · exact xO_mem_graphCentralizer b c
  · exact yO_mem_graphCentralizer b c
  · exact mul_mem (mul_mem hζ (xO_mem_graphCentralizer b c)) (inv_mem hζ)
  · exact mul_mem (mul_mem hζ (yO_mem_graphCentralizer b c)) (inv_mem hζ)

variable {F : ModGL TwistTag.D4.tag L →* ModGL TwistTag.D4.tag L} {e : ℤ}

theorem RotFrame.rotS_stable (hF : RotFrame F e) {g : ModGL TwistTag.D4.tag L} (hg : g ∈ rotS L) :
    F g ∈ rotS L := by
  obtain ⟨hgT, hgZ⟩ := Subgroup.mem_inf.1 hg
  obtain ⟨hgG, hgc⟩ := Subgroup.mem_inf.1 hgZ
  have hP : g * diagramMap TwistTag.D4 L = diagramMap TwistTag.D4 L * g :=
    Subgroup.mem_centralizer_singleton_iff.1 hgc
  refine Subgroup.mem_inf.2 ⟨hF.frame.torus g hgT, Subgroup.mem_inf.2 ⟨hF.adjoint g hgG,
    Subgroup.mem_centralizer_singleton_iff.2 ?_⟩⟩
  have := congrArg F hP
  rwa [map_mul, map_mul, hF.frame.diagram] at this

theorem rotR_stable (hF : RotFrame F e) (hξ : ∃ ξ ∈ rotS L, F ζ = ζ * ξ) :
    ∀ g ∈ rotR ζ, F g ∈ rotR ζ := by
  obtain ⟨ξ, hξS, hFζ⟩ := hξ
  obtain ⟨lam, hlam⟩ := exists_lam_of_mem_rotS hξS
  have hle : rotR ζ ≤ (rotR ζ).comap F := by
    rw [rotR, Subgroup.closure_le]
    intro g hg
    rw [SetLike.mem_coe, Subgroup.mem_comap]
    have hgen : ∀ {h : ModGL TwistTag.D4.tag L}, h ∈ rotGen ζ → h ∈ rotR ζ :=
      fun h => Subgroup.subset_closure h
    rcases hg with (((hg | ⟨c, rfl⟩) | ⟨c, rfl⟩) | ⟨c, rfl⟩) | ⟨c, rfl⟩
    · exact hgen (rotGen_S (hF.rotS_stable hg))
    · obtain ⟨c', h | h⟩ := hF.frob_xO c
      · rw [h]; exact hgen (rotGen_x c')
      · rw [h]; exact hgen (rotGen_y c')
    · obtain ⟨c', h | h⟩ := hF.frob_yO c
      · rw [h]; exact hgen (rotGen_y c')
      · rw [h]; exact hgen (rotGen_x c')
    · obtain ⟨c', h | h⟩ := hF.frob_xO c
      · have e1 : F (ζ * xO c * ζ⁻¹) = ζ * (ξ * xO c' * ξ⁻¹) * ζ⁻¹ := by
          rw [map_mul, map_mul, map_inv, hFζ, h]; group
        rw [e1, (hlam c').1]
        exact hgen (rotGen_xc _)
      · have e1 : F (ζ * xO c * ζ⁻¹) = ζ * (ξ * yO c' * ξ⁻¹) * ζ⁻¹ := by
          rw [map_mul, map_mul, map_inv, hFζ, h]; group
        rw [e1, (hlam c').2]
        exact hgen (rotGen_yc _)
    · obtain ⟨c', h | h⟩ := hF.frob_yO c
      · have e1 : F (ζ * yO c * ζ⁻¹) = ζ * (ξ * yO c' * ξ⁻¹) * ζ⁻¹ := by
          rw [map_mul, map_mul, map_inv, hFζ, h]; group
        rw [e1, (hlam c').2]
        exact hgen (rotGen_yc _)
      · have e1 : F (ζ * yO c * ζ⁻¹) = ζ * (ξ * xO c' * ξ⁻¹) * ζ⁻¹ := by
          rw [map_mul, map_mul, map_inv, hFζ, h]; group
        rw [e1, (hlam c').1]
        exact hgen (rotGen_xc _)
  intro g hg
  exact hle hg

theorem zeta_mem_rotR {b : Lˣ} (hζ : ζ ∈ graphCentralizer TwistTag.D4.tag L (rotElt b))
    (hm : ζ ∈ monomialSubgroup TwistTag.D4.tag L) {M Mi : D4Mat} (hMMi : M * Mi = 1)
    (hconj : d4MatShort * (M * (d4MatShort * Mi)) = M)
    (hMw : ∀ x, weylQuotientHom TwistTag.D4.tag L ⟨ζ, hm⟩ • x = M *ᵥ x) : ζ ∈ rotR ζ := by
  obtain ⟨hnm, hnw⟩ := nO_weyl (L := L)
  set n : ModGL TwistTag.D4.tag L := xO (1 : L) * yO (-1) * xO 1 with hn
  set m : ModGL TwistTag.D4.tag L := ζ * n * ζ⁻¹ with hmdef
  have hnR : n ∈ rotR ζ :=
    mul_mem (mul_mem (Subgroup.subset_closure (rotGen_x 1)) (Subgroup.subset_closure (rotGen_y _)))
      (Subgroup.subset_closure (rotGen_x 1))
  have hmR : m ∈ rotR ζ := by
    have e : m = (ζ * xO (1 : L) * ζ⁻¹) * (ζ * yO (-1) * ζ⁻¹) * (ζ * xO 1 * ζ⁻¹) := by
      rw [hmdef, hn]; group
    rw [e]
    exact mul_mem (mul_mem (Subgroup.subset_closure (rotGen_xc 1))
      (Subgroup.subset_closure (rotGen_yc _))) (Subgroup.subset_closure (rotGen_xc 1))
  have hnZ : n ∈ graphCentralizer TwistTag.D4.tag L (rotElt b) :=
    mul_mem (mul_mem (xO_mem_graphCentralizer b _) (yO_mem_graphCentralizer b _))
      (xO_mem_graphCentralizer b _)
  have hmZ : m ∈ graphCentralizer TwistTag.D4.tag L (rotElt b) :=
    mul_mem (mul_mem hζ hnZ) (inv_mem hζ)
  have hmm : m ∈ monomialSubgroup TwistTag.D4.tag L :=
    mul_mem (mul_mem hm hnm) (inv_mem hm)
  have hnmm : n * m ∈ monomialSubgroup TwistTag.D4.tag L := mul_mem hnm hmm
  have himg : weylQuotientHom TwistTag.D4.tag L ⟨n * m, hnmm⟩ =
      weylQuotientHom TwistTag.D4.tag L ⟨ζ, hm⟩ := by
    have e1 : (⟨n * m, hnmm⟩ : monomialSubgroup TwistTag.D4.tag L) =
        ⟨n, hnm⟩ * (⟨ζ, hm⟩ * ⟨n, hnm⟩ * ⟨ζ, hm⟩⁻¹) := rfl
    rw [e1, map_mul, map_mul, map_mul, map_inv]
    refine FaithfulSMul.eq_of_smul_eq_smul (α := Fin TwistTag.D4.tag.rank → ℤ) fun v => ?_
    have hinv := weyl_inv_smul_mulVec hMMi hMw
    rw [mul_smul, mul_smul, mul_smul, hinv, hnw, hMw, hnw, hMw, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    rw [show d4MatShort * M * d4MatShort * Mi = M by simp only [mul_assoc]; exact hconj]
  have hζ'm : ζ * (n * m)⁻¹ ∈ monomialSubgroup TwistTag.D4.tag L :=
    mul_mem hm (inv_mem hnmm)
  have hζ'w : weylQuotientHom TwistTag.D4.tag L ⟨ζ * (n * m)⁻¹, hζ'm⟩ = 1 := by
    have e1 : (⟨ζ * (n * m)⁻¹, hζ'm⟩ : monomialSubgroup TwistTag.D4.tag L) =
        ⟨ζ, hm⟩ * ⟨n * m, hnmm⟩⁻¹ := rfl
    rw [e1, map_mul, map_inv, himg, mul_inv_cancel]
  have hζ'T := mem_torus_of_weyl_eq_one hζ'm hζ'w
  have hζ'Z : ζ * (n * m)⁻¹ ∈ graphCentralizer TwistTag.D4.tag L (rotElt b) :=
    mul_mem hζ (inv_mem (mul_mem hnZ hmZ))
  have hζ'S := mem_rotS_of_mem_graphCentralizer hζ'T hζ'Z
  have h2 : ζ * (n * m)⁻¹ * (n * m) ∈ rotR ζ :=
    mul_mem (Subgroup.subset_closure (rotGen_S hζ'S)) (mul_mem hnR hmR)
  rwa [inv_mul_cancel_right] at h2

end Assembly

section Frames

variable {p : ℕ} [Fact p.Prime] {L : Type} [Field L] [IsAlgClosed L] [CharP L p]

theorem twistHom_weyl_image (Fr : L →+* L) {ζ : ModGL TwistTag.D4.tag L}
    (hm : ζ ∈ monomialSubgroup TwistTag.D4.tag L) :
    ∃ hFm : twistHom TwistTag.D4 L Fr ζ ∈ monomialSubgroup TwistTag.D4.tag L,
      weylQuotientHom TwistTag.D4.tag L ⟨twistHom TwistTag.D4 L Fr ζ, hFm⟩ =
        weylTwist TwistTag.D4 (weylQuotientHom TwistTag.D4.tag L ⟨ζ, hm⟩) := by
  obtain ⟨w, k, hk, hζe⟩ := monomialSubgroup_le_torusWeylCosets hm
  have hw : weylQuotientHom TwistTag.D4.tag L ⟨ζ, hm⟩ = w := by
    refine weylQuotientHom_eq ?_
    show MapsRootLines ζ w
    rw [hζe]
    exact mapsRootLines_mul_canonicalRep hk w
  have hFk := twistHom_mem_torusGroup_d4 Fr hk
  have hFζ : twistHom TwistTag.D4 L Fr ζ =
      twistHom TwistTag.D4 L Fr k *
        canonicalRep (coxeterSystem TwistTag.D4.tag) L (weylTwist TwistTag.D4 w) := by
    rw [hζe, map_mul, twistHom_canonicalRep]
  have hFm : twistHom TwistTag.D4 L Fr ζ ∈ monomialSubgroup TwistTag.D4.tag L := by
    rw [hFζ]
    exact mul_mem (torusGroup_le_monomialSubgroup hFk) (canonicalRep_mem_monomialSubgroup L _)
  refine ⟨hFm, ?_⟩
  rw [hw]
  refine weylQuotientHom_eq ?_
  show MapsRootLines (twistHom TwistTag.D4 L Fr ζ) _
  rw [hFζ]
  exact mapsRootLines_mul_canonicalRep hFk _

theorem weylTwist_smul_of_perm {w : WeylGroup TwistTag.D4.tag} {M : D4Mat}
    (hMP : M * d4PermMat = d4PermMat * M) (hw : ∀ x, w • x = M *ᵥ x) (x : Fin TwistTag.D4.tag.rank → ℤ) :
    weylTwist TwistTag.D4 w • x = M *ᵥ x := by
  set v := permLattice TwistTag.D4.perm.symm x with hv
  have hx : x = permLattice TwistTag.D4.perm v := (permLattice_permLattice_symm _ x).symm
  rw [hx, weylTwist_smul_permLattice, hw, permLattice_d4_eq, permLattice_d4_eq,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hMP]

theorem rotFrame_one (f : ℕ) (hq : 2 ≤ p ^ f) :
    RotFrame (twistHom TwistTag.D4 L (iterateFrobenius L p f)) ((p ^ f : ℕ) : ℤ) := by
  refine ⟨ellFrame_one f hq, fun g hg => twistHom_mem_adjointGroup _ _ _ hg,
    fun c => ⟨iterateFrobenius L p f c, Or.inl (twistHom_xO _ c)⟩,
    fun c => ⟨iterateFrobenius L p f c, Or.inl (twistHom_yO _ c)⟩,
    fun M ζ hζ hMP hMw => ?_⟩
  obtain ⟨hFm, hFw⟩ := twistHom_weyl_image (iterateFrobenius L p f) hζ
  refine ⟨hFm, fun x => ?_⟩
  rw [hFw]
  exact weylTwist_smul_of_perm hMP hMw x

theorem rotFrame_two (f : ℕ) (hq : 2 ≤ p ^ f) :
    RotFrame (twistHomOppHom (iterateFrobenius L p f)) (-((p ^ f : ℕ) : ℤ)) := by
  obtain ⟨μ, hμ⟩ := z0_conj_xO (L := L)
  obtain ⟨ν, hν⟩ := z0_conj_yO (L := L)
  refine ⟨ellFrame_two f hq, fun g hg => ?_, fun c => ?_, fun c => ?_, fun M ζ hζ hMP hMw => ?_⟩
  · rw [twistHomOppHom_apply, twistHomOpp]
    have hz := monomialSubgroup_le_adjointGroup' (trialityOpposition_mem_monomialSubgroup (K := L))
    exact mul_mem (mul_mem hz (twistHom_mem_adjointGroup _ _ _ hg)) (inv_mem hz)
  · refine ⟨(μ : L) * iterateFrobenius L p f c, Or.inr ?_⟩
    rw [twistHomOppHom_apply, twistHomOpp, twistHom_xO, hμ]
  · refine ⟨(ν : L) * iterateFrobenius L p f c, Or.inr ?_⟩
    rw [twistHomOppHom_apply, twistHomOpp, twistHom_yO, hν]
  · obtain ⟨hFm, hFw⟩ := twistHom_weyl_image (iterateFrobenius L p f) hζ
    have hz := trialityOpposition_mem_monomialSubgroup (K := L)
    have hmm : twistHomOppHom (iterateFrobenius L p f) ζ ∈ monomialSubgroup TwistTag.D4.tag L := by
      rw [twistHomOppHom_apply, twistHomOpp]
      exact mul_mem (mul_mem hz hFm) (inv_mem hz)
    refine ⟨hmm, fun x => ?_⟩
    have e1 : (⟨twistHomOppHom (iterateFrobenius L p f) ζ, hmm⟩ : monomialSubgroup TwistTag.D4.tag L)
        = ⟨_, hz⟩ * ⟨_, hFm⟩ * ⟨_, hz⟩⁻¹ := by
      refine Subtype.ext ?_
      change twistHomOppHom (iterateFrobenius L p f) ζ = _
      rw [twistHomOppHom_apply, twistHomOpp]
      rfl
    have hF1 : ∀ y, weylQuotientHom TwistTag.D4.tag L ⟨twistHom TwistTag.D4 L (iterateFrobenius L p f) ζ, hFm⟩ • y
        = M *ᵥ y := by
      rw [hFw]
      exact weylTwist_smul_of_perm hMP hMw
    have hz0 := weylQuotientHom_trialityOpposition_smul (K := L)
    rw [e1, map_mul, map_mul, map_inv, mul_smul, mul_smul]
    have hzinv : ∀ y : Fin TwistTag.D4.tag.rank → ℤ, (weylQuotientHom TwistTag.D4.tag L ⟨_, hz⟩)⁻¹ • y = -y := by
      intro y
      have : y = weylQuotientHom TwistTag.D4.tag L ⟨_, hz⟩ • (-y) := by rw [hz0, neg_neg]
      conv_lhs => rw [this]
      rw [inv_smul_smul]
    rw [hzinv, smul_neg, hF1, hz0, neg_neg]

end Frames

end CFSG.HardMathSupport.Lang.E6Descent
