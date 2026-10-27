module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherRigidity
public import CFSG.LinearAlgebra.LinearGroups.Perfect

public section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LinearGroups CFSG.LocalAnalysis.ComponentInitial
open Module Submodule
open scoped Pointwise LinearAlgebra.Projectivization commutatorElement

variable {p f : ℕ} {K : Type} [Field K] {r ε : ℕ}

theorem gl_smul_eq_map {ι : Type} [Fintype ι] [DecidableEq ι] (g : GL ι K)
    (W : Submodule K (ι → K)) : g • W = W.map (mulVecLin (g : Matrix ι ι K)) := by
  ext v
  rw [Submodule.mem_map]
  exact Submodule.mem_smul_pointwise_iff_exists v g W

section Levi

variable (h : UnitaryFieldData p f K)

theorem leviDual_mul' (A B : GL (Fin r) K) :
    leviDual h (A * B) = leviDual h A * leviDual h B := by
  rw [leviDual, leviDual, leviDual, _root_.mul_inv_rev, Units.val_mul, Matrix.map_mul,
    transpose_mul]

theorem leviDual_one : leviDual h (1 : GL (Fin r) K) = 1 := by
  rw [leviDual, inv_one, Units.val_one, Matrix.map_one _ (map_zero h.bar) (map_one h.bar),
    transpose_one]

@[expose] noncomputable def leviGL (ε : ℕ) : GL (Fin r) K →* GL (HypIndex r ε) K where
  toFun A := glOfLinearEquiv (hypLeviEquiv h A)
  map_one' := Units.ext <| ext_iff_mulVec.mpr fun v => by
    rw [glOfLinearEquiv_mulVec, hypLeviEquiv_apply, Units.val_one, Units.val_one, one_mulVec,
      leviDual_one, leviFun_one]
  map_mul' A B := Units.ext <| ext_iff_mulVec.mpr fun v => by
    rw [Units.val_mul, ← mulVec_mulVec, glOfLinearEquiv_mulVec, glOfLinearEquiv_mulVec,
      glOfLinearEquiv_mulVec, hypLeviEquiv_apply, hypLeviEquiv_apply, hypLeviEquiv_apply,
      leviFun_leviFun, Units.val_mul, leviDual_mul']

theorem leviGL_mulVec (A : GL (Fin r) K) (v : HypIndex r ε → K) :
    ((leviGL h ε A : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ v =
      leviFun (A : Matrix (Fin r) (Fin r) K) (leviDual h A) v :=
  glOfLinearEquiv_mulVec _ v

theorem coe_leviGL (A : GL (Fin r) K) :
    ((leviGL h ε A : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) =
      blk3 (A : Matrix (Fin r) (Fin r) K) 0 0 1 0 (leviDual h A) := by
  refine ext_iff_mulVec.mpr fun v => ?_
  rw [leviGL_mulVec]
  funext c
  rcases c with i | k | i <;>
    simp [leviFun, mulVec, dotProduct, Fintype.sum_sum_type, one_apply]

theorem det_leviGL (A : GL (Fin r) K) :
    ((leviGL h ε A : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K).det =
      (A : Matrix (Fin r) (Fin r) K).det *
        h.bar ((A⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K).det := by
  rw [coe_leviGL, det_blk3, det_one, mul_one, leviDual, det_transpose,
    RingHom.map_det h.bar]
  rfl

@[expose] noncomputable def leviSU (ε : ℕ) : SpecialLinearGroup (Fin r) K →* hypSU h r ε :=
  ((leviGL h ε).comp SpecialLinearGroup.toGL).codRestrict (hypSU h r ε) fun A =>
    mem_hypSU.mpr ⟨hypLevi_isometry h _, by
      rw [MonoidHom.comp_apply, det_leviGL, ← map_inv, SpecialLinearGroup.coe_GL_coe_matrix,
        SpecialLinearGroup.coe_GL_coe_matrix, Matrix.SpecialLinearGroup.det_coe,
        Matrix.SpecialLinearGroup.det_coe, map_one, mul_one]⟩

theorem coe_leviSU (A : SpecialLinearGroup (Fin r) K) :
    ((leviSU h ε A : hypSU h r ε) : GL (HypIndex r ε) K) =
      leviGL h ε (SpecialLinearGroup.toGL A) :=
  rfl

theorem leviSU_mulVec (A : SpecialLinearGroup (Fin r) K) (v : HypIndex r ε → K) :
    (((leviSU h ε A : hypSU h r ε) : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ v =
      leviFun (A : Matrix (Fin r) (Fin r) K) (leviDual h (SpecialLinearGroup.toGL A)) v := by
  rw [coe_leviSU, leviGL_mulVec, SpecialLinearGroup.coe_GL_coe_matrix]

end Levi

section XPt

variable (h : UnitaryFieldData p f K)

@[expose] noncomputable def xPt (ε : ℕ) (U : ℙ K (Fin r → K)) : hypIsotropicLines h r ε :=
  ⟨U.submodule.map (hypXEmb r ε), by rw [finrank_map_hypXEmb]; exact U.finrank_submodule,
    fun a ha => hypX_isotropic h a (LinearMap.map_le_range ha) a (LinearMap.map_le_range ha)⟩

theorem coe_xPt (U : ℙ K (Fin r → K)) :
    (xPt h ε U : Submodule K (HypIndex r ε → K)) = U.submodule.map (hypXEmb r ε) :=
  rfl

theorem xPt_le (U : ℙ K (Fin r → K)) :
    (xPt h ε U : Submodule K (HypIndex r ε → K)) ≤ hypX K r ε :=
  LinearMap.map_le_range

theorem xPt_injective : Function.Injective (xPt h ε (r := r)) := fun _ _ hU =>
  Projectivization.submodule_injective
    (Submodule.map_injective_of_injective hypXEmb_injective (congrArg Subtype.val hU))

theorem exists_xPt_eq (L : hypIsotropicLines h r ε)
    (hL : (L : Submodule K (HypIndex r ε → K)) ≤ hypX K r ε) : ∃ U, xPt h ε U = L := by
  have hd : finrank K ((L : Submodule K (HypIndex r ε → K)).comap (hypXEmb r ε)) = 1 := by
    rw [finrank_comap_hypXEmb hL]
    exact L.2.1
  obtain ⟨a, ha, hLa⟩ := ProjectiveGeometry.exists_eq_span_singleton hd
  refine ⟨Projectivization.mk K a ha, Subtype.ext ?_⟩
  rw [coe_xPt, Projectivization.submodule_mk, ← hLa, map_comap_hypXEmb hL]

omit h in
theorem submodule_smul_sl (A : SpecialLinearGroup (Fin r) K)
    (U : ℙ K (Fin r → K)) :
    (A • U).submodule = U.submodule.map (mulVecLin (A : Matrix (Fin r) (Fin r) K)) := by
  induction U using Projectivization.ind with
  | h v hv =>
    rw [Projectivization.smul_mk, Projectivization.submodule_mk, Projectivization.submodule_mk,
      Submodule.map_span, Set.image_singleton]
    rfl

theorem leviSU_smul_xPt (A : SpecialLinearGroup (Fin r) K) (U : ℙ K (Fin r → K)) :
    hypProjLineAction h r ε (hypProj h r ε (leviSU h ε A)) (xPt h ε U) = xPt h ε (A • U) := by
  apply Subtype.ext
  change ((leviSU h ε A : hypSU h r ε) : GL (HypIndex r ε) K) •
    (xPt h ε U : Submodule K (HypIndex r ε → K)) = _
  rw [gl_smul_eq_map, coe_xPt, coe_xPt, submodule_smul_sl, ← Submodule.map_comp,
    ← Submodule.map_comp]
  congr 1
  refine LinearMap.ext fun a => ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, mulVecLin_apply, mulVecLin_apply,
    leviSU_mulVec, leviFun_hypXEmb]

end XPt

section Blocks

theorem eq_hypXEmb_of_mem {v : HypIndex r ε → K} (hv : v ∈ hypX K r ε) :
    v = hypXEmb r ε (fun i => v (.inl i)) := by
  obtain ⟨a, rfl⟩ := hv
  rfl

theorem eq_hypYEmb_of_mem {v : HypIndex r ε → K} (hv : v ∈ hypY K r ε) :
    v = hypYEmb r ε (fun i => v (.inr (.inr i))) := by
  obtain ⟨b, rfl⟩ := hv
  rfl

@[expose] def xBlock (g : Matrix (HypIndex r ε) (HypIndex r ε) K) : Matrix (Fin r) (Fin r) K :=
  Matrix.of fun i j => g (.inl i) (.inl j)

@[expose] def yBlock (g : Matrix (HypIndex r ε) (HypIndex r ε) K) : Matrix (Fin r) (Fin r) K :=
  Matrix.of fun i j => g (.inr (.inr i)) (.inr (.inr j))

@[expose] def zBlock (g : Matrix (HypIndex r ε) (HypIndex r ε) K) : Matrix (Fin ε) (Fin ε) K :=
  Matrix.of fun k l => g (.inr (.inl k)) (.inr (.inl l))

theorem mulVec_hypXEmb {g : Matrix (HypIndex r ε) (HypIndex r ε) K}
    (hg : ∀ a, g *ᵥ hypXEmb r ε a ∈ hypX K r ε) (a : Fin r → K) :
    g *ᵥ hypXEmb r ε a = hypXEmb r ε (xBlock g *ᵥ a) := by
  rw [eq_hypXEmb_of_mem (hg a)]
  congr 1
  funext i
  simp [mulVec, dotProduct, Fintype.sum_sum_type, hypXEmb, xBlock]

theorem mulVec_hypYEmb {g : Matrix (HypIndex r ε) (HypIndex r ε) K}
    (hg : ∀ b, g *ᵥ hypYEmb r ε b ∈ hypY K r ε) (b : Fin r → K) :
    g *ᵥ hypYEmb r ε b = hypYEmb r ε (yBlock g *ᵥ b) := by
  rw [eq_hypYEmb_of_mem (hg b)]
  congr 1
  funext i
  simp [mulVec, dotProduct, Fintype.sum_sum_type, hypYEmb, yBlock]

theorem mulVec_hypZEmb {g : Matrix (HypIndex r ε) (HypIndex r ε) K}
    (hg : ∀ t, ∀ c, (∀ k, c ≠ .inr (.inl k)) → (g *ᵥ hypZEmb r ε t) c = 0) (t : Fin ε → K) :
    g *ᵥ hypZEmb r ε t = hypZEmb r ε (zBlock g *ᵥ t) := by
  funext c
  rcases c with i | k | i
  · rw [hg t _ fun k h0 => by cases h0]
    rfl
  · simp [mulVec, dotProduct, Fintype.sum_sum_type, hypZEmb, zBlock]
  · rw [hg t _ fun k h0 => by cases h0]
    rfl

theorem blk3_diag_mulVec (A : Matrix (Fin r) (Fin r) K) (P : Matrix (Fin ε) (Fin ε) K)
    (C : Matrix (Fin r) (Fin r) K) (a b : Fin r → K) (t : Fin ε → K) :
    blk3 A 0 0 P 0 C *ᵥ (hypXEmb r ε a + hypZEmb r ε t + hypYEmb r ε b) =
      hypXEmb r ε (A *ᵥ a) + hypZEmb r ε (P *ᵥ t) + hypYEmb r ε (C *ᵥ b) := by
  funext c
  rcases c with i | k | i <;>
    simp [mulVec, dotProduct, Fintype.sum_sum_type, hypXEmb, hypYEmb, hypZEmb]

theorem blk3_one_one : blk3 (1 : Matrix (Fin r) (Fin r) K) 0 0 (1 : Matrix (Fin ε) (Fin ε) K) 0 1 =
    1 := by
  ext a b
  rcases a with i | k | i <;> rcases b with j | l | j <;> simp [one_apply]

end Blocks

section Stab

variable (h : UnitaryFieldData p f K)

@[expose] def xyStab (r ε : ℕ) : Subgroup (hypSU h r ε) :=
  MulAction.stabilizer (hypSU h r ε) (hypX K r ε) ⊓
    MulAction.stabilizer (hypSU h r ε) (hypY K r ε)

theorem mem_xyStab {g : hypSU h r ε} :
    g ∈ xyStab h r ε ↔ g • hypX K r ε = hypX K r ε ∧ g • hypY K r ε = hypY K r ε :=
  Iff.rfl

variable {h}

theorem mulVec_mem_of_smul_eq {g : hypSU h r ε} {W : Submodule K (HypIndex r ε → K)}
    (hW : g • W = W) {v : HypIndex r ε → K} (hv : v ∈ W) :
    ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ v ∈ W := by
  rw [← hW]
  exact Submodule.smul_mem_pointwise_smul v g W hv

theorem smul_le_iff_of_smul_eq {g : hypSU h r ε} {W : Submodule K (HypIndex r ε → K)}
    (hW : g • W = W) (L : Submodule K (HypIndex r ε → K)) : g • L ≤ W ↔ L ≤ W := by
  constructor
  · intro hL u hu
    have h1 : g • u ∈ W := hL (Submodule.smul_mem_pointwise_smul u g L hu)
    rw [← hW] at h1
    obtain ⟨u', hu', he⟩ := (Submodule.mem_smul_pointwise_iff_exists _ g W).mp h1
    rw [← smul_left_cancel g he]
    exact hu'
  · intro hL v hv
    obtain ⟨u, hu, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists v g L).mp hv
    rw [← hW]
    exact Submodule.smul_mem_pointwise_smul u g W (hL hu)

variable (g : xyStab h r ε)

theorem xyStab_mulVec_hypXEmb (a : Fin r → K) :
    (((g : hypSU h r ε) : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ
      hypXEmb r ε a = hypXEmb r ε (xBlock (((g : hypSU h r ε) : GL (HypIndex r ε) K) :
        Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ a) :=
  mulVec_hypXEmb (fun a => mulVec_mem_of_smul_eq ((mem_xyStab h).mp g.2).1 ⟨a, rfl⟩) a

theorem xyStab_mulVec_hypYEmb (b : Fin r → K) :
    (((g : hypSU h r ε) : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ
      hypYEmb r ε b = hypYEmb r ε (yBlock (((g : hypSU h r ε) : GL (HypIndex r ε) K) :
        Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ b) :=
  mulVec_hypYEmb (fun b => mulVec_mem_of_smul_eq ((mem_xyStab h).mp g.2).2 ⟨b, rfl⟩) b

theorem xyStab_mulVec_hypZEmb (t : Fin ε → K) :
    (((g : hypSU h r ε) : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ
      hypZEmb r ε t = hypZEmb r ε (zBlock (((g : hypSU h r ε) : GL (HypIndex r ε) K) :
        Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ t) := by
  refine mulVec_hypZEmb (fun t c hc => ?_) t
  have hpair : ∀ u : HypIndex r ε → K, (u ∈ hypX K r ε ∨ u ∈ hypY K r ε) →
      hypForm h r ε u (((g : hypSU h r ε) : GL (HypIndex r ε) K) *ᵥ hypZEmb r ε t) = 0 := by
    intro u hu
    set g' : hypSU h r ε := ((g⁻¹ : xyStab h r ε) : hypSU h r ε) with hg'
    have hu' : g' • u ∈ hypX K r ε ∨ g' • u ∈ hypY K r ε := by
      rcases hu with hu | hu
      · exact Or.inl (mulVec_mem_of_smul_eq ((mem_xyStab h).mp (g⁻¹).2).1 hu)
      · exact Or.inr (mulVec_mem_of_smul_eq ((mem_xyStab h).mp (g⁻¹).2).2 hu)
    have he : u = (g : hypSU h r ε) • g' • u := by
      rw [smul_smul, hg', ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, one_smul]
    have h2 : hypForm h r ε u ((g : hypSU h r ε) • hypZEmb r ε t) =
        hypForm h r ε (g' • u) (hypZEmb r ε t) := by
      conv_lhs => rw [he]
      exact hypForm_smul_smul h _ _ _
    refine h2.trans ?_
    rcases hu' with ⟨a, ha⟩ | ⟨b, hb⟩
    · rw [← ha, hypForm_hypXEmb]
      simp [hypZEmb]
    · rw [← hb, hypForm_hypYEmb]
      simp [hypZEmb]
  rcases c with i | k | i
  · have := hpair (hypYEmb r ε (Pi.single i 1)) (Or.inr ⟨_, rfl⟩)
    rw [hypForm_hypYEmb] at this
    simpa [Pi.single_apply] using this
  · exact absurd rfl (hc k)
  · have := hpair (hypXEmb r ε (Pi.single i 1)) (Or.inl ⟨_, rfl⟩)
    rw [hypForm_hypXEmb] at this
    simpa [Pi.single_apply] using this

end Stab

section XBlock

variable (h : UnitaryFieldData p f K)

@[expose] noncomputable def xBlockHom (r ε : ℕ) : xyStab h r ε →* Matrix (Fin r) (Fin r) K where
  toFun g := xBlock (((g : hypSU h r ε) : GL (HypIndex r ε) K) :
    Matrix (HypIndex r ε) (HypIndex r ε) K)
  map_one' := by
    ext i j
    simp [xBlock, one_apply]
  map_mul' g g' := by
    refine ext_iff_mulVec.mpr fun a => hypXEmb_injective (ε := ε) ?_
    rw [← mulVec_mulVec, ← xyStab_mulVec_hypXEmb (g * g'), ← xyStab_mulVec_hypXEmb g,
      ← xyStab_mulVec_hypXEmb g', mulVec_mulVec]
    rfl

@[expose] noncomputable def xBlockUnits (r ε : ℕ) : xyStab h r ε →* GL (Fin r) K :=
  (xBlockHom h r ε).toHomUnits

theorem coe_xBlockUnits (g : xyStab h r ε) :
    ((xBlockUnits h r ε g : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) =
      xBlock (((g : hypSU h r ε) : GL (HypIndex r ε) K) :
        Matrix (HypIndex r ε) (HypIndex r ε) K) :=
  rfl

theorem yBlock_eq_leviDual (g : xyStab h r ε) :
    yBlock (((g : hypSU h r ε) : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) =
      leviDual h (xBlockUnits h r ε g) := by
  set M := (((g : hypSU h r ε) : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K)
    with hM
  have hAC : ((xBlock M).map h.bar)ᵀ * yBlock M = 1 := by
    refine ext_iff_mulVec.mpr fun b => funext fun i => ?_
    have h1 := hypForm_smul_smul h (g : hypSU h r ε) (hypXEmb r ε (Pi.single i 1)) (hypYEmb r ε b)
    change hypForm h r ε (M *ᵥ hypXEmb r ε (Pi.single i 1)) (M *ᵥ hypYEmb r ε b) = _ at h1
    rw [hM, xyStab_mulVec_hypXEmb, xyStab_mulVec_hypYEmb, hypForm_hypXEmb_hypYEmb,
      hypForm_hypXEmb_hypYEmb, bar_mulVec_dotProduct, ← hM] at h1
    have hbar : (fun j => h.bar ((Pi.single i (1 : K) : Fin r → K) j)) = Pi.single i 1 := by
      funext j
      by_cases hj : j = i
      · subst hj
        simp
      · simp [hj]
    rw [hbar, single_dotProduct, single_dotProduct, one_mul, one_mul] at h1
    rw [h1, one_mulVec]
  have hA : ((xBlockUnits h r ε g : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) = xBlock M := rfl
  calc yBlock M = (leviDual h (xBlockUnits h r ε g) *
      (((xBlockUnits h r ε g : GL (Fin r) K) : Matrix (Fin r) (Fin r) K).map h.bar)ᵀ) *
        yBlock M := by rw [leviDual_mul, Matrix.one_mul]
    _ = leviDual h (xBlockUnits h r ε g) := by rw [Matrix.mul_assoc, hA, hAC, Matrix.mul_one]

theorem coe_eq_blk3 (g : xyStab h r ε) :
    (((g : hypSU h r ε) : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) =
      blk3 (xBlock (((g : hypSU h r ε) : GL (HypIndex r ε) K) :
          Matrix (HypIndex r ε) (HypIndex r ε) K)) 0 0
        (zBlock (((g : hypSU h r ε) : GL (HypIndex r ε) K) :
          Matrix (HypIndex r ε) (HypIndex r ε) K)) 0 (leviDual h (xBlockUnits h r ε g)) := by
  refine ext_iff_mulVec.mpr fun v => ?_
  obtain ⟨a, t, b, rfl⟩ : ∃ a t b, v = hypXEmb r ε a + hypZEmb r ε t + hypYEmb r ε b :=
    ⟨_, _, _, hypSplit v⟩
  rw [blk3_diag_mulVec, mulVec_add, mulVec_add, xyStab_mulVec_hypXEmb, xyStab_mulVec_hypZEmb,
    xyStab_mulVec_hypYEmb, yBlock_eq_leviDual]

theorem xBlockUnits_injective (hε : ε ≤ 1) : Function.Injective (xBlockUnits h r ε) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro g hg
  have hA : xBlockUnits h r ε g = 1 := hg
  have hA' : xBlock (((g : hypSU h r ε) : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K) = 1 := by
    rw [← coe_xBlockUnits, hA, Units.val_one]
  have hg' := coe_eq_blk3 h g
  rw [hA', hA, leviDual_one] at hg'
  have hdet := (mem_hypSU.mp (g : hypSU h r ε).2).2
  rw [hg', det_blk3, det_one, one_mul, mul_one] at hdet
  have hP : zBlock (((g : hypSU h r ε) : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K) = 1 := by
    obtain rfl | rfl : ε = 0 ∨ ε = 1 := by omega
    · ext k
      exact k.elim0
    · ext k l
      obtain rfl : k = 0 := Subsingleton.elim _ _
      obtain rfl : l = 0 := Subsingleton.elim _ _
      rw [det_fin_one] at hdet
      rw [hdet, one_apply_eq]
  rw [hP, blk3_one_one] at hg'
  exact Subgroup.mem_bot.mpr (Subtype.ext (Subtype.ext (Units.ext hg')))

theorem leviSU_mem_xyStab (A : SpecialLinearGroup (Fin r) K) : leviSU h ε A ∈ xyStab h r ε := by
  have hX : ∀ B : SpecialLinearGroup (Fin r) K, ∀ v ∈ hypX K r ε,
      (((leviSU h ε B : hypSU h r ε) : GL (HypIndex r ε) K) :
        Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ v ∈ hypX K r ε := by
    rintro B _ ⟨a, rfl⟩
    rw [leviSU_mulVec, leviFun_hypXEmb]
    exact ⟨_, rfl⟩
  have hY : ∀ B : SpecialLinearGroup (Fin r) K, ∀ v ∈ hypY K r ε,
      (((leviSU h ε B : hypSU h r ε) : GL (HypIndex r ε) K) :
        Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ v ∈ hypY K r ε := by
    rintro B _ ⟨b, rfl⟩
    rw [leviSU_mulVec, leviFun_hypYEmb]
    exact ⟨_, rfl⟩
  have hinv : (((leviSU h ε A : hypSU h r ε) : GL (HypIndex r ε) K)⁻¹ : GL (HypIndex r ε) K) =
      ((leviSU h ε A⁻¹ : hypSU h r ε) : GL (HypIndex r ε) K) := by
    rw [map_inv, Subgroup.coe_inv]
  refine ⟨smul_eq_of_mulVec_mem (hX A) fun v hv => ?_,
    smul_eq_of_mulVec_mem (hY A) fun v hv => ?_⟩
  · rw [hinv]
    exact hX A⁻¹ v hv
  · rw [hinv]
    exact hY A⁻¹ v hv

@[expose] noncomputable def leviXY (ε : ℕ) : SpecialLinearGroup (Fin r) K →* xyStab h r ε :=
  (leviSU h ε).codRestrict (xyStab h r ε) (leviSU_mem_xyStab h)

theorem coe_leviXY (A : SpecialLinearGroup (Fin r) K) :
    ((leviXY h ε A : xyStab h r ε) : hypSU h r ε) = leviSU h ε A :=
  rfl

theorem xBlockUnits_leviXY (A : SpecialLinearGroup (Fin r) K) :
    xBlockUnits h r ε (leviXY h ε A) = SpecialLinearGroup.toGL A := by
  ext i j
  rw [coe_xBlockUnits, coe_leviXY, coe_leviSU, coe_leviGL]
  rfl

end XBlock

section PointStab

variable (h : UnitaryFieldData p f K)

@[expose] def isoPtsOf (W : Submodule K (HypIndex r ε → K)) : Set (hypIsotropicLines h r ε) :=
  {L | (L : Submodule K (HypIndex r ε → K)) ≤ W}

@[expose] noncomputable def xyPointStab (r ε : ℕ) :
    Subgroup (Equiv.Perm (hypIsotropicLines h r ε)) :=
  (hypProjLineAction h r ε).range ⊓
    MulAction.stabilizer (Equiv.Perm (hypIsotropicLines h r ε)) (isoPtsOf h (hypX K r ε)) ⊓
    MulAction.stabilizer (Equiv.Perm (hypIsotropicLines h r ε)) (isoPtsOf h (hypY K r ε))

@[expose] noncomputable def leviPointGroup (r ε : ℕ) :
    Subgroup (Equiv.Perm (hypIsotropicLines h r ε)) :=
  ((hypProjLineAction h r ε).comp ((hypProj h r ε).comp (leviSU (r := r) h ε))).range

@[expose] noncomputable def xyPerm (r ε : ℕ) :
    xyStab h r ε →* Equiv.Perm (hypIsotropicLines h r ε) :=
  (hypProjLineAction h r ε).comp ((hypProj h r ε).comp (xyStab h r ε).subtype)

theorem xyPerm_apply (g : xyStab h r ε) (L : hypIsotropicLines h r ε) :
    (xyPerm h r ε g L : Submodule K (HypIndex r ε → K)) =
      (g : hypSU h r ε) • (L : Submodule K (HypIndex r ε → K)) :=
  rfl

theorem mem_xyPointStab {x : Equiv.Perm (hypIsotropicLines h r ε)} :
    x ∈ xyPointStab h r ε ↔ x ∈ (hypProjLineAction h r ε).range ∧
      (∀ L : hypIsotropicLines h r ε, ((x L : Submodule K (HypIndex r ε → K)) ≤ hypX K r ε ↔
        (L : Submodule K (HypIndex r ε → K)) ≤ hypX K r ε)) ∧
      (∀ L : hypIsotropicLines h r ε, ((x L : Submodule K (HypIndex r ε → K)) ≤ hypY K r ε ↔
        (L : Submodule K (HypIndex r ε → K)) ≤ hypY K r ε)) := by
  simp only [xyPointStab, Subgroup.mem_inf, MulAction.mem_stabilizer_set, Equiv.Perm.smul_def,
    isoPtsOf, Set.mem_ofPred_eq, and_assoc]

variable {h}

theorem smul_eq_of_forall_le_iff {g : hypSU h r ε} {W : Submodule K (HypIndex r ε → K)}
    (hW : ∀ v ∈ W, ∀ w ∈ W, hypForm h r ε v w = 0)
    (hg : ∀ L : hypIsotropicLines h r ε, (g • (L : Submodule K (HypIndex r ε → K)) ≤ W ↔
      (L : Submodule K (HypIndex r ε → K)) ≤ W)) : g • W = W := by
  refine smul_eq_of_mulVec_mem (g := (g : GL (HypIndex r ε) K)) (fun v hv => ?_) fun v hv => ?_
  · by_cases hv0 : v = 0
    · rw [hv0, mulVec_zero]
      exact W.zero_mem
    let L : hypIsotropicLines h r ε := ⟨K ∙ v, span_mem_hypIsotropicLines h hv0 (hW v hv v hv)⟩
    have hL := (hg L).mpr ((span_singleton_le_iff_mem _ _).mpr hv)
    exact hL (Submodule.smul_mem_pointwise_smul v g _ (mem_span_singleton_self v))
  · by_cases hv0 : v = 0
    · rw [hv0, mulVec_zero]
      exact W.zero_mem
    set w := (g⁻¹ : hypSU h r ε) • v with hw
    have hgw : g • w = v := by rw [hw, smul_inv_smul]
    have hw0 : w ≠ 0 := fun h0 => hv0 (by rw [← hgw, h0, smul_zero])
    have hww : hypForm h r ε w w = 0 := by
      rw [hw]
      exact (hypForm_smul_smul h g⁻¹ v v).trans (hW v hv v hv)
    let L : hypIsotropicLines h r ε := ⟨K ∙ w, span_mem_hypIsotropicLines h hw0 hww⟩
    have hL : g • (L : Submodule K (HypIndex r ε → K)) ≤ W := by
      intro u hu
      obtain ⟨u', hu', rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists u g _).mp hu
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hu'
      rw [smul_comm, hgw]
      exact W.smul_mem c hv
    exact (hg L).mp hL (mem_span_singleton_self w)

theorem exists_of_mem_xyPointStab {x : Equiv.Perm (hypIsotropicLines h r ε)}
    (hx : x ∈ xyPointStab h r ε) : ∃ g : xyStab h r ε, xyPerm h r ε g = x := by
  obtain ⟨⟨y, rfl⟩, hX, hY⟩ := (mem_xyPointStab h).mp hx
  obtain ⟨g, rfl⟩ := hypProj_surjective h r ε y
  exact ⟨⟨g, smul_eq_of_forall_le_iff (hypX_isotropic h) hX,
    smul_eq_of_forall_le_iff (hypY_isotropic h) hY⟩, rfl⟩

theorem xyPerm_mem_xyPointStab (g : xyStab h r ε) : xyPerm h r ε g ∈ xyPointStab h r ε :=
  (mem_xyPointStab h).mpr ⟨⟨hypProj h r ε g, rfl⟩,
    fun _ => smul_le_iff_of_smul_eq ((mem_xyStab h).mp g.2).1 _,
    fun _ => smul_le_iff_of_smul_eq ((mem_xyStab h).mp g.2).2 _⟩

theorem xyPerm_leviXY (A : SpecialLinearGroup (Fin r) K) :
    xyPerm h r ε (leviXY h ε A) = hypProjLineAction h r ε (hypProj h r ε (leviSU h ε A)) :=
  rfl

theorem leviPointGroup_le : leviPointGroup h r ε ≤ xyPointStab h r ε := by
  rintro _ ⟨A, rfl⟩
  exact xyPerm_mem_xyPointStab (leviXY h ε A)

theorem commutator_xyPointStab_le (hε : ε ≤ 1) :
    ⁅xyPointStab h r ε, xyPointStab h r ε⁆ ≤ leviPointGroup h r ε := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  obtain ⟨g, rfl⟩ := exists_of_mem_xyPointStab hx
  obtain ⟨g', rfl⟩ := exists_of_mem_xyPointStab hy
  set B₀ : GL (Fin r) K := ⁅xBlockUnits h r ε g, xBlockUnits h r ε g'⁆ with hB₀
  have hdet : (B₀ : Matrix (Fin r) (Fin r) K).det = 1 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply, hB₀, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _), Units.val_one]
  set B : SpecialLinearGroup (Fin r) K := ⟨B₀, hdet⟩
  have hB : SpecialLinearGroup.toGL B = B₀ := Units.ext rfl
  have hk : ⁅g, g'⁆ = leviXY h ε B := xBlockUnits_injective h hε (by
    rw [map_commutatorElement, xBlockUnits_leviXY, hB])
  refine ⟨B, ?_⟩
  rw [← map_commutatorElement, hk]
  rfl

theorem commute_of_forall_le_hypX (hε : ε ≤ 1) {c : Equiv.Perm (hypIsotropicLines h r ε)}
    (hc : c ∈ xyPointStab h r ε)
    (hcX : ∀ L : hypIsotropicLines h r ε,
      (L : Submodule K (HypIndex r ε → K)) ≤ hypX K r ε → c L = L)
    {x : Equiv.Perm (hypIsotropicLines h r ε)} (hx : x ∈ xyPointStab h r ε) :
    c * x = x * c := by
  obtain ⟨k, rfl⟩ := exists_of_mem_xyPointStab hc
  obtain ⟨g, rfl⟩ := exists_of_mem_xyPointStab hx
  set A := xBlock (((k : hypSU h r ε) : GL (HypIndex r ε) K) :
    Matrix (HypIndex r ε) (HypIndex r ε) K) with hA
  have hmul : ∀ a : Fin r → K, ∃ μ : K, A *ᵥ a = μ • a := by
    intro a
    by_cases ha : a = 0
    · exact ⟨0, by rw [ha, mulVec_zero, smul_zero]⟩
    have hx0 : hypXEmb r ε a ≠ 0 := fun h0 => ha (hypXEmb_injective (h0.trans (map_zero _).symm))
    let L : hypIsotropicLines h r ε := ⟨K ∙ hypXEmb r ε a,
      span_mem_hypIsotropicLines h hx0 (hypX_isotropic h _ ⟨a, rfl⟩ _ ⟨a, rfl⟩)⟩
    have hL := congrArg Subtype.val (hcX L ((span_singleton_le_iff_mem _ _).mpr ⟨a, rfl⟩))
    rw [xyPerm_apply] at hL
    have hmem : (k : hypSU h r ε) • hypXEmb r ε a ∈ K ∙ hypXEmb r ε a := by
      have := Submodule.smul_mem_pointwise_smul (hypXEmb r ε a) (k : hypSU h r ε)
        (K ∙ hypXEmb r ε a) (mem_span_singleton_self _)
      change _ ∈ ((k : hypSU h r ε) • (L : Submodule K (HypIndex r ε → K))) at this
      rwa [hL] at this
    obtain ⟨μ, hμ⟩ := Submodule.mem_span_singleton.mp hmem
    refine ⟨μ, hypXEmb_injective (ε := ε) ?_⟩
    rw [map_smul, hμ, hA, ← xyStab_mulVec_hypXEmb]
    rfl
  obtain ⟨μ, hμ⟩ := LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent
    (f := mulVecLin A) fun v hv => by
      obtain ⟨ν, hν⟩ := hmul v
      have := LinearIndependent.pair_iff.mp hv ν (-1) (by
        rw [mulVecLin_apply, hν, neg_one_smul, add_neg_cancel])
      exact neg_ne_zero.mpr one_ne_zero this.2
  have hAμ : A = μ • (1 : Matrix (Fin r) (Fin r) K) := ext_iff_mulVec.mpr fun v => by
    have := LinearMap.congr_fun hμ v
    rw [mulVecLin_apply] at this
    rw [this, LinearMap.smul_apply, Module.End.one_apply, smul_mulVec, one_mulVec]
  have hcomm : k * g = g * k := xBlockUnits_injective h hε (by
    rw [map_mul, map_mul]
    refine Units.ext ?_
    rw [Units.val_mul, Units.val_mul, coe_xBlockUnits h k, ← hA, hAμ, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one])
  rw [← map_mul, hcomm, map_mul]

end PointStab

theorem exists_finset_card_four (h : UnitaryFieldData p f K) : ∃ s : Finset K, s.card = 4 := by
  have := h.finite
  have : Fintype K := Fintype.ofFinite K
  have hq := UnitaryFieldData.one_lt_pow h
  have hcard : 4 ≤ (Finset.univ : Finset K).card := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, UnitaryFieldData.card_eq_sq h]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ (p ^ f) ^ 2 := Nat.pow_le_pow_left hq 2
  obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq hcard
  exact ⟨t, ht⟩

theorem unitary_rank_two_opposite_levi (h : UnitaryFieldData p f K) (hε : ε ≤ 1) :
    ⁅xyPointStab h 2 ε, xyPointStab h 2 ε⁆ = leviPointGroup h 2 ε ∧
      Group.IsPerfect (leviPointGroup h 2 ε) ∧
      (∀ c ∈ xyPointStab h 2 ε, (∀ L : hypIsotropicLines h 2 ε,
          (L : Submodule K (HypIndex 2 ε → K)) ≤ hypX K 2 ε → c L = L) →
        ∀ g ∈ xyPointStab h 2 ε, c * g = g * c) ∧
      (∀ (A : SpecialLinearGroup (Fin 2) K) (U : ℙ K (Fin 2 → K)),
        hypProjLineAction h 2 ε (hypProj h 2 ε (leviSU h ε A)) (xPt h ε U) = xPt h ε (A • U)) ∧
      {τ : Equiv.Perm (ℙ K (Fin 2 → K)) | ∃ g ∈ leviPointGroup h 2 ε,
          ∀ U, g (xPt h ε U) = xPt h ε (τ U)} =
        Set.range (MulAction.toPermHom (SpecialLinearGroup (Fin 2) K) (ℙ K (Fin 2 → K))) := by
  have : Group.IsPerfect (SpecialLinearGroup (Fin 2) K) :=
    special_linear_dimension_two_perfect (exists_finset_card_four h)
  have hperf : Group.IsPerfect (leviPointGroup h 2 ε) := Group.IsPerfect.range _
  have hLL : ⁅leviPointGroup h 2 ε, leviPointGroup h 2 ε⁆ = leviPointGroup h 2 ε :=
    Subgroup.isPerfect_iff.mp hperf
  refine ⟨le_antisymm (commutator_xyPointStab_le hε) ?_, hperf,
    fun c hc hcX g hg => commute_of_forall_le_hypX hε hc hcX hg, leviSU_smul_xPt h, ?_⟩
  · rw [← hLL]
    exact Subgroup.commutator_mono leviPointGroup_le leviPointGroup_le
  · ext τ
    constructor
    · rintro ⟨_, ⟨A, rfl⟩, hτ⟩
      refine ⟨A, Equiv.ext fun U => (xPt_injective (ε := ε) h).eq_iff.mp ?_⟩
      rw [← hτ U]
      exact (leviSU_smul_xPt h A U).symm
    · rintro ⟨A, rfl⟩
      exact ⟨_, ⟨A, rfl⟩, fun U => leviSU_smul_xPt h A U⟩

end CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
