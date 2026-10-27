module

public import CFSG.ClassicalInvolution.Phan.PhanQ1Pair
public import CFSG.ClassicalInvolution.Phan.PhanP7Rot

public section

namespace CFSG.ClassicalInvolution.PhanQ

open QuadraticMap CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution.PhanP
  CFSG.ClassicalInvolution.PhanD4 CFSG.ClassicalInvolution.PhanG

section Act

variable {F : Type} [Field F] {ε : F}

@[expose] noncomputable def NPair.act (g : spinGroup (quadPlus 4 F)) (z : NPair ε) : NPair ε where
  x := spinAction (quadPlus 4 F) g z.x
  y := spinAction (quadPlus 4 F) g z.y
  hx := (map_spinAction (quadPlus 4 F) g z.x).trans z.hx
  hy := (map_spinAction (quadPlus 4 F) g z.y).trans z.hy
  hxy := by
    have h := polar_spinAction (quadPlus 4 F) g z.x z.y
    exact h.trans z.hxy

noncomputable instance : SMul (spinGroup (quadPlus 4 F)) (NPair ε) := ⟨NPair.act⟩

theorem NPair.smul_x (g : spinGroup (quadPlus 4 F)) (z : NPair ε) :
    (g • z).x = spinAction (quadPlus 4 F) g z.x := rfl

theorem NPair.smul_y (g : spinGroup (quadPlus 4 F)) (z : NPair ε) :
    (g • z).y = spinAction (quadPlus 4 F) g z.y := rfl

theorem NPair.mul_smul' (g h : spinGroup (quadPlus 4 F)) (z : NPair ε) :
    (g * h) • z = g • (h • z) := by
  ext1
  · simp only [NPair.smul_x, map_mul, LinearEquiv.mul_apply]
  · simp only [NPair.smul_y, map_mul, LinearEquiv.mul_apply]

theorem NPair.one_smul' (z : NPair ε) : (1 : spinGroup (quadPlus 4 F)) • z = z := by
  ext1
  · simp only [NPair.smul_x, map_one]
    rfl
  · simp only [NPair.smul_y, map_one]
    rfl

theorem NPair.inv_smul_smul' (g : spinGroup (quadPlus 4 F)) (z : NPair ε) : g⁻¹ • (g • z) = z := by
  rw [← NPair.mul_smul', inv_mul_cancel, NPair.one_smul']

theorem NPair.smul_inv_smul' (g : spinGroup (quadPlus 4 F)) (z : NPair ε) : g • (g⁻¹ • z) = z := by
  rw [← NPair.mul_smul', mul_inv_cancel, NPair.one_smul']

theorem colP_smul (g : spinGroup (quadPlus 4 F)) {z w : NPair ε} :
    ColP ε (g • z) (g • w) ↔ ColP ε z w := by
  simp only [ColP, NPair.smul_x, NPair.smul_y, B8, polar_spinAction]

theorem smul_rot (hε : ε ≠ 0) (g : spinGroup (quadPlus 4 F)) (s t : F)
    (hst : s ^ 2 + t ^ 2 / ε = 1) (z : NPair ε) :
    g • (z.rot hε s t hst) = (g • z).rot hε s t hst := by
  ext1
  · simp only [NPair.smul_x, NPair.smul_y, NPair.rot_x, map_add, map_smul]
  · simp only [NPair.smul_x, NPair.smul_y, NPair.rot_y, map_add, map_smul]

end Act

section Base

variable {F : Type} [Field F]

@[expose] noncomputable def z0 (ε : F) : NPair ε where
  x := vecA1 F
  y := jOp ε (vecA1 F)
  hx := Q_vecA1
  hy := by
    have h := Q_comb_A ε 0 1
    simpa using h
  hxy := by
    have h := Q_comb_A ε 1 1
    have h1 : Q8 (vecA1 F + jOp ε (vecA1 F)) = 1 + ε := by
      simpa using h
    have h2 : Q8 (jOp ε (vecA1 F)) = ε := by
      have h' := Q_comb_A ε 0 1
      simpa using h'
    have h3 := Q8_lin (1 : F) 1 (vecA1 F) (jOp ε (vecA1 F))
    rw [one_smul, one_smul] at h3
    have hq : Q8 (vecA1 F) = 1 := Q_vecA1
    rw [h1, h2, hq] at h3
    linear_combination -h3

theorem z0_x (ε : F) : (z0 ε).x = vecA1 F := rfl

theorem z0_y (ε : F) : (z0 ε).y = jOp ε (vecA1 F) := rfl

end Base

section Stab

variable {F : Type} [Field F] {ε : F} {hε : ε ≠ 0} {h4 : (4 : F) ≠ 0}

theorem comb_mem_planeA (h2 : (2 : F) ≠ 0) (α β : F) :
    α • vecA1 F + β • jOp ε (vecA1 F) ∈ planeA ε hε h4 :=
  add_mem (Submodule.smul_mem _ _ (vecA1_mem_planeA ε hε h4))
    (Submodule.smul_mem _ _ (jOp_mem_planeA h2 (vecA1_mem_planeA ε hε h4)))

theorem exists_rot_of_stabJ (h2 : (2 : F) ≠ 0) {g : spinGroup (quadPlus 4 F)}
    (hg : g ∈ stabJ ε hε h4) :
    ∃ (s t : F) (hst : s ^ 2 + t ^ 2 / ε = 1), g • z0 ε = (z0 ε).rot hε s t hst := by
  obtain ⟨⟨⟨α, β⟩, hab⟩, hpr⟩ := exists_param_A h2 hg.1
  have hab' : α ^ 2 + ε * β ^ 2 = 1 := hab
  have hst : α ^ 2 + (-(ε * β)) ^ 2 / ε = 1 := by
    field_simp
    linear_combination hab'
  refine ⟨α, -(ε * β), hst, ?_⟩
  have hJ : spinAction (quadPlus 4 F) g (jOp ε (vecA1 F)) =
      jOp ε (spinAction (quadPlus 4 F) g (vecA1 F)) :=
    hg.2 _ (vecA1_mem_planeA ε hε h4)
  ext1
  · rw [NPair.smul_x, NPair.rot_x, z0_x, z0_y, hpr]
    have : -(-(ε * β) / ε) = β := by field_simp
    rw [this]
  · rw [NPair.smul_y, NPair.rot_y, z0_x, z0_y, hJ, hpr, map_add, map_smul, map_smul,
      jOp_jOp_vecA1]
    module

theorem act_mem_planeA_of_rot (h2 : (2 : F) ≠ 0) {g : spinGroup (quadPlus 4 F)} {s t : F}
    {hst : s ^ 2 + t ^ 2 / ε = 1} (h : g • z0 ε = (z0 ε).rot hε s t hst) {x : V8 F}
    (hx : x ∈ planeA ε hε h4) : spinAction (quadPlus 4 F) g x ∈ planeA ε hε h4 := by
  obtain ⟨α, β, rfl⟩ := exists_comb_of_mem_planeA h2 hx
  have h1 : spinAction (quadPlus 4 F) g (vecA1 F) = s • vecA1 F + (-(t / ε)) • jOp ε (vecA1 F) := by
    have := congrArg NPair.x h
    simpa [NPair.smul_x, NPair.rot_x, z0_x, z0_y] using this
  have h2' : spinAction (quadPlus 4 F) g (jOp ε (vecA1 F)) =
      t • vecA1 F + s • jOp ε (vecA1 F) := by
    have := congrArg NPair.y h
    simpa [NPair.smul_y, NPair.rot_y, z0_x, z0_y] using this
  rw [map_add, map_smul, map_smul, h1, h2']
  have : α • (s • vecA1 F + (-(t / ε)) • jOp ε (vecA1 F)) +
      β • (t • vecA1 F + s • jOp ε (vecA1 F)) =
      (α * s + β * t) • vecA1 F + (α * (-(t / ε)) + β * s) • jOp ε (vecA1 F) := by module
  rw [this]
  exact comb_mem_planeA h2 _ _

theorem inv_smul_z0_of_rot (hε : ε ≠ 0) {g : spinGroup (quadPlus 4 F)} {s t : F}
    {hst : s ^ 2 + t ^ 2 / ε = 1} (hst' : s ^ 2 + (-t) ^ 2 / ε = 1)
    (h : g • z0 ε = (z0 ε).rot hε s t hst) : g⁻¹ • z0 ε = (z0 ε).rot hε s (-t) hst' := by
  have h1 : g⁻¹ • (g • z0 ε) = g⁻¹ • ((z0 ε).rot hε s t hst) := by rw [h]
  rw [NPair.inv_smul_smul', smul_rot] at h1
  conv_rhs => rw [h1]
  rw [NPair.rot_rot_neg]

theorem mem_stabJ_of_rot (h2 : (2 : F) ≠ 0) (hε : ε ≠ 0) {g : spinGroup (quadPlus 4 F)} {s t : F}
    {hst : s ^ 2 + t ^ 2 / ε = 1} (h : g • z0 ε = (z0 ε).rot hε s t hst) :
    g ∈ stabJ ε hε h4 := by
  have hst' : s ^ 2 + (-t) ^ 2 / ε = 1 := by rw [neg_sq]; exact hst
  have hinv := inv_smul_z0_of_rot hε hst' h
  refine ⟨fun x => ⟨fun hx => ?_, fun hx => act_mem_planeA_of_rot h2 h hx⟩, fun x hx => ?_⟩
  · have := act_mem_planeA_of_rot (h4 := h4) h2 hinv hx
    have key : spinAction (quadPlus 4 F) g⁻¹ (spinAction (quadPlus 4 F) g x) = x := by
      rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
      rfl
    rwa [key] at this
  · obtain ⟨α, β, rfl⟩ := exists_comb_of_mem_planeA h2 hx
    have h1 : spinAction (quadPlus 4 F) g (vecA1 F) =
        s • vecA1 F + (-(t / ε)) • jOp ε (vecA1 F) := by
      have := congrArg NPair.x h
      simpa [NPair.smul_x, NPair.rot_x, z0_x, z0_y] using this
    have h2' : spinAction (quadPlus 4 F) g (jOp ε (vecA1 F)) =
        t • vecA1 F + s • jOp ε (vecA1 F) := by
      have := congrArg NPair.y h
      simpa [NPair.smul_y, NPair.rot_y, z0_x, z0_y] using this
    simp only [map_add, map_smul, h1, h2', jOp_jOp_vecA1]
    match_scalars <;> field_simp

end Stab

end CFSG.ClassicalInvolution.PhanQ
