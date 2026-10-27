module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotFusionNotTransvectionCore

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag

variable {n : ℕ} {K : Type*} [Field K]

section Root

@[expose] def xab {a b : Fin n} (hab : a ≠ b) (c : K) : projectiveSL n K :=
  proj n K (SpecialLinearGroup.transvection hab c)

theorem xab_def {a b : Fin n} (hab : a ≠ b) (c : K) :
    xab hab c = proj n K (SpecialLinearGroup.transvection hab c) :=
  rfl

theorem xab_add {a b : Fin n} (hab : a ≠ b) (c d : K) :
    xab hab (c + d) = xab hab c * xab hab d := by
  rw [xab, SpecialLinearGroup.transvection_add, map_mul]
  rfl

@[simp]
theorem xab_zero {a b : Fin n} (hab : a ≠ b) : xab (K := K) hab 0 = 1 := by
  rw [xab, SpecialLinearGroup.transvection_coeff_zero, map_one]

theorem xab_mem_blockSL {I : Finset (Fin n)} {a b : Fin n} (hab : a ≠ b) (ha : a ∈ I)
    (hb : b ∈ I) (c : K) : xab hab c ∈ blockSL I :=
  proj_transvection_mem_blockSL hab ha hb c

theorem xab_mem_rootSL2 {a b : Fin n} (hab : a ≠ b) (c : K) : xab hab c ∈ rootSL2 a b :=
  proj_transvection_mem_rootSL2 hab c

@[expose] def rootGroup {a b : Fin n} (hab : a ≠ b) : Subgroup (projectiveSL n K) :=
  ((proj n K).comp (SpecialLinearGroup.transvectionHom hab)).range

theorem mem_rootGroup {a b : Fin n} (hab : a ≠ b) {x : projectiveSL n K} :
    x ∈ rootGroup hab ↔ ∃ c : K, xab hab c = x := by
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨Multiplicative.toAdd c, by
      rw [MonoidHom.comp_apply, SpecialLinearGroup.transvectionHom_apply, xab]⟩
  · rintro ⟨c, rfl⟩
    exact ⟨Multiplicative.ofAdd c, by
      rw [MonoidHom.comp_apply, SpecialLinearGroup.transvectionHom_apply, toAdd_ofAdd, xab]⟩

theorem xab_mem_rootGroup {a b : Fin n} (hab : a ≠ b) (c : K) : xab hab c ∈ rootGroup hab :=
  (mem_rootGroup hab).2 ⟨c, rfl⟩

theorem rootGroup_le_blockSL {I : Finset (Fin n)} {a b : Fin n} (hab : a ≠ b) (ha : a ∈ I)
    (hb : b ∈ I) : rootGroup (K := K) hab ≤ blockSL I := by
  intro x hx
  obtain ⟨c, rfl⟩ := (mem_rootGroup hab).1 hx
  exact xab_mem_blockSL hab ha hb c

end Root

section Placement

theorem InvPlacement.mat_eq_transvection (P : InvPlacement n 1) :
    P.mat K = SpecialLinearGroup.transvection (P.u_ne_w 0 0) 1 := by
  ext i j
  rw [InvPlacement.coe_mat, SpecialLinearGroup.transvection_coe, Matrix.add_apply,
    Matrix.add_apply, single_apply]
  congr 1
  simp only [InvPlacement.nil, Matrix.of_apply, Fin.exists_fin_one]

@[expose] def pairPlacement {a b : Fin n} (hab : a ≠ b) : InvPlacement n 1 :=
  InvPlacement.ofFun (fun _ => a) (fun _ => b) (fun x y _ => Subsingleton.elim x y)
    (fun x y _ => Subsingleton.elim x y) (fun _ _ => hab)

theorem pairPlacement_mat {a b : Fin n} (hab : a ≠ b) :
    (pairPlacement hab).mat K = SpecialLinearGroup.transvection hab 1 :=
  (pairPlacement hab).mat_eq_transvection

theorem pairPlacement_elt {a b : Fin n} (hab : a ≠ b) :
    (pairPlacement hab).elt K = xab hab 1 := by
  rw [InvPlacement.elt, pairPlacement_mat]
  rfl

theorem pairPlacement_level_left {a b : Fin n} (hab : a ≠ b) : (pairPlacement hab).level a = 0 :=
  (pairPlacement hab).level_u 0

theorem pairPlacement_level_right {a b : Fin n} (hab : a ≠ b) :
    (pairPlacement hab).level b = 2 :=
  (pairPlacement hab).level_w 0

theorem pairPlacement_level_of_ne {a b i : Fin n} (hab : a ≠ b) (hia : i ≠ a) (hib : i ≠ b) :
    (pairPlacement hab).level i = 1 :=
  (pairPlacement hab).level_eq_one_iff.2
    ⟨fun _ h => hia h.symm, fun _ h => hib h.symm⟩

theorem pairPlacement_free {a b : Fin n} (hab : a ≠ b) :
    (pairPlacement hab).free = ({a, b} : Finset (Fin n))ᶜ := by
  ext i
  rw [InvPlacement.mem_free, InvPlacement.level_eq_one_iff, Finset.mem_compl, Finset.mem_insert,
    Finset.mem_singleton, not_or]
  constructor
  · rintro ⟨hu, hw⟩
    exact ⟨fun h => hu 0 h.symm, fun h => hw 0 h.symm⟩
  · rintro ⟨ha, hb⟩
    exact ⟨fun _ h => ha h.symm, fun _ h => hb h.symm⟩

theorem isInvolutionClass_one_xab [CharP K 2] {a b : Fin n} (hab : a ≠ b) :
    IsInvolutionClass 1 (xab (K := K) hab 1) := by
  refine ⟨(pairPlacement hab).mat K, by rw [pairPlacement_mat]; rfl,
    (pairPlacement hab).mat_mul_self, ?_⟩
  rw [InvPlacement.coe_mat, add_sub_cancel_left]
  exact rank_nilOf (K := K) (u := fun _ : Fin 1 => a) (w := fun _ : Fin 1 => b)
    (fun x y _ => Subsingleton.elim x y) (fun x y _ => Subsingleton.elim x y)

end Placement

section Conj

theorem permMatrix_mul_transvection (ρ : Equiv.Perm (Fin n)) (i j : Fin n) (c : K) :
    ρ.permMatrix K * Matrix.transvection i j c =
      Matrix.transvection (ρ.symm i) (ρ.symm j) c * ρ.permMatrix K := by
  ext k l
  simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv,
    submatrix_apply, id, Matrix.transvection, Matrix.add_apply, Matrix.one_apply, single_apply,
    Equiv.symm_apply_eq, Equiv.eq_symm_apply, Equiv.apply_symm_apply]

theorem transvection_congr {i j i' j' : Fin n} (hij : i ≠ j) (hij' : i' ≠ j') (hi : i = i')
    (hj : j = j') (c : K) :
    SpecialLinearGroup.transvection hij c = SpecialLinearGroup.transvection hij' c := by
  subst hi hj
  rfl

variable [CharP K 2]

@[expose] def permSL (ρ : Equiv.Perm (Fin n)) : SpecialLinearGroup (Fin n) K :=
  ⟨ρ.permMatrix K, by
    rw [det_permutation]
    rcases Int.units_eq_one_or (Equiv.Perm.sign ρ) with h | h <;> simp [h, CharTwo.neg_eq]⟩

theorem coe_permSL (ρ : Equiv.Perm (Fin n)) :
    ((permSL ρ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) = ρ.permMatrix K :=
  rfl

theorem permSL_mul_transvection_mul_inv (ρ : Equiv.Perm (Fin n)) {i j : Fin n} (hij : i ≠ j)
    (c : K) :
    permSL ρ * SpecialLinearGroup.transvection hij c * (permSL ρ)⁻¹ =
      SpecialLinearGroup.transvection (ρ.symm.injective.ne hij) c := by
  rw [mul_inv_eq_iff_eq_mul]
  exact Subtype.ext (permMatrix_mul_transvection ρ i j c)

theorem exists_conj_xab_eq_xab {i j a b : Fin n} (hij : i ≠ j) (hab : a ≠ b) (c : K) :
    ∃ g : projectiveSL n K, g * xab hij c * g⁻¹ = xab hab c := by
  obtain ⟨ρ, hρa, hρb⟩ := exists_perm_apply_eq_apply_eq hab hij
  refine ⟨proj n K (permSL ρ), ?_⟩
  rw [xab, xab, ← map_inv, ← map_mul, ← map_mul, permSL_mul_transvection_mul_inv,
    transvection_congr _ hab (by rw [← hρa, Equiv.symm_apply_apply])
      (by rw [← hρb, Equiv.symm_apply_apply])]

theorem exists_conj_eq_xab [Finite K] {a b : Fin n} (hab : a ≠ b) {z : projectiveSL n K}
    (hz : IsInvolutionClass 1 z) : ∃ c : projectiveSL n K, c * z * c⁻¹ = xab hab 1 := by
  obtain ⟨P, c₁, hc₁⟩ := exists_conj_eq_elt_of_isInvolutionClass_one hz
  obtain ⟨c₂, hc₂⟩ := exists_conj_xab_eq_xab (P.u_ne_w 0 0) hab (1 : K)
  refine ⟨c₂ * c₁, ?_⟩
  have hP : P.elt K = xab (P.u_ne_w 0 0) 1 := by
    rw [InvPlacement.elt, P.mat_eq_transvection]
    rfl
  rw [← hc₂, ← hP, ← hc₁]
  group

end Conj

section Fusion

variable {G : Type*} [Group G] {L : Subgroup G}

theorem exists_conj_eq_mul_xab [Finite K] [CharP K 2] (e : L ≃* projectiveSL n K) {t : G}
    (hLt : L ≤ centralizer ({t} : Set G)) {a b : Fin n} (hab : a ≠ b)
    (h : ∃ (g : G) (z : L), IsInvolutionClass 1 (e z) ∧ g⁻¹ * t * g = t * (z : G)) :
    ∃ g : G, g⁻¹ * t * g = t * ((e.symm (xab hab 1) : L) : G) := by
  obtain ⟨g, z, hz, hgz⟩ := h
  obtain ⟨c, hc⟩ := exists_conj_eq_xab hab hz
  set m : L := e.symm c with hm
  have hmz : m * z * m⁻¹ = e.symm (xab hab 1) := by
    rw [← hc, map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply]
  have hmt : (m : G) * t = t * m := mem_centralizer_singleton_iff.1 (hLt m.2)
  refine ⟨g * (m : G)⁻¹, ?_⟩
  rw [← hmz]
  calc (g * (m : G)⁻¹)⁻¹ * t * (g * (m : G)⁻¹) = m * (g⁻¹ * t * g) * (m : G)⁻¹ := by group
    _ = m * t * z * (m : G)⁻¹ := by rw [hgz, mul_assoc (m : G) t]
    _ = t * ((m * z * m⁻¹ : L) : G) := by
      rw [hmt]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group

theorem exists_conj_eq_mul_xab' [Finite K] [CharP K 2] (e : L ≃* projectiveSL n K) {t : G}
    (hLt : L ≤ centralizer ({t} : Set G)) {a b : Fin n} (hab : a ≠ b)
    (h : ∃ (g : G) (z : L), IsInvolutionClass 1 (e z) ∧ g⁻¹ * t * g = t * (z : G)) :
    ∃ (g : G) (y : L), e y = xab hab 1 ∧ IsInvolutionClass 1 (e y) ∧ e y ∈ rootSL2 a b ∧
      g⁻¹ * t * g = t * (y : G) := by
  obtain ⟨g, hg⟩ := exists_conj_eq_mul_xab e hLt hab h
  refine ⟨g, e.symm (xab hab 1), e.apply_symm_apply _, ?_, ?_, hg⟩
  · rw [e.apply_symm_apply]
    exact isInvolutionClass_one_xab hab
  · rw [e.apply_symm_apply]
    exact xab_mem_rootSL2 hab 1

end Fusion

end CFSG.SeitzReduction.LinearPilot
