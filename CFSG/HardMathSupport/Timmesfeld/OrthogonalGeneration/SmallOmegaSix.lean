module

public import CFSG.Open.StatedDefs
public import CFSG.ClassicalGroups.Orthogonal.CharTwoTransvection
public import CFSG.ClassicalGroups.Orthogonal.Matrix
public import CFSG.LieType.Universal.Spin.Forms

public section
namespace CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration
open CFSG.Open Matrix
namespace SmallOmegaSix

abbrev ι6 : Type := Fin 3 ⊕ Fin 3
abbrev Q6 : (ι6 → ZMod 2) → ZMod 2 := StatedQuadPlus 3 (ZMod 2)

@[expose] def Emat : Fin 3 → Fin 8 → ZMod 2 :=
  ![![1,1,1,1,0,0,0,0], ![1,1,0,0,1,1,0,0], ![1,0,1,0,1,0,1,0]]
@[expose] def Gmat : Fin 3 → Fin 8 → ZMod 2 :=
  ![![0,1,1,1,1,0,0,0], ![1,0,0,1,1,1,0,0], ![0,1,0,1,0,1,1,0]]

@[expose] def Fm : Matrix (Fin 8) ι6 (ZMod 2) :=
  Matrix.of fun k a => Sum.elim (fun i => Emat i k) (fun i => Gmat i k) a
@[expose] def Tm : Matrix ι6 (Fin 8) (ZMod 2) :=
  Matrix.of fun a k => Sum.elim (fun i => Gmat i k) (fun i => Emat i k) a
@[expose] def Pm (σ : Equiv.Perm (Fin 8)) : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  Matrix.of fun i j => if σ⁻¹ i = j then 1 else 0

@[expose] def one8 : Fin 8 → ZMod 2 := fun _ => 1

theorem TF : Tm * Fm = 1 := by decide +kernel
theorem T_one : Tm *ᵥ one8 = 0 := by decide +kernel
theorem F_even : ∀ v : ι6 → ZMod 2, ∑ k, (Fm *ᵥ v) k = 0 := by decide +kernel
theorem FT : ∀ w : Fin 8 → ZMod 2, ∑ k, w k = 0 →
    Fm *ᵥ (Tm *ᵥ w) = w ∨ Fm *ᵥ (Tm *ᵥ w) = w + one8 := by decide +kernel

theorem Pm_mulVec (σ : Equiv.Perm (Fin 8)) (w : Fin 8 → ZMod 2) :
    Pm σ *ᵥ w = fun i => w (σ⁻¹ i) := by
  ext i
  simp [Pm, Matrix.mulVec, dotProduct]

theorem Pm_mul (σ τ : Equiv.Perm (Fin 8)) : Pm (σ * τ) = Pm σ * Pm τ := by
  rw [Matrix.ext_iff_mulVec]
  intro w
  rw [← Matrix.mulVec_mulVec, Pm_mulVec, Pm_mulVec, Pm_mulVec]
  ext i
  simp [_root_.mul_inv_rev]

theorem Pm_one : Pm 1 = 1 := by
  ext i j
  simp [Pm, Matrix.one_apply]

theorem Pm_one8 (σ : Equiv.Perm (Fin 8)) : Pm σ *ᵥ one8 = one8 := by
  rw [Pm_mulVec]; rfl

theorem Pm_sum (σ : Equiv.Perm (Fin 8)) (w : Fin 8 → ZMod 2) :
    ∑ k, (Pm σ *ᵥ w) k = ∑ k, w k := by
  rw [Pm_mulVec]
  exact Equiv.sum_comp σ⁻¹ w

@[expose] def Mm (σ : Equiv.Perm (Fin 8)) : Matrix ι6 ι6 (ZMod 2) := Tm * Pm σ * Fm

theorem Mm_mulVec (σ : Equiv.Perm (Fin 8)) (v : ι6 → ZMod 2) :
    Mm σ *ᵥ v = Tm *ᵥ (Pm σ *ᵥ (Fm *ᵥ v)) := by
  simp [Mm, Matrix.mulVec_mulVec, Matrix.mul_assoc]

theorem Mm_one : Mm 1 = 1 := by
  rw [Mm, Pm_one, Matrix.mul_one, TF]

theorem Mm_mul (σ τ : Equiv.Perm (Fin 8)) : Mm (σ * τ) = Mm σ * Mm τ := by
  rw [Matrix.ext_iff_mulVec]
  intro v
  rw [← Matrix.mulVec_mulVec, Mm_mulVec, Mm_mulVec, Mm_mulVec, Pm_mul, ← Matrix.mulVec_mulVec]
  have hw := Pm_sum τ (Fm *ᵥ v)
  rw [F_even] at hw
  rcases FT _ hw with h | h
  · rw [h]
  · rw [h, Matrix.mulVec_add, Pm_one8, Matrix.mulVec_add, T_one, add_zero]

@[expose] def Jm : Matrix ι6 ι6 (ZMod 2) :=
  Matrix.of fun a b => Sum.elim (fun i => Sum.elim (fun _ => 0) (fun j => if i = j then 1 else 0) b)
    (fun i => Sum.elim (fun j => if i = j then 1 else 0) (fun _ => 0) b) a

@[expose] def polar6 (v w : ι6 → ZMod 2) : ZMod 2 := v ⬝ᵥ (Jm *ᵥ w)

theorem polar6_eq (v w : ι6 → ZMod 2) :
    polar6 v w = ∑ i : Fin 3, (v (.inl i) * w (.inr i) + w (.inl i) * v (.inr i)) := by
  revert v w
  decide +kernel

@[expose] def pairvec (i j : Fin 8) : Fin 8 → ZMod 2 :=
  fun k => (if k = i then 1 else 0) + (if k = j then 1 else 0)

@[expose] def uvec (i j : Fin 8) : ι6 → ZMod 2 := Tm *ᵥ pairvec i j

theorem swap_matrix : ∀ i j : Fin 8, i ≠ j →
    Mm (Equiv.swap i j) = 1 + Matrix.vecMulVec (uvec i j) (Jm *ᵥ uvec i j) := by
  decide +kernel

theorem swap_formula (i j : Fin 8) (h : i ≠ j) (v : ι6 → ZMod 2) :
    Mm (Equiv.swap i j) *ᵥ v = v + polar6 v (uvec i j) • uvec i j := by
  rw [swap_matrix i j h, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.vecMulVec_mulVec, polar6,
    dotProduct_comm, IsCentralScalar.op_smul_eq_smul]

theorem Q6_uvec : ∀ i j : Fin 8, i ≠ j → Q6 (uvec i j) = 1 := by decide +kernel

theorem uvec_surj : ∀ v : ι6 → ZMod 2, Q6 v = 1 → ∃ i j : Fin 8, i ≠ j ∧ uvec i j = v := by
  decide +kernel

theorem uvec_inj : ∀ a b c d : Fin 8, a ≠ b → c ≠ d → uvec a b = uvec c d →
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by decide +kernel

theorem Mm_pair (σ : Equiv.Perm (Fin 8)) (i j : Fin 8) :
    Mm σ *ᵥ uvec i j = uvec (σ i) (σ j) := by
  have hp : ∑ k, pairvec i j k = 0 := by
    simp only [pairvec, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    decide
  have hP : Pm σ *ᵥ pairvec i j = pairvec (σ i) (σ j) := by
    rw [Pm_mulVec]
    ext k
    simp [pairvec, Equiv.symm_apply_eq]
  rw [Mm_mulVec, uvec, uvec, ← hP]
  rcases FT _ hp with h | h
  · rw [h]
  · rw [h, Matrix.mulVec_add, Pm_one8, Matrix.mulVec_add, T_one, add_zero]

theorem Mm_eq_one_imp (σ : Equiv.Perm (Fin 8)) (h : Mm σ = 1) : σ = 1 := by
  have hpair : ∀ i j : Fin 8, i ≠ j → (σ i = i ∧ σ j = j) ∨ (σ i = j ∧ σ j = i) := by
    intro i j hij
    have h1 := Mm_pair σ i j
    rw [h, Matrix.one_mulVec] at h1
    exact uvec_inj _ _ _ _ (σ.injective.ne hij) hij h1.symm
  have key : ∀ i x : Fin 8, (x = i ∨ x = i + 1) → (x = i ∨ x = i + 2) → x = i := by decide
  have hne1 : ∀ i : Fin 8, i ≠ i + 1 := by decide
  have hne2 : ∀ i : Fin 8, i ≠ i + 2 := by decide
  refine Equiv.ext fun i => ?_
  have h1 := hpair i (i + 1) (hne1 i)
  have h2 := hpair i (i + 2) (hne2 i)
  have h1' : σ i = i ∨ σ i = i + 1 := by tauto
  have h2' : σ i = i ∨ σ i = i + 2 := by tauto
  exact key i _ h1' h2'

@[expose] def psi0 : Equiv.Perm (Fin 8) →* Matrix ι6 ι6 (ZMod 2) where
  toFun := Mm
  map_one' := Mm_one
  map_mul' := Mm_mul

@[expose] def psi : Equiv.Perm (Fin 8) →* GL ι6 (ZMod 2) := psi0.toHomUnits

theorem psi_val (σ : Equiv.Perm (Fin 8)) : ((psi σ : GL ι6 (ZMod 2)) : Matrix ι6 ι6 (ZMod 2)) = Mm σ :=
  rfl

theorem psi_injective : Function.Injective psi := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro σ hσ
  rw [MonoidHom.mem_ker] at hσ
  rw [Subgroup.mem_bot]
  apply Mm_eq_one_imp
  have := congrArg (fun A : GL ι6 (ZMod 2) => (A : Matrix ι6 ι6 (ZMod 2))) hσ
  simpa [psi_val] using this

theorem Q6_transvection : ∀ u : ι6 → ZMod 2, Q6 u = 1 → ∀ v : ι6 → ZMod 2,
    Q6 (v + polar6 v u • u) = Q6 v := by decide +kernel

@[expose] def O6 : Subgroup (GL ι6 (ZMod 2)) :=
  Subgroup.closure {A : GL ι6 (ZMod 2) | ∀ v, Q6 ((A : Matrix ι6 ι6 (ZMod 2)) *ᵥ v) = Q6 v}

theorem statedOmega_eq : StatedOmega Q6 = ⁅O6, O6⁆ := rfl

theorem mem_O6 {A : GL ι6 (ZMod 2)} :
    A ∈ O6 ↔ ∀ v, Q6 ((A : Matrix ι6 ι6 (ZMod 2)) *ᵥ v) = Q6 v := by
  have h := CFSG.ClassicalGroups.Orthogonal.closure_isometries_eq_comap
    (Q := CFSG.LieType.Universal.Spin.quadPlus 3 (ZMod 2)) (Q₀ := Q6)
    (CFSG.LieType.Universal.Spin.coe_quadPlus 3 (ZMod 2))
  show A ∈ Subgroup.closure _ ↔ _
  have e : ∀ v, CFSG.LieType.Universal.Spin.quadPlus 3 (ZMod 2) v = Q6 v :=
    fun v => congrFun (CFSG.LieType.Universal.Spin.coe_quadPlus 3 (ZMod 2)) v
  rw [h, Subgroup.mem_comap, TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  simp only [MulEquiv.coe_toMonoidHom, CFSG.ClassicalGroups.Orthogonal.toLinEquiv_apply, e]

theorem psi_mem_O6 (σ : Equiv.Perm (Fin 8)) : psi σ ∈ O6 := by
  have : (⊤ : Subgroup (Equiv.Perm (Fin 8))) ≤ O6.comap psi := by
    rw [← Equiv.Perm.closure_isSwap, Subgroup.closure_le]
    rintro _ ⟨i, j, hij, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, mem_O6]
    intro v
    rw [psi_val, swap_formula i j hij]
    exact Q6_transvection _ (Q6_uvec i j hij) v
  exact this (Subgroup.mem_top σ)

section Abstract

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG.ClassicalGroups.Orthogonal QuadraticMap Module in
theorem O6_le_range (A : GL ι6 (ZMod 2)) (hA : A ∈ O6) : A ∈ psi.range := by
  have e : ∀ v, CFSG.LieType.Universal.Spin.quadPlus 3 (ZMod 2) v = Q6 v :=
    fun v => congrFun (CFSG.LieType.Universal.Spin.coe_quadPlus 3 (ZMod 2)) v
  have hQ : (polarBilin (CFSG.LieType.Universal.Spin.quadPlus 3 (ZMod 2))).Nondegenerate :=
    CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadPlus 3 (ZMod 2)
  have hdim : finrank (ZMod 2) (Fin 3 ⊕ Fin 3 → ZMod 2) = 6 := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp [Fintype.card_sum]
  have hgen := orthogonalGroup_eq_closure_reflect hQ (by omega) (Or.inl (by omega))
  let H : Subgroup ((ι6 → ZMod 2) ≃ₗ[ZMod 2] (ι6 → ZMod 2)) :=
    psi.range.map (toLinEquiv ι6 (ZMod 2)).toMonoidHom
  have hle : TauCeti.QuadraticMap.orthogonalGroup (CFSG.LieType.Universal.Spin.quadPlus 3 (ZMod 2))
      ≤ H := by
    rw [hgen, Subgroup.closure_le]
    rintro _ ⟨v, rfl⟩
    rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) (CFSG.LieType.Universal.Spin.quadPlus 3 (ZMod 2) v) with h0 | h1
    · rw [SetLike.mem_coe, reflect_of_map_eq_zero h0]
      exact one_mem _
    · obtain ⟨i, j, hij, huv⟩ := uvec_surj v (by rw [← e]; exact h1)
      refine ⟨psi (Equiv.swap i j), ⟨_, rfl⟩, ?_⟩
      ext x
      rw [MulEquiv.coe_toMonoidHom, toLinEquiv_apply, psi_val, swap_formula i j hij,
        reflect_apply_of_map_eq_one h1, huv, CFSG.LieType.Universal.Spin.polar_quadPlus, polar6_eq]
  have hA' : toLinEquiv ι6 (ZMod 2) A ∈ TauCeti.QuadraticMap.orthogonalGroup
      (CFSG.LieType.Universal.Spin.quadPlus 3 (ZMod 2)) := by
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro v
    rw [toLinEquiv_apply, e, e]
    exact mem_O6.1 hA v
  obtain ⟨s, hs, hsA⟩ := hle hA'
  have := (toLinEquiv ι6 (ZMod 2)).injective hsA
  rw [← this]
  exact hs

end Abstract

@[expose] def psiO : Equiv.Perm (Fin 8) →* O6 := psi.codRestrict O6 psi_mem_O6

theorem psiO_bijective : Function.Bijective psiO := by
  refine ⟨?_, ?_⟩
  · intro σ τ h
    exact psi_injective (congrArg (fun x : O6 => (x : GL ι6 (ZMod 2))) h)
  · intro A
    obtain ⟨σ, hσ⟩ := O6_le_range A A.2
    exact ⟨σ, Subtype.ext hσ⟩

@[expose] noncomputable def o6MulEquivPerm : Equiv.Perm (Fin 8) ≃* O6 :=
  MulEquiv.ofBijective psiO psiO_bijective

end SmallOmegaSix

open SmallOmegaSix in
@[expose] noncomputable def statedOmega_quadPlus_three_mulEquiv_alt8 :
    ↥(StatedOmega (StatedQuadPlus 3 (ZMod 2))) ≃* ↥(alternatingGroup (Fin 8)) := by
  have h1 : Subgroup.map O6.subtype (⁅(⊤ : Subgroup O6), (⊤ : Subgroup O6)⁆) =
      StatedOmega Q6 := by
    rw [statedOmega_eq, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
  have h2 : Subgroup.map o6MulEquivPerm.symm.toMonoidHom (⁅(⊤ : Subgroup O6), (⊤ : Subgroup O6)⁆) =
      alternatingGroup (Fin 8) := by
    have htop : o6MulEquivPerm.symm.toMonoidHom.range = ⊤ :=
      MonoidHom.range_eq_top.2 o6MulEquivPerm.symm.surjective
    rw [Subgroup.map_commutator, Subgroup.map_top, htop]
    exact alternatingGroup.commutator_perm_eq (by simp)
  exact ((MulEquiv.subgroupCongr h1.symm).trans
    (Subgroup.equivMapOfInjective _ O6.subtype O6.subtype_injective).symm).trans
    ((MulEquiv.subgroupMap o6MulEquivPerm.symm _).trans (MulEquiv.subgroupCongr h2))

theorem card_alternatingGroup_eight : Nat.card ↥(alternatingGroup (Fin 8)) = 20160 := by
  rw [nat_card_alternatingGroup]
  simp [Nat.factorial]

theorem card_statedOmega_quadPlus_three :
    Nat.card ↥(StatedOmega (StatedQuadPlus 3 (ZMod 2))) = 20160 := by
  rw [Nat.card_congr statedOmega_quadPlus_three_mulEquiv_alt8.toEquiv]
  exact card_alternatingGroup_eight

theorem isSimpleGroup_statedOmega_quadPlus_three :
    IsSimpleGroup ↥(StatedOmega (StatedQuadPlus 3 (ZMod 2))) :=
  have : IsSimpleGroup ↥(alternatingGroup (Fin 8)) := alternatingGroup.isSimpleGroup (by simp)
  statedOmega_quadPlus_three_mulEquiv_alt8.isSimpleGroup

end CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration
