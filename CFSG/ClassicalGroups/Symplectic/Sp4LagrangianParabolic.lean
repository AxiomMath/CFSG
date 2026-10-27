module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherSylow
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticSixCoverModel
public import CFSG.LinearAlgebra.SL2CharTwoInvolution
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixCoverModel

public section

namespace CFSG.ClassicalGroups.Symplectic.Sp4

open Matrix Subgroup CFSG.Open
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl

variable {K : Type} [Field K]

theorem unipotent_fixed_eq_smul (v : Fin 2 ⊕ Fin 2 → K)
    (hv : ∀ g ∈ unipotent 2 K, ((g : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v = v) :
    v = v (Sum.inl 0) • Pi.single (Sum.inl 0) (1 : K) := by
  have h : v ∈ (flag 2 K 1 : Set (Fin 2 ⊕ Fin 2 → K)) := by
    rw [← (SymplecticHigher.unitriangular_invariant_isotropic_subspaces (r := 2) (K := K)).1]
    exact hv
  obtain ⟨hf, he⟩ := mem_isoFlag.mp ((mem_flag_of_le (by norm_num)).mp h)
  funext i
  rcases i with j | j <;> fin_cases j <;> simp [hf, he 1 (by simp)]

theorem torusHom_mulVec_e1 (β : Kˣ) :
    (((torusHom (r := 2) (k := K) (Pi.mulSingle (1 : Fin 2) β) : StatedSp 2 K) :
        GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
      Pi.single (Sum.inl 0) (1 : K) = Pi.single (Sum.inl 0) (1 : K) := by
  rw [coe_torusHom]
  funext x
  rw [Matrix.mulVec_diagonal]
  by_cases hx : x = Sum.inl 0
  · subst hx
    simp [Pi.mulSingle]
  · simp [Pi.single_eq_of_ne hx]

theorem pairMat_mulVec_single_of_ne {ι : Type*} [Fintype ι] [DecidableEq ι]
    {a b c : ι} (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b) (g : Matrix (Fin 2) (Fin 2) K) :
    pairMat a b g *ᵥ Pi.single c (1 : K) = Pi.single c (1 : K) := by
  funext x
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single c]
  · by_cases hx : x = c
    · subst hx
      rw [Pi.single_eq_same, mul_one, pairMat_apply_of_ne hca hcb, one_apply_eq]
    · rw [Pi.single_eq_same, mul_one, Pi.single_eq_of_ne hx]
      by_cases hxa : x = a
      · subst hxa
        rw [pairMat_apply_fst_of_ne hca hcb]
      by_cases hxb : x = b
      · subst hxb
        rw [pairMat_apply_snd_of_ne hab hca hcb]
      · rw [pairMat_apply_of_ne hxa hxb]
        simp [hx]
  · intro y _ hyc
    rw [Pi.single_eq_of_ne hyc, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ c) h

theorem lam_sl2W_mulVec_e1 :
    ((((lam (1 : Fin 2) (sl2W (k := K))) : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
      Pi.single (Sum.inl 0) (1 : K) = Pi.single (Sum.inl 0) (1 : K) := by
  rw [coe_lam]
  exact pairMat_mulVec_single_of_ne (by simp) (by simp) (by simp) _

theorem torusHom_mem_normalizer_unipotent (t : Fin 2 → Kˣ) :
    torusHom (r := 2) (k := K) t ∈ normalizer (unipotent 2 K : Set (StatedSp 2 K)) := by
  rw [SymplecticHigher.normalizer_unipotent]
  exact torus_le_borelSubgroup ⟨t, rfl⟩

theorem orderOf_torusHom_mulSingle (i : Fin 2) (β : Kˣ) :
    orderOf (torusHom (r := 2) (k := K) (Pi.mulSingle i β)) = orderOf β := by
  rw [orderOf_injective (torusHom (r := 2) (k := K)) torusHom_injective, orderOf_piMulSingle]

theorem commute_lam_torusHom_mulSingle {i j : Fin 2} (hij : i ≠ j)
    (g : SpecialLinearGroup (Fin 2) K) (β : Kˣ) :
    Commute (lam i g) (torusHom (r := 2) (k := K) (Pi.mulSingle j β)) := by
  rw [← lam_sl2Diag]
  exact commute_lam_lam hij g _

theorem lam_zero_range_le_centralizer (β : Kˣ) :
    (lam (0 : Fin 2) : SpecialLinearGroup (Fin 2) K →* StatedSp 2 K).range ≤
      Subgroup.centralizer ({torusHom (r := 2) (k := K) (Pi.mulSingle (1 : Fin 2) β)} :
        Set (StatedSp 2 K)) := by
  rintro _ ⟨g, rfl⟩
  exact Subgroup.mem_centralizer_singleton_iff.mpr
    (commute_lam_torusHom_mulSingle (i := 0) (j := 1) (by decide) g β)

@[expose] noncomputable def lagrangianLeviSL : Subgroup (StatedSp 2 K) :=
  ((leviSp (r := 2) (k := K)).comp
    (Matrix.SpecialLinearGroup.toGL (n := Fin 2) (R := K))).range

theorem leviSp_eq_lam_of_coe_eq_unitri (a : K) (A : Matrix.SpecialLinearGroup (Fin 2) K)
    (ha : (A : Matrix (Fin 2) (Fin 2) K) = SymplecticFour.unitri a) :
    leviSp (r := 2) (k := K) (Matrix.SpecialLinearGroup.toGL A) = SymplecticFour.lam a := by
  apply statedSp_ext
  rw [coe_leviSp, SymplecticFour.coe_lam, fromBlocks_inj]
  refine ⟨?_, rfl, rfl, ?_⟩
  · rw [show ((Matrix.SpecialLinearGroup.toGL A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      (A : Matrix (Fin 2) (Fin 2) K) from rfl, ha]
  · rw [show (((Matrix.SpecialLinearGroup.toGL A)⁻¹ : GL (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) = Matrix.adjugate (A : Matrix (Fin 2) (Fin 2) K) from by
      rw [← map_inv]
      exact Matrix.SpecialLinearGroup.coe_inv A]
    rw [ha, Matrix.adjugate_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [SymplecticFour.unitri]

theorem lam_mem_lagrangianLeviSL (a : K) :
    SymplecticFour.lam a ∈ lagrangianLeviSL (K := K) := by
  rw [lagrangianLeviSL, MonoidHom.mem_range]
  exact ⟨⟨SymplecticFour.unitri a, SymplecticFour.det_unitri a⟩,
    leviSp_eq_lam_of_coe_eq_unitri a _ rfl⟩

theorem leviSp_conj_tau_mem (A : Matrix.SpecialLinearGroup (Fin 2) K)
    {C : Matrix (Fin 2) (Fin 2) K} (hC : Cᵀ = C) :
    (leviSp (r := 2) (k := K) (Matrix.SpecialLinearGroup.toGL A)) * SymplecticFour.tau hC *
      (leviSp (r := 2) (k := K) (Matrix.SpecialLinearGroup.toGL A))⁻¹ ∈
        SymplecticFour.radical K := by
  refine ⟨(A : Matrix (Fin 2) (Fin 2) K) * C * (A : Matrix (Fin 2) (Fin 2) K)ᵀ, ?_, ?_⟩
  · rw [transpose_mul, transpose_mul, transpose_transpose, hC, Matrix.mul_assoc]
  · exact SymplecticSixCover.leviSp_mul_upperUnipotentSp_mul_inv
      (Matrix.SpecialLinearGroup.toGL A) hC

@[expose] noncomputable def lagrangianParabolicSL : Subgroup (StatedSp 2 K) where
  carrier := {x | ∃ q ∈ SymplecticFour.radical K, ∃ l ∈ lagrangianLeviSL (K := K), q * l = x}
  one_mem' := ⟨1, (SymplecticFour.radical K).one_mem, 1, lagrangianLeviSL.one_mem, one_mul 1⟩
  mul_mem' := by
    rintro x y ⟨q1, hq1, l1, hl1, rfl⟩ ⟨q2, hq2, l2, hl2, rfl⟩
    refine ⟨q1 * (l1 * q2 * l1⁻¹), (SymplecticFour.radical K).mul_mem hq1 ?_,
      l1 * l2, lagrangianLeviSL.mul_mem hl1 hl2, ?_⟩
    · obtain ⟨A, rfl⟩ := hl1
      obtain ⟨C, hC, rfl⟩ := hq2
      exact leviSp_conj_tau_mem A hC
    · group
  inv_mem' := by
    rintro x ⟨q, hq, l, ⟨A, rfl⟩, rfl⟩
    obtain ⟨C, hC, hqC⟩ := (SymplecticFour.radical K).inv_mem hq
    refine ⟨leviSp (r := 2) (k := K) (Matrix.SpecialLinearGroup.toGL A⁻¹) * q⁻¹ *
      (leviSp (r := 2) (k := K) (Matrix.SpecialLinearGroup.toGL A⁻¹))⁻¹, ?_,
      leviSp (r := 2) (k := K) (Matrix.SpecialLinearGroup.toGL A⁻¹), ⟨A⁻¹, rfl⟩, ?_⟩
    · rw [hqC]
      exact leviSp_conj_tau_mem A⁻¹ hC
    · simp only [MonoidHom.comp_apply, map_inv]
      group

theorem unipotent_le_lagrangianParabolicSL : unipotent 2 K ≤ lagrangianParabolicSL (K := K) := by
  intro u hu
  obtain ⟨C, hC, a, rfl⟩ := SymplecticFour.mem_unipotent_iff.1 hu
  exact ⟨SymplecticFour.tau hC, ⟨C, hC, rfl⟩, SymplecticFour.lam a,
    lam_mem_lagrangianLeviSL a, rfl⟩

theorem lagrangianParabolicSL_conj_mem_radical {x : StatedSp 2 K}
    (hx : x ∈ lagrangianParabolicSL (K := K)) {y : StatedSp 2 K}
    (hy : y ∈ SymplecticFour.radical K) : x * y * x⁻¹ ∈ SymplecticFour.radical K := by
  obtain ⟨q, hq, _, ⟨A, rfl⟩, rfl⟩ := hx
  obtain ⟨C, hC, rfl⟩ := hy
  have h := (SymplecticFour.radical K).mul_mem
    ((SymplecticFour.radical K).mul_mem hq (leviSp_conj_tau_mem A hC))
    ((SymplecticFour.radical K).inv_mem hq)
  simpa only [MonoidHom.comp_apply, _root_.mul_inv_rev, mul_assoc] using h

theorem lagrangianParabolicSL_le_normalizer_radical :
    lagrangianParabolicSL (K := K) ≤
      normalizer (SymplecticFour.radical K : Set (StatedSp 2 K)) := by
  intro x hx
  rw [mem_normalizer_iff]
  intro y
  constructor
  · exact lagrangianParabolicSL_conj_mem_radical hx
  · intro hy
    have h := lagrangianParabolicSL_conj_mem_radical (lagrangianParabolicSL.inv_mem hx) hy
    rwa [show x⁻¹ * (x * y * x⁻¹) * x⁻¹⁻¹ = y by group] at h

theorem tau_leviSp_mulVec_e1 (A : GL (Fin 2) K) {C : Matrix (Fin 2) (Fin 2) K} (hC : Cᵀ = C) :
    (((SymplecticFour.tau hC * leviSp (r := 2) (k := K) A : StatedSp 2 K) :
        GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
      Pi.single (Sum.inl 0) (1 : K) =
      Sum.elim ((A : Matrix (Fin 2) (Fin 2) K) *ᵥ Pi.single (0 : Fin 2) 1) 0 := by
  rw [Subgroup.coe_mul, Units.val_mul, SymplecticFour.coe_tau, coe_leviSp,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_mulVec]
  simp [Matrix.mulVec_zero, Matrix.zero_mulVec, Matrix.one_mulVec, Matrix.mulVec_add,
    Matrix.add_mulVec, Matrix.zero_mul, Matrix.mul_zero, Matrix.one_mul, add_zero, zero_add,
    Function.comp, Pi.single]

theorem exists_unitri_of_mulVec_e1 {A : Matrix.SpecialLinearGroup (Fin 2) K}
    (hA : (A : Matrix (Fin 2) (Fin 2) K) *ᵥ Pi.single (0 : Fin 2) 1 = Pi.single 0 1) :
    ∃ a : K, (A : Matrix (Fin 2) (Fin 2) K) = SymplecticFour.unitri a := by
  have h00 : (A : Matrix (Fin 2) (Fin 2) K) 0 0 = 1 := by
    have := congrFun hA 0
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  have h10 : (A : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by
    have := congrFun hA 1
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  have h11 : (A : Matrix (Fin 2) (Fin 2) K) 1 1 = 1 := by
    have hdet : (A : Matrix (Fin 2) (Fin 2) K).det = 1 := A.2
    rw [Matrix.det_fin_two] at hdet
    rw [h00, h10] at hdet
    simpa using hdet
  refine ⟨(A : Matrix (Fin 2) (Fin 2) K) 0 1, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [SymplecticFour.unitri, h00, h10, h11]

theorem mem_unipotent_of_mulVec_e1 {g : StatedSp 2 K} (hg : g ∈ lagrangianParabolicSL (K := K))
    (he1 : ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
      Pi.single (Sum.inl 0) (1 : K) = Pi.single (Sum.inl 0) 1) :
    g ∈ unipotent 2 K := by
  rcases hg with ⟨q, hq, l, hl, rfl⟩
  rcases hq with ⟨C, hC, rfl⟩
  rcases hl with ⟨A, rfl⟩
  change (((SymplecticFour.tau hC * leviSp (r := 2) (k := K)
    (Matrix.SpecialLinearGroup.toGL A) : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ Pi.single (Sum.inl 0) 1 =
    Pi.single (Sum.inl 0) 1 at he1
  rw [tau_leviSp_mulVec_e1 (Matrix.SpecialLinearGroup.toGL A) hC] at he1
  have hAe1 : (A : Matrix (Fin 2) (Fin 2) K) *ᵥ Pi.single (0 : Fin 2) 1 = Pi.single 0 1 := by
    funext i
    have h := congrFun he1 (Sum.inl i)
    simpa [Sum.elim_inl, Pi.single] using h
  obtain ⟨a, ha⟩ := exists_unitri_of_mulVec_e1 hAe1
  have hl' : leviSp (r := 2) (k := K) (Matrix.SpecialLinearGroup.toGL A) =
      SymplecticFour.lam a := leviSp_eq_lam_of_coe_eq_unitri a A ha
  exact SymplecticFour.mem_unipotent_iff.mpr ⟨C, hC, a, by
    simp only [MonoidHom.comp_apply]
    rw [hl']⟩

theorem torusHom_pair_eq_leviSp (β : Kˣ) :
    torusHom (r := 2) (k := K) (fun i : Fin 2 => if i = 0 then β else β⁻¹) =
      leviSp (r := 2) (k := K) (Matrix.SpecialLinearGroup.toGL (sl2Diag β)) := by
  show leviSp (r := 2) (k := K) (TauCeti.diagGL (fun i : Fin 2 => if i = 0 then β else β⁻¹)) =
    leviSp (r := 2) (k := K) (Matrix.SpecialLinearGroup.toGL (sl2Diag β))
  congr 1
  apply Units.ext
  rw [TauCeti.diagGL_coe, Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
    SymplecticTorusWeyl.coe_sl2Diag]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, Matrix.of_apply]

@[expose] noncomputable def lagrangianTorus (β : Kˣ) : StatedSp 2 K :=
  torusHom (r := 2) (k := K) (fun i : Fin 2 => if i = 0 then β else β⁻¹)

@[expose] noncomputable def lagrangianWeyl : StatedSp 2 K :=
  leviSp (r := 2) (k := K) (Matrix.SpecialLinearGroup.toGL (sl2W (k := K)))

theorem lagrangianTorus_mem (β : Kˣ) : lagrangianTorus β ∈ lagrangianParabolicSL (K := K) := by
  refine ⟨1, (SymplecticFour.radical K).one_mem, lagrangianTorus β, ?_, one_mul _⟩
  rw [lagrangianTorus, torusHom_pair_eq_leviSp]
  exact ⟨sl2Diag β, rfl⟩

theorem lagrangianWeyl_mem : lagrangianWeyl (K := K) ∈ lagrangianParabolicSL (K := K) :=
  ⟨1, (SymplecticFour.radical K).one_mem, lagrangianWeyl, ⟨sl2W, rfl⟩, one_mul _⟩

theorem lagrangianTorus_mem_normalizer_unipotent (β : Kˣ) :
    lagrangianTorus β ∈ normalizer (unipotent 2 K : Set (StatedSp 2 K)) :=
  torusHom_mem_normalizer_unipotent _

noncomputable def leviConjHom : SpecialLinearGroup (Fin 2) K →* StatedSp 2 K :=
  (MulAut.conj (lam (1 : Fin 2) (sl2W (k := K)))).toMonoidHom.comp
    ((leviSp (r := 2) (k := K)).comp (Matrix.SpecialLinearGroup.toGL (n := Fin 2) (R := K)))

theorem leviConjHom_apply (A : SpecialLinearGroup (Fin 2) K) :
    leviConjHom (K := K) A =
      lam (1 : Fin 2) (sl2W (k := K)) *
        leviSp (r := 2) (k := K) (Matrix.SpecialLinearGroup.toGL A) *
        (lam (1 : Fin 2) (sl2W (k := K)))⁻¹ := by
  rw [leviConjHom, MonoidHom.comp_apply, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply]

theorem leviConjHom_injective : Function.Injective (leviConjHom (K := K)) :=
  (MulAut.conj (lam (1 : Fin 2) (sl2W (k := K)))).injective.comp
    (BinarySymplecticSix.leviSp_injective.comp Matrix.SpecialLinearGroup.toGL_injective)

section CharTwo

variable [CharP K 2]

theorem sl2W_conj_torusHom (β : Kˣ) :
    (lam (1 : Fin 2) (sl2W (k := K))) *
        torusHom (r := 2) (k := K) (Pi.mulSingle (1 : Fin 2) β) *
        (lam (1 : Fin 2) (sl2W (k := K)))⁻¹ =
      (torusHom (r := 2) (k := K) (Pi.mulSingle (1 : Fin 2) β))⁻¹ := by
  simpa only [map_mul, map_inv, lam_sl2Diag] using
    congrArg (lam (1 : Fin 2)) (CFSG.LinearAlgebra.sl2W_mul_sl2Diag_mul_sl2W_inv (K := K) β)

theorem orderOf_lagrangianTorus (β : Kˣ) : orderOf (lagrangianTorus β) = orderOf β := by
  rw [lagrangianTorus, torusHom_pair_eq_leviSp]
  exact (orderOf_injective ((leviSp (r := 2) (k := K)).comp SpecialLinearGroup.toGL)
    (BinarySymplecticSix.leviSp_injective.comp SpecialLinearGroup.toGL_injective) (sl2Diag β)).trans
    (CFSG.LinearAlgebra.orderOf_sl2Diag β)

theorem lagrangianWeyl_conj_lagrangianTorus (β : Kˣ) :
    lagrangianWeyl * lagrangianTorus β * (lagrangianWeyl (K := K))⁻¹ = (lagrangianTorus β)⁻¹ := by
  rw [lagrangianTorus, torusHom_pair_eq_leviSp, lagrangianWeyl]
  simpa only [map_mul, map_inv] using
    congrArg (fun A => leviSp (r := 2) (k := K) (SpecialLinearGroup.toGL A))
      (CFSG.LinearAlgebra.sl2W_mul_sl2Diag_mul_sl2W_inv (K := K) β)

theorem lam_sl2W_conj_lagrangianTorus (β : Kˣ) :
    lam (1 : Fin 2) (sl2W (k := K)) * lagrangianTorus β * (lam (1 : Fin 2) (sl2W (k := K)))⁻¹ =
      torusHom (r := 2) (k := K) (fun _ : Fin 2 => β) := by
  have hsplit : lagrangianTorus β = torusHom (r := 2) (k := K) (Pi.mulSingle 0 β) *
      torusHom (Pi.mulSingle 1 β⁻¹) := by
    rw [lagrangianTorus, ← map_mul]
    congr 1
    funext i
    fin_cases i <;> simp
  have hc := (commute_lam_torusHom_mulSingle (i := 1) (j := 0) (by decide) (sl2W (k := K)) β).eq
  calc _ = torusHom (r := 2) (k := K) (Pi.mulSingle 0 β) * (lam (1 : Fin 2) (sl2W (k := K)) *
        torusHom (Pi.mulSingle 1 β⁻¹) * (lam (1 : Fin 2) (sl2W (k := K)))⁻¹) := by
        rw [hsplit, ← mul_assoc, hc]
        group
    _ = torusHom (fun _ : Fin 2 => β) := by
        rw [sl2W_conj_torusHom, ← map_inv, ← map_mul]
        congr 1
        funext i
        fin_cases i <;> simp

theorem leviConjHom_commute_lagrangianTorus (β : Kˣ) (A : SpecialLinearGroup (Fin 2) K) :
    Commute (leviConjHom (K := K) A) (lagrangianTorus β) := by
  have h2 : lam (1 : Fin 2) (sl2W (k := K)) * lam 1 sl2W = 1 := by
    rw [← map_mul, CFSG.LinearAlgebra.sl2W_mul_self, map_one]
  have hb : lagrangianTorus β =
      MulAut.conj (lam (1 : Fin 2) (sl2W (k := K))) (torusHom (fun _ : Fin 2 => β)) := by
    rw [MulAut.conj_apply, ← lam_sl2W_conj_lagrangianTorus, inv_eq_of_mul_eq_one_right h2]
    calc lagrangianTorus β = (lam (1 : Fin 2) (sl2W (k := K)) * lam 1 sl2W) * lagrangianTorus β *
          (lam (1 : Fin 2) (sl2W (k := K)) * lam 1 sl2W) := by rw [h2, one_mul, mul_one]
      _ = _ := by group
  have hL : Commute (leviSp (r := 2) (k := K) (SpecialLinearGroup.toGL A))
      (torusHom (r := 2) (k := K) (fun _ : Fin 2 => β)) := by
    have hdiag : Commute (SpecialLinearGroup.toGL A) (TauCeti.diagGL (fun _ : Fin 2 => β)) := by
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, SpecialLinearGroup.coe_GL_coe_matrix, TauCeti.diagGL_coe]
      ext i j
      simp [Matrix.mul_diagonal, Matrix.diagonal_mul, mul_comm]
    exact hdiag.map (leviSp (r := 2) (k := K))
  rw [leviConjHom_apply, hb]
  exact hL.map (MulAut.conj (lam (1 : Fin 2) (sl2W (k := K)))).toMonoidHom

theorem radical_relIndex_unipotent [Finite K] :
    (SymplecticFour.radical K).relIndex (unipotent 2 K) = Nat.card K := by
  have hmul := relIndex_mul_card (H := SymplecticFour.radical K) (K := unipotent 2 K)
  rw [inf_eq_left.mpr SymplecticFour.radical_le_unipotent, SymplecticFour.card_radical,
    show Nat.card (unipotent 2 K) = Nat.card K ^ 4 from card_unipotent 2] at hmul
  refine Nat.eq_of_mul_eq_mul_right (pow_pos (Finite.card_pos (α := K)) 3) ?_
  rw [hmul]
  ring

end CharTwo

end CFSG.ClassicalGroups.Symplectic.Sp4
